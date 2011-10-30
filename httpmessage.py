# Copyright (c) 2009-2011 Matt Anderson.
#  
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to
# deal in the Software without restriction, including without limitation the
# rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
# sell copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#  
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#  
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
# IN THE SOFTWARE.
"""A library for working with http messages and rfc822-style messages.
"""
import sys
if sys.version_info < (2, 6):
    raise ImportError('Python version 2.6 is required for httpmessage.')

import time
import collections
__author__ = "Matt Anderson (manders2k.dev (at) gmail.com)"
__copyright__ = "Copyright 2009-{0}, Matt Anderson".format(
    time.localtime().tm_year)
__contributors__ = []
__license__ = "MIT"
v = __version_info__ = collections.namedtuple(
    "VersionInfo", "major minor prerel prerelver")(0, 5, "a", 1)
__version__ = "{0}.{1}{2}{3}".format(
    v.major, v.minor,
    v.prerel if v.prerel else "",
    v.prerelver if v.prerel else "")
del v
import os
import urlparse
import operator
import re
import cStringIO as stringio
import itertools
import socket
import select
import pprint
import contextlib


#======================================================================
# constants
#======================================================================
_filelike_methods = frozenset(
    """close closed flush isatty read readline readlines reset seek softspace
    tell truncate write writelines""".split())

_missing = object()

CRLF = '\r\n'

DATASIZE_EOF = -1
DATASIZE_CHUNKED = -2
DATASIZE_BYTERANGE = -3

#======================================================================
# functions
#======================================================================
@contextlib.contextmanager
def _restore_position(io):
    """A helper context manager for working with a filelike object.

    The position in the file on entering the context is restored on exit of the
    context, so the suite managed by the context is free to move the position as
    part of its operation.

    >>> import StringIO
    >>> io = StringIO.StringIO()
    >>> io.write('0123456789')
    >>> io.tell()
    10
    >>> with _restore_position(io) as orig_pos:
    ...     print orig_pos
    ...     io.seek(2)
    ...     print io.tell()
    10
    2
    >>> io.tell()
    10
    """
    origpos = io.tell()
    try:
        yield origpos
    finally:
        io.seek(origpos)

def read_headers(fobj):
    r"""Tries to read RFC822-style headers from a filelike object.

    Returns a :class:`MultiDict`. The filelike object used as input must support
    the :meth:`seek` method.

    If :func:`read_headers` encounters anything unexpected while attempting to
    read headers, it assumes that what it is reading is actually not a block of
    headers. It it seeks to the input object's position to where it was when
    :func:`read_headers` was called, and returns an empty :class:`MultiDict`.

    >>> import StringIO
    >>> import pprint
    >>> io = StringIO.StringIO('''Foo: foo
    ... Bar: bar
    ... Foo: baaz
    ... 
    ... flup
    ... ''')
    >>> headers = read_headers(io)
    >>> headers
    MultiDict([
      (Ident(key='Foo', index=0), 'foo'),
      (Ident(key='Bar', index=0), 'bar'),
      (Ident(key='Foo', index=1), 'baaz')
    ])
    >>> pprint.pprint(headers.items())
    [(Ident(key='Foo', index=0), 'foo'),
     (Ident(key='Bar', index=0), 'bar'),
     (Ident(key='Foo', index=1), 'baaz')]
    >>> type(headers).__name__
    'MultiDict'
    >>> io.tell()
    29
    >>> io.read()
    'flup\n'
    """
    headers = MultiDict()
    origpos = fobj.tell()
    abort = True
    key = None
    while True:
        line = fobj.readline().rstrip()
        if not line:
            abort = False
            break
        elif line[0].isspace():
            if not key: break
            headers[key] += ' {0}'.format(line.strip())
        else:
            try:
                key, value = [
                    s.strip() for s in line.split(':', 1)]
            except ValueError: 
                break
            headers.additem(key, value)
    if abort:
        fobj.seek(origpos)
        headers.clear()
    return headers

def read_data_chunked(fobj):
    """Read http chunked-style data from the file-like object.

    Read **all** chunks from the file-like, and return the data as a string,
    with the chunking data wrappers removed.
    """
    # FIXME: Should we always read all chunks? Or should we only read "enough"
    # (where enough is some parameter)?
    #
    # we're expecting a chunk to consist of the following:
    # 1. the size of the chunk in hex, followed by '\r\n'
    # 2. the chunk data, of exactly the size specified in (1)
    # 3. and end-chunk separator, consisting exactly of '\r\n'
    #
    # The last chunk there is to read will be the zero chunk (ie, the
    # size will be zero, with no chunk data).
    chunks = []
    finished = False
    while not finished:
        try:
            size = int(fobj.readline().strip(), 16)
        except ValueError:
            raise ValueError('Error while reading chunk size')
        if size == 0:
            finished = True
        chunks.append(fobj.read(size))
        assert len(chunks[-1]) == size
        sep = fobj.readline()
        if sep != CRLF:
            raise ValueError(
                'Found {0!r}; expecting end separator "\\r\\n"'.format(sep))
    return ''.join(chunks)

def read_data_byterange(fobj):
    # How often would we need this?  I've never encountered it.
    raise NotImplementedError()

def read_data(fobj, datasize):
    """Read message data from the file-like object.

    Switches on the ``datasize`` parameter. If ``datasize`` is the constant
    DATASIZE_CHUNKED or DATASIZE_BYTERANGE, it delegates to the relevant
    function.
    """
    if datasize == DATASIZE_EOF:
        return fobj.read()
    elif datasize == DATASIZE_CHUNKED:
        return read_data_chunked(fobj)
    elif datasize == DATASIZE_BYTERANGE:
        return read_data_byterange(fobj)
    else:
        datasize = int(datasize)
        if datasize < 0:
            raise ValueError('illegal data size {0!r}'.format(datasize))
        return fobj.read(datasize)


#======================================================================
# Exceptions
#======================================================================
class HttpMessageException(Exception): pass
class RequestUriNotSet(HttpMessageException): pass


#======================================================================
# Helper Class: SocketReadfile
#======================================================================
class SocketReadfile(object):
    """A fully buffered file-like object which provides read access to a socket.

    This wraps a socket and provides read access to it as if it were a file.
    It buffers the socket's data lazily as you try to :func:`read` the data,
    but buffers it so that you can :func:`seek` backwards if you wish to, call
    :func:`tell` on it to know your current position, etc.

    A :class:`SocketReadfile` can be constructed with a ``buffer_callback``
    parameter, which should be a callable which takes 1 argument (a chunk of
    data read). Immediately after the :class:`SocketReadfile` has buffered
    some new data, this callback is called with the data read, it is possible
    to work with this data in parallel to it being read by the
    :class:`SocketReadfile`.  This may be useful if implementing a proxy, for
    example, and you wish to send data along to a client as soon as it comes
    in.
    """
    recv_size = 1024
    timeout = None

    def _buffer_callback(self, bytes):
        pass

    def __init__(self, sock, buffer_callback=None):
        self._sock = sock
        self._io = stringio.StringIO()
        self._buffer_size = 0
        self._fully_buffered = False
        if buffer_callback is not None:
            self._buffer_callback = buffer_callback

    def _become_pure_proxy(self):
        self._fully_buffered = True
        io = self._io
        for attrname in _filelike_methods:
            setattr(self, attrname, getattr(io, attrname))

    def _socket_ready(self, timeout):
        r_ok = False
        try:
            r_ok, _, _ = select.select([self._sock], [], [], timeout)
        except socket.error:
            self._become_pure_proxy()
        return bool(r_ok)

    def socket_peek(self, bufsize, timeout=_missing):
        if self._fully_buffered: return ''
        if timeout is _missing:
            timeout = self.timeout
        if not self._socket_ready(timeout):
            return ''
        return self._sock.recv(bufsize, socket.MSG_PEEK)

    def _buffer_to(self, pos, timeout=_missing):
        if self._fully_buffered: return
        io = self._io
        if timeout is _missing:
            timeout = self.timeout
        with _restore_position(io):
            io.seek(0, os.SEEK_END)
            while self._buffer_size < pos:
                if not self._socket_ready(timeout):
                    break
                size = min(self.recv_size, pos-self._buffer_size)
                data = self._sock.recv(size)
                if not data:
                    self._become_pure_proxy()
                    break
                io.write(data)
                self._buffer_size += len(data)
                self._buffer_callback(data)

    def _buffer_all(self, timeout=_missing):
        self._buffer_to(1e400, timeout)

    def seek(self, offset, whence=os.SEEK_SET):
        if whence == os.SEEK_END:
            self._buffer_all()
        else:
            pos = offset
            if whence == os.SEEK_CUR:
                pos = self.tell() + offset
            self._buffer_to(pos)
        self._io.seek(offset, whence)

    def close(self):
        self._become_pure_proxy()
        self._io.close()

    def read(self, count=_missing):
        args = []
        if count is _missing:
            self._buffer_all()
        else:
            args = [count]
            pos = self.tell() + count
            self._buffer_to(pos)
        return self._io.read(*args)

    def readline(self):
        io = self._io
        with _restore_position(io) as origpos:
            # FIXME: Why reset first? Don't think that it's helpful, and could
            # be quite inefficient
            io.reset()
            text = io.read()
        if text.find('\n', origpos) == -1:
            while not self._fully_buffered:
                incoming = self.socket_peek(self.recv_size)
                nl_pos = incoming.find('\n')
                if nl_pos == -1:
                    self._buffer_to(self._buffer_size+self.recv_size)
                else:
                    self._buffer_to(self._buffer_size+nl_pos+1)
                    break
        return io.readline()

    def readlines(self):
        self._buffer_all()
        return self._io.readlines()

    def truncate(self):
        self._become_pure_proxy()
        self._io.truncate()

    def write(self, text):
        if len(text) + self.tell() > self._buffer_size:
            self._become_pure_proxy()
        self._io.write(text)
        
    def writelines(self, lines):
        for line in lines:
            self.write(line)

    def __len__(self):
        io = self._io
        with _restore_position(io):
            io.seek(0, os.SEEK_END)
            return io.tell()

    def __getattr__(self, attrname):
        if attrname in _filelike_methods:
            return getattr(self._io, attrname)
        raise AttributeError(attrname)


#======================================================================
# Helper Class: Url
#======================================================================
class Url(object):
    """A parsed url, similar to :class:`urlparse.ParseResult`.
    
    Url objects can be edited, and transformed back into textual representations
    by calling str() on the url object.
    """
    @property
    def username(self):
        # taken from urlparse.ResultMixin Python 2.7.1
        netloc = self.netloc
        if "@" in netloc:
            userinfo = netloc.rsplit("@", 1)[0]
            if ":" in userinfo:
                userinfo = userinfo.split(":", 1)[0]
            return userinfo
        return None

    @property
    def password(self):
        # taken from urlparse.ResultMixin Python 2.7.1
        netloc = self.netloc
        if "@" in netloc:
            userinfo = netloc.rsplit("@", 1)[0]
            if ":" in userinfo:
                return userinfo.split(":", 1)[1]
        return None

    @property
    def hostname(self):
        # taken from urlparse.ResultMixin Python 2.7.1
        netloc = self.netloc.split('@')[-1]
        if '[' in netloc and ']' in netloc:
            return netloc.split(']')[0][1:].lower()
        elif ':' in netloc:
            return netloc.split(':')[0].lower()
        elif netloc == '':
            return None
        else:
            return netloc.lower()

    @property
    def port(self):
        # taken from urlparse.ResultMixin Python 2.7.1
        netloc = self.netloc.split('@')[-1].split(']')[-1]
        if ':' in netloc:
            port = netloc.split(':')[1]
            return int(port, 10)
        else:
            return None

    @property
    def query_string(self):
        return '&'.join(
            '{key}={value}'.format(key=k, value=v)
            for ((k, i), v) in self.query.iteritems())

    def __init__(self, text):
        parsed = urlparse.urlparse(text)
        self.scheme = parsed.scheme
        self.netloc = parsed.netloc
        self.path = parsed.path
        self.params = parsed.params
        self.query = MultiDict(urlparse.parse_qsl(parsed.query))
        self.fragment = parsed.fragment

    def __str__(self):
        return urlparse.urlunparse((self.scheme, self.netloc, self.path, 
            self.params, self.query_string, self.fragment))

    def __repr__(self):
        return '{0}({1!r})'.format(type(self).__name__, str(self))


#======================================================================
# Class: MultiDict
#======================================================================
class _KeyValue(object):
    # a helper class for the MultiDict
    key = property(lambda self:self._key)
    def __init__(self, key, value):
        self._key, self.value = key, value
    def __repr__(self):
        return "{0}({1!r}, {2!r})".format(
            type(self).__name__, self.key, self.value)
    def __iter__(self):
        yield self.key; yield self.value


class Ident(collections.namedtuple("Ident", "key index")):
    # a helper for working with/displaying key-index pairs; multidict "idents"
    __slots__ = ()


class MultiDict(collections.MutableMapping):
    """An insert-time-ordered dictionary supporting multiple values per key.

    Keys to the dictionary should be in the form of a (key, index) pair. For
    example:

    >>> md = MultiDict([("foo", "bar")])
    >>> md["foo", 0]
    "bar"

    If :attr:`strict_indexing` is ``False`` (the default), keys are permitted
    to be specified without an index, and if this is done, the "last" index of
    a key is always assumed.

    """

    strict_indexing = False

    def __init__(self, __iterable=(), **kwargs):
        # We have three core datastructures, set up or re-initialized by
        # self.clear().  self._kv is a list of :class:`_KeyValue` objects,
        # self._map is a defaultdict of lists (used to store ind)
        self._kv = None
        self._map = None
        self._count = None
        self.clear()
        self.update(__iterable, **kwargs)

    def __getitem__(self, ident):
        key, index = self._split_ident(ident)
        try:
            kvi = self._map[key][index]
            return self._kv[kvi].value
        except KeyError:
            raise KeyError(ident)
        except IndexError:
            raise KeyError(
                'Index {0} out of range (length {1}) for key {2!r}'.format(
                    index, self.len(key), key))

    def __setitem__(self, ident, value):
        key, index = self._split_ident(ident)
        value = self.value_encode(key, value)
        keylength = self._len(key)
        if index > keylength:
            raise KeyError(
                'Index {0} out of range in {1!r}'.format(index, ident))
        if index < keylength:
            kvi = self._map[key][index]
            self._kv[kvi].value = value
        else:
            kvi = len(self._kv)
            self._kv.append(_KeyValue(key, value))
            self._map[key].append(kvi)
            self._count += 1

    def __delitem__(self, ident):
        if ident not in self:
            raise KeyError(ident)
        key, index = self._split_ident(ident)
        kvi_seq = self._map[key]
        kvi = kvi_seq.pop(index)
        if not kvi_seq: del self._map[key]
        self._kv[kvi] = None
        self._count -= 1
        if len(self._kv) > 2 * self._count:
            # over half our self._kv entries are None
            self._rebuild()

    def _len(self, key=_missing):
        if key is _missing:
            return self._count
        key = self.key_encode(key)
        if key in self._map:
            return len(self._map[key])
        else:
            return 0

    def __len__(self):
        return self._len()
    
    def _iter(self, key=_missing):
        indicies = collections.defaultdict(int)
        kv_seq = ()
        if key is _missing:
            kv_seq = (kv for kv in self._kv if kv is not None)
        else:
            key = self.key_encode(key)
            if key in self._map:
                kv_seq = (Ident(*self._kv[kvi]) for kvi in self._map[key])
        for kv in kv_seq:
            key = kv.key
            yield Ident(key, indicies[key])
            indicies[key] += 1

    def __iter__(self):
        return self._iter()

    def clear(self):
        self._kv = []
        self._map = collections.defaultdict(list)
        self._count = 0

    def key_encode(self, key):
        return key

    def value_encode(self, key, value):
        return value

    def _is_ident(self, ident):
        i = ident
        return isinstance(i, tuple) and len(i) == 2 and isinstance(i[1], int)

    def _split_ident(self, ident):
        # An "ident" is a (key, index) pair. Break it apart and assure that 
        # the index is an integer. Call self.key_encode() to do an (optional)
        # arbitrary transform on the key.
        if self._is_ident(ident):
            key, index = ident
        elif self.strict_indexing:
            raise KeyError("{0} is not a valid (key, index) pair".format(ident))
        else:
            key = ident
            index = 0 if not self._len(key) else -1
        key = self.key_encode(key)
        return key, index

    def _rebuild(self):
        # Each delete, we stick None in place of a kv in self._kv instead of 
        # immediately removing the item from the list. Rebuilding clears those
        # out and compacts our storage.
        items = self.items()
        self.clear()
        self.update(items)

    def _repritems(self, pad=2):
        tmpl = " "*pad + "{0!r}"
        return ",\n".join(tmpl.format(item) for item in self.items())

    def __repr__(self):
        return "{0}([\n{1}\n])".format(type(self).__name__, self._repritems())

    def update(self, __iterable=(), **kwargs):
        if isinstance(__iterable, collections.Mapping):
            argiter = __iterable.iteritems()
        else:
            argiter = __iterable
        for key, value in itertools.chain(argiter, kwargs.iteritems()):
            if self._is_ident(key):
                self[key] = value
            else:
                self.additem(key, value)

    def getitem(self, key, index=-1):
        return self[key, index]

    def setitem(self, key, value, index=-1):
        if index == -1 and not self.len(key):
            index = 0
        self[key, index] = value

    def additem(self, key, value):
        self[key, self._len(key)] = value

    def delitem(self, key, index=-1):
        del self[key, index]

    def iterkeys(self, key=_missing):
        return self._iter(key)
    
    def keys(self, key=_missing):
        return list(self.iterkeys(key))

    def iteritems(self, key=_missing):
        for ident in self._iter(key):
            yield ident, self[ident]

    def items(self, key=_missing):
        return list(self.iteritems(key))

    def itervalues(self, key=_missing):
        for ident in self._iter(key):
            yield self[ident]

    # Shadowing a builtin; generally bad.  Best put it at the end.
    def len(self, key=_missing):
        return self._len(key)


#======================================================================
# Class: Message
#======================================================================
class Message(MultiDict):
    """Represents an RFC822-style message.
    """

    def key_encode(self, key):
        return str(key).title()

    @classmethod
    def from_text(cls, text):
        """Construct a :class:`Message` from input text.
        
        An alternate constructor.

        """
        return cls.from_filelike(stringio.StringIO(text))

    @classmethod
    def from_filelike(cls, fileobj):
        """Construct a :class:`Message` from a file-like object.
        
        An alternate constructor.
        
        """
        msg = cls()
        msg.update(read_headers(fileobj))
        msg.data = read_data(fileobj, msg.calculate_expected_datasize())
        return msg

    def __init__(self, headers=(), data=''):
        self._data = stringio.StringIO()
        self.write(data)
        self.reset()
        super(Message, self).__init__(headers)

    def __getattr__(self, attrname):
        if attrname in _filelike_methods:
            return getattr(self._data, attrname)
        raise AttributeError(attrname)

    def __dir__(self):
        attrs = set(_filelike_methods)
        attrs.update(self.__dict__)
        for cls in type(self).mro():
            attrs.update(cls.__dict__)
        return sorted(attrs)

    data = property(doc='textual data of the message')

    @data.getter
    def data(self):
        with _restore_position(self):
            self.reset()
            return self.read()

    @data.setter
    def data(self, value):
        self.reset()
        self.truncate()
        self.write(value)
        self.reset()

    def __repr__(self):
        return "{0}([\n{1}\n], data={2}".format(
            type(self).__name__, self._repritems(), self.data)

    def __str__(self):
        head = CRLF.join(
            "{key}: {value}".format(key=k, value=v)
            for ((k, i), v) in self.iteritems())
        return "{head}{sep}{body}".format(
            head=head, sep=CRLF+CRLF, body=self.data)

    def __iter__(self):
        raise TypeError(
            'Cannot iterate over a {0}; use iterkeys() or '
            'iterlines() instead.'.format(type(self).__name__))

    def iterlines(self):
        return iter(self._data)

    def calculate_expected_datasize(self):
        return DATASIZE_EOF


#======================================================================
# Class: HttpMessage
#======================================================================
class HttpMessage(Message):
    """A HTTP Message.
    """
    http_version = 'HTTP/1.1'
    scheme = 'http'
    _kwattrs = ()

    def _firstline_getter(self):
        raise NotImplementedError()

    @property
    def firstline(self):
        items = [str(field) for field in self._firstline_getter(self)]
        return '{0} {1} {2}'.format(*items)

    @classmethod
    def from_socket(cls, sock):
        return cls.from_filelike(SocketReadfile(sock))

    @classmethod
    def from_filelike(cls, fobj, request_method='GET'):
        firstline = fobj.readline()
        if firstline.lower().startswith('http/'):
            if not issubclass(cls, ResponseMessage):
                cls = ResponseMessage
        else:
            if not issubclass(cls, RequestMessage):
                cls = RequestMessage
        msg = cls()
        msg.firstline_update(firstline)
        msg.update(read_headers(fobj))
        if hasattr(msg, 'request_method'):
            msg.request_method = request_method
        msg.data = read_data(fobj, msg.calculate_expected_datasize())
        return msg

    def __init__(self, *args, **kwargs):
        if type(self) == HttpMessage:
            self.__class__ = RequestMessage
        for attrname in self._kwattrs:
            self._kwargs_set(attrname, kwargs)
        super(HttpMessage, self).__init__(*args, **kwargs)

    def __str__(self):
        return "{firstline}{CRLF}{message}".format(
            firstline=self.firstline,
            CRLF=CRLF,
            message=super(HttpMessage, self).__str__())

    def __repr__(self):
        args = []
        for attrname in self._kwattrs:
            attrval = self.__dict__.get(attrname, _missing)
            if attrval is not _missing:
                args.append('  {0}={1!r}'.format(attrname, attrval))
        if len(self):
            args.append('  headers=[\n{0}\n  ]'.format(self._repritems(4)))
        else:
            args.append('  headers=[]')
        args.append('  data={0!r}'.format(self.data))
        return "{0}(\n{1}\n)".format(type(self).__name__, ",\n".join(args))

    def _kwargs_set(self, attrname, kwargs):
        attrval = kwargs.pop(attrname, _missing)
        if attrval is not _missing:
            setattr(self, attrname, attrval)

    def calculate_expected_datasize(self):
        size = DATASIZE_EOF
        if self.get('transfer-encoding', 'identity') != 'identity':
            size = DATASIZE_CHUNKED
        elif self.get('content-length', None) is not None:
            size = int(self['content-length'])
        elif self.get('content-type', '').lower() == 'multipart/byteranges':
            size = DATASIZE_BYTERANGE
        return size


#======================================================================
# Class: RequestMessage
#======================================================================
class RequestMessage(HttpMessage):
    """An HTTP Request message.
    """
    method = 'GET'
    request_uri = '/'
    _kwattrs = 'method request_uri http_version'.split()
    _firstline_getter = operator.attrgetter(*_kwattrs)
    _no_data_methods = frozenset('GET HEAD'.split())

    @property
    def url(self):
        # is this getting available information from the right places?
        request_url = Url(self.request_uri)
        netloc = hostname = self.get('hostname', request_url.hostname) or ''
        if request_url.port:
            netloc = '{0}:{1}'.format(hostname, request_url.port)
        return Url(urlparse.urlunparse((self.scheme, netloc, request_url.path,
            request_url.params, request_url.query_string, request_url.fragment)))

    def calculate_expected_datasize(self):
        if self.method.upper() in self._no_data_methods:
            return 0
        return super(RequestMessage, self).calculate_expected_datasize()

    def firstline_update(self, line):
        line_parts = line.strip().split()
        if len(line_parts) == 2:
            line_parts.append('HTTP/0.9')
        try:
            self.method, self.request_uri, self.http_version = line_parts
        except ValueError:
            raise ValueError('Malformed firstline {0!r}'.format(line))

    def fetch_response(self, sock=None):
        """Take the request message and (attempt to) get a response.

        If no socket is provided, this will open a new network socket to the
        remote host. The :class:`RequestMessage` will send itself as the
        request over the socket, and make an :class:`ResponseMessage` from
        what comes back from the remote host.

        The request must include a ``request_uri`` attribute.
        """
        if not self.request_uri:
            raise RequestUriNotSet("cannot fetch_response() {0!r}".format(self))
        url = Url(self.request_uri)
        if url.hostname and 'host' not in self:
            self['host'] = url.hostname
        if not self.get('host'):
            raise ValueError('Host header field not set; cannot fetch.')
        if not sock:
            port = url.port if url.port else 80
            sock = socket.socket()
            sock.connect((self['host'], port))
        sock.sendall(str(self))
        fobj = SocketReadfile(sock)
        resp = ResponseMessage.from_filelike(fobj, self.method)
        return resp

    def as_wsgi_environ(self, **kw):
        """Turn the request message into a WSGI environment.
        """
        # this could use some work / verification
        url = Url(self.request_uri)
        environ = {
            'REQUEST_METHOD': self.method,
            'SCRIPT_NAME': '',
            'PATH_INFO': url.path,
            'QUERY_STRING': url.query_string,
            'SERVER_PROTOCOL': self.http_version,
            'SERVER_NAME': self.get('host', ''),
            'SERVER_PORT': url.port,
            'CONTENT_TYPE': self.get('content-type', ''),
            'CONTENT_LENGTH': self.get('content-length', ''),}
        for key in self.iterkeys():
            envkey = 'HTTP_{0}'.format(key.replace('-','_').upper())
            environ[envkey] = self[key]
        environ['wsgi.input'] = stringio.StringIO(self.data)
        environ.update(kw)
        return environ


#======================================================================
# Class: ResponseMessage
#======================================================================
class ResponseMessage(HttpMessage):
    """An HTTP Response message.
    """
    request_method = 'GET'
    status_code = 200
    reason_phrase = ''
    _kwattrs = 'http_version status_code reason_phrase request_method'.split()
    _firstline_getter = operator.attrgetter(*_kwattrs[:3])

    def calculate_expected_datasize(self):
        code = self.status_code
        if 100 <= code < 200 or code == 204 or code == 304:
            return 0
        if self.request_method.upper() == 'HEAD':
            return 0
        return super(ResponseMessage, self).calculate_expected_datasize()

    def firstline_update(self, line):
        line_parts = re.split(r'\s+', line.strip(), 3)
        if len(line_parts) < 2:
            raise ValueError('Malformed firstline {0!r}'.format(line))
        self.http_version = line_parts[0]
        self.status_code = int(line_parts[1])
        self.reason_phrase = ' '.join(line_parts[2:])
    

