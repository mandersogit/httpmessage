######################################################################
``httpmessage``: a library for http messaging
######################################################################

The :mod:`httpmessage` package is not a HTTP *server* library or a HTTP
*client* library. It tries instead to be a HTTP *peer* library, allowing
programs to more easily speak HTTP to one another. The design of
:mod:`httpmessage` had writing a proxy server in mind, so it tries to preserve
the integrity of HTTP messages so they can be modified and retransmitted if
desired. Hopefully, the library is well suited to writing both clients and
servers, but it does not assume that the program using it is a client or a
server.

