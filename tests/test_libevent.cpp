/*
 * File: test_libevent.cpp
 * Project: future stream
 * Created Date: Friday August 16th 2019
 * Author: DaGai  <binghan2836@163.com>
 * -----
 * Last Modified: Sunday August 18th 2019 10:15:30 pm
 * Modified By:   the developer formerly known as DaGai
 * -----
 * MIT License
 * 
 * Copyright (c) 2019 binghan2836@163.com
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 * 
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 * -----
 * HISTORY:
 * Date          By    Comments
 * ----------    ---    ----------------------------------------------------------
 */

#include <thread>
#include <iostream>
#include <string>
#include <algorithm>

#include <openssl/ssl.h>
#include <openssl/err.h>
#include <openssl/rand.h>

#include <openssl/x509v3.h>

#include "gmock/gmock.h"
#include "gtest/gtest.h"

#include "config.h"

#include <event2/bufferevent_ssl.h>
#include <event2/bufferevent.h>
#include <event2/buffer.h>
#include <event2/listener.h>
#include <event2/util.h>
#include <event2/http.h>

/*
 * Helper functions to perform basic hostname validation using OpenSSL.
 *
 * Please read "everything-you-wanted-to-know-about-openssl.pdf" before
 * attempting to use this code. This whitepaper describes how the code works,
 * how it should be used, and what its limitations are.
 *
 * Author:  Alban Diquet
 * License: See LICENSE
 *
 */

typedef enum
{
    MatchFound,
    MatchNotFound,
    NoSANPresent,
    MalformedCertificate,
    Error
} HostnameValidationResult;

#define CURL_HOST_NOMATCH 0
#define CURL_HOST_MATCH 1

/* Portable, consistent toupper (remember EBCDIC). Do not use toupper() because
   its behavior is altered by the current locale. */
static char Curl_raw_toupper(char in)
{
    switch (in)
    {
    case 'a':
        return 'A';
    case 'b':
        return 'B';
    case 'c':
        return 'C';
    case 'd':
        return 'D';
    case 'e':
        return 'E';
    case 'f':
        return 'F';
    case 'g':
        return 'G';
    case 'h':
        return 'H';
    case 'i':
        return 'I';
    case 'j':
        return 'J';
    case 'k':
        return 'K';
    case 'l':
        return 'L';
    case 'm':
        return 'M';
    case 'n':
        return 'N';
    case 'o':
        return 'O';
    case 'p':
        return 'P';
    case 'q':
        return 'Q';
    case 'r':
        return 'R';
    case 's':
        return 'S';
    case 't':
        return 'T';
    case 'u':
        return 'U';
    case 'v':
        return 'V';
    case 'w':
        return 'W';
    case 'x':
        return 'X';
    case 'y':
        return 'Y';
    case 'z':
        return 'Z';
    }
    return in;
}

/*
 * Curl_raw_equal() is for doing "raw" case insensitive strings. This is meant
 * to be locale independent and only compare strings we know are safe for
 * this.  See http://daniel.haxx.se/blog/2008/10/15/strcasecmp-in-turkish/ for
 * some further explanation to why this function is necessary.
 *
 * The function is capable of comparing a-z case insensitively even for
 * non-ascii.
 */

static int Curl_raw_equal(const char *first, const char *second)
{
    while (*first && *second)
    {
        if (Curl_raw_toupper(*first) != Curl_raw_toupper(*second))
            /* get out of the loop as soon as they don't match */
            break;
        first++;
        second++;
    }
    /* we do the comparison here (possibly again), just to make sure that if the
     loop above is skipped because one of the strings reached zero, we must not
     return this as a successful match */
    return (Curl_raw_toupper(*first) == Curl_raw_toupper(*second));
}

static int Curl_raw_nequal(const char *first, const char *second, size_t max)
{
    while (*first && *second && max)
    {
        if (Curl_raw_toupper(*first) != Curl_raw_toupper(*second))
        {
            break;
        }
        max--;
        first++;
        second++;
    }
    if (0 == max)
        return 1; /* they are equal this far */

    return Curl_raw_toupper(*first) == Curl_raw_toupper(*second);
}

/*
 * Match a hostname against a wildcard pattern.
 * E.g.
 *  "foo.host.com" matches "*.host.com".
 *
 * We use the matching rule described in RFC6125, section 6.4.3.
 * http://tools.ietf.org/html/rfc6125#section-6.4.3
 */

static int hostmatch(const char *hostname, const char *pattern)
{
    const char *pattern_label_end, *pattern_wildcard, *hostname_label_end;
    int wildcard_enabled;
    size_t prefixlen, suffixlen;
    pattern_wildcard = strchr(pattern, '*');
    if (pattern_wildcard == NULL)
        return Curl_raw_equal(pattern, hostname) ? CURL_HOST_MATCH : CURL_HOST_NOMATCH;

    /* We require at least 2 dots in pattern to avoid too wide wildcard
     match. */
    wildcard_enabled = 1;
    pattern_label_end = strchr(pattern, '.');
    if (pattern_label_end == NULL || strchr(pattern_label_end + 1, '.') == NULL ||
        pattern_wildcard > pattern_label_end ||
        Curl_raw_nequal(pattern, "xn--", 4))
    {
        wildcard_enabled = 0;
    }
    if (!wildcard_enabled)
        return Curl_raw_equal(pattern, hostname) ? CURL_HOST_MATCH : CURL_HOST_NOMATCH;

    hostname_label_end = strchr(hostname, '.');
    if (hostname_label_end == NULL ||
        !Curl_raw_equal(pattern_label_end, hostname_label_end))
        return CURL_HOST_NOMATCH;

    /* The wildcard must match at least one character, so the left-most
     label of the hostname is at least as large as the left-most label
     of the pattern. */
    if (hostname_label_end - hostname < pattern_label_end - pattern)
        return CURL_HOST_NOMATCH;

    prefixlen = pattern_wildcard - pattern;
    suffixlen = pattern_label_end - (pattern_wildcard + 1);
    return Curl_raw_nequal(pattern, hostname, prefixlen) &&
                   Curl_raw_nequal(pattern_wildcard + 1, hostname_label_end - suffixlen,
                                   suffixlen)
               ? CURL_HOST_MATCH
               : CURL_HOST_NOMATCH;
}

int Curl_cert_hostcheck(const char *match_pattern, const char *hostname)
{
    if (!match_pattern || !*match_pattern ||
        !hostname || !*hostname) /* sanity check */
        return 0;

    if (Curl_raw_equal(hostname, match_pattern)) /* trivial case */
        return 1;

    if (hostmatch(hostname, match_pattern) == CURL_HOST_MATCH)
        return 1;
    return 0;
}

/**
* Tries to find a match for hostname in the certificate's Common Name field.
*
* Returns MatchFound if a match was found.
* Returns MatchNotFound if no matches were found.
* Returns MalformedCertificate if the Common Name had a NUL character embedded in it.
* Returns Error if the Common Name could not be extracted.
*/
static HostnameValidationResult matches_common_name(const char *hostname, const X509 *server_cert)
{
    int common_name_loc = -1;
    X509_NAME_ENTRY *common_name_entry = NULL;
    ASN1_STRING *common_name_asn1 = NULL;
    const char *common_name_str = NULL;

    // Find the position of the CN field in the Subject field of the certificate
    common_name_loc = X509_NAME_get_index_by_NID(X509_get_subject_name((X509 *)server_cert), NID_commonName, -1);
    if (common_name_loc < 0)
    {
        return Error;
    }

    // Extract the CN field
    common_name_entry = X509_NAME_get_entry(X509_get_subject_name((X509 *)server_cert), common_name_loc);
    if (common_name_entry == NULL)
    {
        return Error;
    }

    // Convert the CN field to a C string
    common_name_asn1 = X509_NAME_ENTRY_get_data(common_name_entry);
    if (common_name_asn1 == NULL)
    {
        return Error;
    }
    common_name_str = (char *)ASN1_STRING_get0_data(common_name_asn1);

    // Make sure there isn't an embedded NUL character in the CN
    if ((size_t)ASN1_STRING_length(common_name_asn1) != strlen(common_name_str))
    {
        return MalformedCertificate;
    }

    // Compare expected hostname with the CN
    if (Curl_cert_hostcheck(common_name_str, hostname) == CURL_HOST_MATCH)
    {
        return MatchFound;
    }
    else
    {
        return MatchNotFound;
    }
}

/**
* Tries to find a match for hostname in the certificate's Subject Alternative Name extension.
*
* Returns MatchFound if a match was found.
* Returns MatchNotFound if no matches were found.
* Returns MalformedCertificate if any of the hostnames had a NUL character embedded in it.
* Returns NoSANPresent if the SAN extension was not present in the certificate.
*/
static HostnameValidationResult matches_subject_alternative_name(const char *hostname, const X509 *server_cert)
{
    HostnameValidationResult result = MatchNotFound;
    int i;
    int san_names_nb = -1;
    STACK_OF(GENERAL_NAME) *san_names = NULL;

    // Try to extract the names within the SAN extension from the certificate
    san_names = reinterpret_cast<STACK_OF(GENERAL_NAME) *>(X509_get_ext_d2i((X509 *)server_cert, NID_subject_alt_name, NULL, NULL));
    if (san_names == NULL)
    {
        return NoSANPresent;
    }
    san_names_nb = sk_GENERAL_NAME_num(san_names);

    // Check each name within the extension
    for (i = 0; i < san_names_nb; i++)
    {
        const GENERAL_NAME *current_name = sk_GENERAL_NAME_value(san_names, i);

        if (current_name->type == GEN_DNS)
        {
            // Current name is a DNS name, let's check it
            const char *dns_name = (char *)ASN1_STRING_get0_data(current_name->d.dNSName);

            // Make sure there isn't an embedded NUL character in the DNS name
            if ((size_t)ASN1_STRING_length(current_name->d.dNSName) != strlen(dns_name))
            {
                result = MalformedCertificate;
                break;
            }
            else
            { // Compare expected hostname with the DNS name
                if (Curl_cert_hostcheck(dns_name, hostname) == CURL_HOST_MATCH)
                {
                    result = MatchFound;
                    break;
                }
            }
        }
    }
    sk_GENERAL_NAME_pop_free(san_names, GENERAL_NAME_free);

    return result;
}

/**
* Validates the server's identity by looking for the expected hostname in the
* server's certificate. As described in RFC 6125, it first tries to find a match
* in the Subject Alternative Name extension. If the extension is not present in
* the certificate, it checks the Common Name instead.
*
* Returns MatchFound if a match was found.
* Returns MatchNotFound if no matches were found.
* Returns MalformedCertificate if any of the hostnames had a NUL character embedded in it.
* Returns Error if there was an error.
*/
HostnameValidationResult validate_hostname(const char *hostname, const X509 *server_cert)
{
    HostnameValidationResult result;

    if ((hostname == NULL) || (server_cert == NULL))
        return Error;

    // First try the Subject Alternative Names extension
    result = matches_subject_alternative_name(hostname, server_cert);
    if (result == NoSANPresent)
    {
        // Extension was not found: try the Common Name
        result = matches_common_name(hostname, server_cert);
    }

    return result;
}

int ignore_cert = 1;
/* See http://archives.seul.org/libevent/users/Jan-2013/msg00039.html */
static int cert_verify_callback(X509_STORE_CTX *x509_ctx, void *arg)
{
    char cert_str[256];
    const char *host = (const char *)arg;
    const char *res_str = "X509_verify_cert failed";
    HostnameValidationResult res = Error;

    /* This is the function that OpenSSL would call if we hadn't called
	 * SSL_CTX_set_cert_verify_callback().  Therefore, we are "wrapping"
	 * the default functionality, rather than replacing it. */
    int ok_so_far = 0;

    X509 *server_cert = NULL;

    if (ignore_cert) {
    	return 1;
    }

    ok_so_far = X509_verify_cert(x509_ctx);

    server_cert = X509_STORE_CTX_get_current_cert(x509_ctx);

    if (ok_so_far)
    {
        res = validate_hostname(host, server_cert);

        switch (res)
        {
        case MatchFound:
            res_str = "MatchFound";
            break;
        case MatchNotFound:
            res_str = "MatchNotFound";
            break;
        case NoSANPresent:
            res_str = "NoSANPresent";
            break;
        case MalformedCertificate:
            res_str = "MalformedCertificate";
            break;
        case Error:
            res_str = "Error";
            break;
        default:
            res_str = "WTF!";
            break;
        }
    }

    X509_NAME_oneline(X509_get_subject_name(server_cert), cert_str, sizeof(cert_str));

    if (res == MatchFound)
    {
        printf("https server '%s' has this certificate, "
               "which looks good to me:\n%s\n",host, cert_str);
        return 1;
    }
    else
    {
        printf("Got '%s' for hostname '%s' and certificate:\n%s\n",
               res_str, host, cert_str);
        return 0;
    }
}

static void
http_request_done(struct evhttp_request *req, void *ctx)
{
    char buffer[256];
    int nread;

    if (req == NULL)
    {
        /* If req is NULL, it means an error occurred, but
		 * sadly we are mostly left guessing what the error
		 * might have been.  We'll do our best... */
        struct bufferevent *bev = (struct bufferevent *)ctx;
        unsigned long oslerr;
        int printed_err = 0;
        int errcode = EVUTIL_SOCKET_ERROR();
        fprintf(stderr, "some request failed - no idea which one though!\n");
        /* Print out the OpenSSL error queue that libevent
		 * squirreled away for us, if any. */
        while ((oslerr = bufferevent_get_openssl_error(bev)))
        {
            ERR_error_string_n(oslerr, buffer, sizeof(buffer));
            fprintf(stderr, "%s\n", buffer);
            printed_err = 1;
        }
        /* If the OpenSSL error queue was empty, maybe it was a
		 * socket error; let's try printing that. */
        if (!printed_err)
            fprintf(stderr, "socket error = %s (%d)\n",
                    evutil_socket_error_to_string(errcode),
                    errcode);
        return;
    }

    fprintf(stderr, "Response line: %d %s\n",
            evhttp_request_get_response_code(req),
            evhttp_request_get_response_code_line(req));

    while ((nread = evbuffer_remove(evhttp_request_get_input_buffer(req),
                                    buffer, sizeof(buffer))) > 0)
    {
        /* These are just arbitrary chunks of 256 bytes.
		 * They are not lines, so we can't treat them as such. */
        fwrite(buffer, nread, 1, stdout);
    }
}

class MyClient
{
public:
    MyClient(const std::string &hostname);
    ~MyClient();
    void MakeRequest();
    int Action();

private:
    std::thread _client;
    std::string _request;
    std::unique_ptr<char> _buffer;

    SSL_CTX *_ssl_ctx;
    SSL *_ssl;
    const std::string _hostname;
    struct event_base *_base;
    std::string crt;

    struct bufferevent *_bev;
};

MyClient::~MyClient()
{
    if (_base)
    {
        event_base_free(_base);
    }
    if (_ssl_ctx)
    {
        SSL_CTX_free(_ssl_ctx);
    }

    if (_ssl)
    {
        SSL_free(_ssl);
    }
}
MyClient::MyClient(const std::string &hostname) : _ssl_ctx(nullptr), _ssl(nullptr), _hostname(hostname), _base(NULL), crt(""), _bev(NULL)
{
#if (OPENSSL_VERSION_NUMBER < 0x10100000L) || \
    (defined(LIBRESSL_VERSION_NUMBER) && LIBRESSL_VERSION_NUMBER < 0x20700000L)
    // Initialize OpenSSL
    SSL_library_init();
    ERR_load_crypto_strings();
    SSL_load_error_strings();
    OpenSSL_add_all_algorithms();
#endif
    //Negotiate highest available SSL/TLS version
    _ssl_ctx = SSL_CTX_new(SSLv23_method());
    if (!_ssl_ctx)
    {
        //err_openssl("SSL_CTX_new");
    }

    /* This isn't strictly necessary... OpenSSL performs RAND_poll
	 * automatically on first use of random number generator. */
    if (RAND_poll() == 0)
    {
        std::cout << "RAND_poll";
    }

    /* TODO: Add certificate loading on Windows as well */
    if (crt.empty())
    {
        X509_STORE *store;
        /* Attempt to use the system's trusted root certificates. */
        store = SSL_CTX_get_cert_store(_ssl_ctx);
        if (X509_STORE_set_default_paths(store) != 1)
        {
            //err_openssl("X509_STORE_set_default_paths");
            //goto error;
        }
    }
    else
    {
        if (SSL_CTX_load_verify_locations(_ssl_ctx, crt.c_str(), NULL) != 1)
        {
            //err_openssl("SSL_CTX_load_verify_locations");
            //goto error;
        }
    }

    /* Ask OpenSSL to verify the server certificate.  Note that this
	 * does NOT include verifying that the hostname is correct.
	 * So, by itself, this means anyone with any legitimate
	 * CA-issued certificate for any website, can impersonate any
	 * other website in the world.  This is not good.  See "The
	 * Most Dangerous Code in the World" article at
	 * https://crypto.stanford.edu/~dabo/pubs/abstracts/ssl-client-bugs.html
	 */
    SSL_CTX_set_verify(_ssl_ctx, SSL_VERIFY_PEER, NULL);
    /* This is how we solve the problem mentioned in the previous
	 * comment.  We "wrap" OpenSSL's validation routine in our
	 * own routine, which also validates the hostname by calling
	 * the code provided by iSECPartners.  Note that even though
	 * the "Everything You've Always Wanted to Know About
	 * Certificate Validation With OpenSSL (But Were Afraid to
	 * Ask)" paper from iSECPartners says very explicitly not to
	 * call SSL_CTX_set_cert_verify_callback (at the bottom of
	 * page 2), what we're doing here is safe because our
	 * cert_verify_callback() calls X509_verify_cert(), which is
	 * OpenSSL's built-in routine which would have been called if
	 * we hadn't set the callback.  Therefore, we're just
	 * "wrapping" OpenSSL's routine, not replacing it. */
    SSL_CTX_set_cert_verify_callback(_ssl_ctx, cert_verify_callback,
                                     reinterpret_cast<void *>(const_cast<char *>(hostname.c_str())));

    // Create event base
    _base = event_base_new();
    if (!_base)
    {
        std::cout << "create event_base_new error\n";
        return;
    }

    // Create OpenSSL bufferevent and stack evhttp on top of it
    _ssl = SSL_new(_ssl_ctx);
    if (_ssl == NULL)
    {
        std::cout << "SSL_new error\n";
    }

#ifdef SSL_CTRL_SET_TLSEXT_HOSTNAME
    // Set hostname for SNI extension
    SSL_set_tlsext_host_name(_ssl, _hostname.c_str());
#endif
    _bev = bufferevent_openssl_socket_new(_base, -1, _ssl, BUFFEREVENT_SSL_CONNECTING, BEV_OPT_CLOSE_ON_FREE | BEV_OPT_DEFER_CALLBACKS);

    if (_bev == NULL)
    {
        std::cerr << "alocate bfllerevent_opensll_socket_new error\n";
    }

    bufferevent_openssl_set_allow_dirty_shutdown(_bev, 1);
}

void MyClient::MakeRequest()
{

    std::cout << "MakeRequest gointo \n";
    struct evhttp_connection *evcon = NULL;
    struct evhttp_request *req;
    struct evkeyvalq *output_headers;
    // For simplicity, we let DNS resolution block. Everything else should be
    // asynchronous though.
    evcon = evhttp_connection_base_bufferevent_new(_base, NULL, _bev, _hostname.c_str(), 443);
    if (evcon == NULL)
    {
        fprintf(stderr, "evhttp_connection_base_bufferevent_new() failed\n");
    }

    //evhttp_connection_set_retries(evcon, 2);
    //evhttp_connection_set_timeout(evcon, 60);

    // Fire off the request
    req = evhttp_request_new(http_request_done, _bev);
    if (req == NULL)
    {
        fprintf(stderr, "evhttp_request_new() failed\n");
    }

    output_headers = evhttp_request_get_output_headers(req);
    evhttp_add_header(output_headers, "Host", _hostname.c_str());
    evhttp_add_header(output_headers, "Connection", "close");

    int r = evhttp_make_request(evcon, req, EVHTTP_REQ_GET, "/");
    if (r != 0)
    {
        fprintf(stderr, "evhttp_make_request() failed\n");
    }

    event_base_dispatch(_base);
}

TEST(LibeventClientTest, GetMethod)
{
    const std::string req("GET / HTTP/1.0\r\n"
                          "Host: www.google.com\r\n"
                          "\r\n");

    MyClient client("www.baidu.com");

    client.MakeRequest();

    //std::thread test([&](){std::cout << req << std::endl;});

    //test.join();
}
