#!/bin/sh -v
rm -f emcssl_ca.key emcssl_ca.crt

openssl ecparam -genkey -name secp256k1 -out emcssl_ca.key
openssl req -new -key emcssl_ca.key -out csr.pem \
    -subj '/O=Emercoin/OU=PKI/CN=EMCSSL/emailAddress=team@emercoin.com/UID=EMC'
openssl req -x509 -days 36500 -key emcssl_ca.key -in csr.pem \
    -out emcssl_ca.crt

rm csr.pem

#openssl req -new -newkey rsa:4096 -nodes -keyout emcssl_ca.key -x509 -days 36500 \
#  -subj '/O=Emercoin/OU=EMCSSL/CN=EMCSSL/emailAddress=team@emercoin.com/UID=EMC' \
#  -out emcssl_ca.crt
