#!/bin/sh
echo "   New Emercoin WWW PKI Certificate generation"
echo 
echo 
echo " Please, answer to following questions."
echo 
echo " 1. Your common name (MANDATORY)"
echo " This is free-form text printable usename"
echo " Can be login ID like 'inflat0r'"
echo " Or personal name, like John Q. Public"
printf "CN: "
read CN
if [ -z "$CN" ] ; then
    echo "ERROR: Common Name must not be empty"
    exit 1
fi
SUBJ="/CN=$CN"

echo " 2. Your e-mail address (optional)"
echo " For example: abdul@bubbleinflatord.com"
printf "eMail: "
read EMAIL
if [ ! -z "$EMAIL" ] ; then
  SUBJ="$SUBJ/emailAddress=$EMAIL"
fi

echo " 3. Your UID for retrieve vCard info (optional)" 
echo "This value printed by script info_crypt.sh during *.ze file creation"
echo "For example: info:2f2c5a7c57d60668:74744c6e4443df490eab0807052bb9"
printf "UID: "
read XUID
if [ ! -z "$XUID" ] ; then
  SUBJ="$SUBJ/UID=$XUID"
fi

#FNAME=$(printf "%08x%08x.tpl" `od -vAn -N4 -tu4 < /dev/urandom` `od -vAn -N4 -tu4 < /dev/urandom`)
#
FNAME=`openssl rand 8 | od -xAn | tr -d '[[:space:]]' | sed 's/^0/f/'`
FNAME="$FNAME.tpl"

echo "Created EMCSSL Certificate template: $FNAME"
#echo "Subj=$SUBJ"
echo $SUBJ >$FNAME
