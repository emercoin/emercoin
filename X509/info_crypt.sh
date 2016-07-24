#!/bin/sh 
#
# InfoCard encryptor
# Uses sha256 from original file as search key (1st 64 bits) and password (160 bits)
# At encrypt secondary file, use original file as 2nd parameter.

FNAME=$1
if [ -z "$FNAME" ] ; then
    echo "Use parameter: Text InfoCard file *.info"
    echo "To create InfoCard file, use template infocard_example.info"
    exit
fi

OUTF=$FNAME.ze

HD=`head -n 1 $FNAME`

PREFIX=`echo $HD | cut -c 1-7`
if [ $PREFIX = "#!info:" ] ; then
    INDEX=`echo $HD | cut -d : -f 2`
    PASSW=`echo $HD | cut -d : -f 3`
else
    SHA256=`openssl dgst -sha256 $FNAME | sed 's/^.* //'`
    INDEX=`echo $SHA256 | cut -c 1-16`		# 64 bit index
    PASSW=`echo $SHA256 | cut -c 21-50`		# 120 bit password
    echo "#!info:$INDEX:$PASSW" >$OUTF
    cat $FNAME >> $OUTF
    mv $OUTF $FNAME
fi

grep -v '^#' $FNAME | gzip -c -9 | openssl enc -aes-256-cbc -salt -out $OUTF -pass pass:$PASSW

echo
echo "Please, deposit into Emercoin NVS pair:"
echo "  Key:   info:$INDEX"

echo "  Value: body of the file: $OUTF"

echo
echo "To link EMCSSL Certificate to this info file, run ./gen_tpl.sh and use"
echo " value for UID: info:$INDEX:$PASSW"

# To decode, run something like following:
#openssl aes-256-cbc -d -pass pass:adaf69d1e661db59cf280e60592b2e79eb065743 -in infocard_example.info.ze | zcat

