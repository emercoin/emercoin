FILE_NAME=$1
PRIVATE_KEY=${FILE_NAME}_private.pem
PUBLIC_KEY=${FILE_NAME}_public.pem
BITCOIN_PRIVATE_KEY=emercoin_${FILE_NAME}_private.key
ALERT_PRIVATE_KEY=emercoin_${FILE_NAME}_private_alert.key
BITCOIN_PUBLIC_KEY=emercoin_${FILE_NAME}_public.key

echo "Generating private key"
openssl ecparam -genkey -name secp256k1 -rand /dev/urandom -out $PRIVATE_KEY

echo "Generating public key"
openssl ec -in $PRIVATE_KEY -pubout -out $PUBLIC_KEY

echo "Generating Emercoin private key"
openssl ec -in $PRIVATE_KEY -outform DER|tail -c +8|head -c 32|xxd -p -c 32 > $BITCOIN_PRIVATE_KEY
echo 308201130201010420`cat $BITCOIN_PRIVATE_KEY`a081a53081a2020101302c06072a8648ce3d0101022100ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff >$ALERT_PRIVATE_KEY
echo "Generating Emercoin public key"
openssl ec -in $PRIVATE_KEY -pubout -outform DER|tail -c 65|xxd -p -c 65 > $BITCOIN_PUBLIC_KEY

echo "Files created!"

