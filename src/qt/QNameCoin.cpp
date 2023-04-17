#include <qt/QNameCoin.h>
#include <qt/RandPayRequest.h>

#include <rpc/server.h>

#include <QDate>

class WalletModel;

using CNameVal = std::vector<unsigned char>;
std::vector<CNameVal> NameCoin_myNames(WalletModel* model);
bool NameActive(const CNameVal& name, int currentBlockHeight = -1);
CNameVal toCNameVal(const std::string & s);
bool NameCoin_isMyName(const CNameVal & name, WalletModel* model);
CNameVal toCNameVal(const QString& s) {
	CNameVal ret;
	auto arr = s.toUtf8();
	for(char c: arr)
		ret.push_back(c);
	return ret;
}

bool QNameCoin::isMyName(const QString & name, WalletModel* model) {
    return NameCoin_isMyName(toCNameVal(name), model);
}
bool QNameCoin::nameActive(const QString & name) {
	return NameActive(toCNameVal(name));
}
QString toQString(const CNameVal & v) {
	const unsigned char* start = &v[0];
	return QString::fromUtf8(reinterpret_cast<const char*>(start), v.size());
}
static bool compareByLessParts(const QString& a, const QString& b) {
	int c1 = a.count(':');
	int c2 = b.count(':');
	if(c1<c2)
		return true;
	if(c1>c2)
		return false;
	return a<b;
}
QStringList QNameCoin::myNames(WalletModel* model, bool sortByLessParts) {
    QStringList ret;
    if (!model) return ret;
    std::vector<CNameVal> names = NameCoin_myNames(model);
	for(const auto & name: names) {
		ret << toQString(name);
	}
	if(sortByLessParts) {
		qSort(ret.begin(), ret.end(), compareByLessParts);
	}
	return ret;
}
QStringList QNameCoin::myNamesStartingWith(const QString & prefix, WalletModel* model) {
	QStringList ret;
    if (!model) return ret;
    for(const auto & s: myNames(model)) {
		if(s.startsWith(prefix))
			ret << s;
	}
	return ret;
}
QString QNameCoin::numberLikeBase64(quint64 n) {
	//like QByteArray::OmitTrailingEquals + but omit also leading zeroes
	static const QList<QChar> chars = []() {
		QList<QChar> ret;
		for(char c ='0'; c<='9'; ++c)
			ret << c;
		for(char c ='a'; c<='z'; ++c)
			ret << c;
		for(char c ='A'; c<='Z'; ++c)
			ret << c;
		ret << '_' << '-';
		return ret;
	}();
	if(0==n)
		return QStringLiteral("0");
	const quint32 base = chars.size();
	QString ret;
	while(n!=0) {
		ret.prepend(chars[n % base]);
		n /= base;
	}
	return ret;
}
QString QNameCoin::currentSecondsPseudoBase64() {
	const QDateTime start(QDate(2018, 11, 10));
	auto secs = start.secsTo(QDateTime::currentDateTime());
	return numberLikeBase64(secs);
}

QNameCoin::SignMessageRet QNameCoin::signMessageByName(const QString& name, const QString& message) {
	SignMessageRet ret;
	try {
		auto val = nameShow(name);
		UniValue address_uni = find_value(val, "address");
		if(!address_uni.isStr()) {
			ret.error = tr("Can't get address for name %1").arg(name);
			return ret;
		}
		ret.address = QString::fromStdString(address_uni.get_str());

		val = signMessageByAddress(ret.address, message);
		if(!val.isStr()) {
			ret.error = tr("Can't sign message");
			return ret;
		}
		ret.signature = QString::fromStdString(val.get_str());
	} catch (UniValue& objError) {
		ret.error = errorToString(objError);
	} catch (const std::exception& e) {
		ret.error = toString(e);
	}
	return ret;
}

UniValue randpay_mktx(const JSONRPCRequest& request);
QString QNameCoin::randPayCreateTx(const RandPayRequest & r, QString & error) {
	try {
		JSONRPCRequest request;
		request.params.setArray();
		request.params.push_back(UniValue(r._chap.toStdString()));
		request.params.push_back(UniValue((double)r._timeout));
		UniValue res = randpay_mktx(request);
		return QString::fromStdString(res.write());
	} catch (UniValue& objError) {
		error = errorToString(objError);
	} catch (const std::exception& e) {
		error = toString(e);
	}
	return {};
}
UniValue signmessage(const JSONRPCRequest& request);
UniValue QNameCoin::signMessageByAddress(const QString& address, const QString& message) {
	JSONRPCRequest request;
	request.params.setArray();
	request.params.push_back(address.toStdString());
	request.params.push_back(message.toStdString());
	return signmessage(request);
}

UniValue name_show(const JSONRPCRequest& request);
UniValue QNameCoin::nameShow(const QString& name) {
	JSONRPCRequest request;
	request.params.setArray();
	request.params.push_back(name.toStdString());
	return name_show(request);
}
QString QNameCoin::errorToString(UniValue& objError) {
	try {
		// Nice formatting for standard-format error
		std::string message = find_value(objError, "message").get_str();
		return QString::fromStdString(message);
	} catch (const std::runtime_error&) { // raised when converting to invalid type, i.e. missing code or message
		return QString::fromStdString(objError.write());// Show raw JSON object
	}
}
QString QNameCoin::toString(const std::exception& e) {
	return QString::fromStdString(e.what());
}
//name_filter
QList<QNameCoin::NVPair> QNameCoin::nameScan(const QString& prefix, int maxCount) {
	QList<QNameCoin::NVPair> ret;
	return ret;
}
