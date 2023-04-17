//RandPayRequest.cpp by Emercoin developers
#include "RandPayRequest.h"
#include "paymentserver.h"
#include <QMessageBox>
#include <QVBoxLayout>
#include <QLabel>
#include <QTimer>
#include <QPushButton>
#include <QNetworkRequest>
#include <QNetworkAccessManager>
#include "../ui_interface.h"
#include "ConfigFile.h"
#include <qt/QNameCoin.h>

#include <wallet/wallet.h>
#include <amount.h>
#include <net.h>
#include <qt/walletcontroller.h>

//test links:
//emercoin://randpay?amount=0.001&chap=ffaaaa&risk=14&timeout=30
//&submit=ESCAPED_URI
RandPayRequest::RandPayRequest(const QUrl & u, PaymentServer* server): QUrlQuery(u) {
	_server = server;
	Q_ASSERT(_server);
}
QString RandPayRequest::parse() {
	bool ok;
#if 0
	const QString amount = queryItemValue("amount");
	if(amount.isEmpty())
		return "No 'amount' specified";
	_amount = amount.toDouble(&ok);
	if(!ok)
		return "'amount' is not number";
	if(_amount<=0)
		return "'amount' is negative";
#endif
	const QString chap = queryItemValue("chap"); // amount:risk:hex
	if(chap.isEmpty())
		return "'chap' is empty";
	for(QChar ch : chap) {
		if(ch.isDigit())
			continue;
                if(ch == ':' || ch == '.' )
                    continue; // Separator risk:challenge
		if('a'<=ch && ch<='f')
			continue;
		if('A'<=ch && ch<='F')
			continue;
		return "'chap' is not hex string";
	}
	_chap = chap;//QByteArray::fromHex(chap.toLatin1());
        _risk = 0; // Deprecated
#if 0
	const QString risk = queryItemValue("risk");//INT
	if(risk.isEmpty())
		return "'risk' is empty";
	_risk = risk.toULongLong(&ok);
	if(!ok)
		return "'risk' is not positive integer";
	if(_risk==0)
		return "'risk' is 0";
#endif
	const QString timeout = queryItemValue("timeout");//optional int
	if(!timeout.isEmpty()) {
		_timeout = timeout.toULongLong(&ok);
		if(!ok)
			return "'timeout' is not positive integer";
	}
	const QString submit = queryItemValue("submit");
	if(submit.isEmpty())
		return "'submit' is empty";
	_submit = submit;
	if(!_submit.isValid())
		return "'submit' is not a valid url";
	if(_submit.scheme().isEmpty()) {
		_submit.setScheme("https");
	} else if(_submit.scheme()!="http" && _submit.scheme()!="https") {
		return "'submit' has unknown protocol";
	}
	return checkAmountInWallet();
}

QString RandPayRequest::checkAmountInWallet()const {
    if(_server->m_wallet_controller->m_wallets.size() == 0)
        return tr("No wallet found");
    CWallet* pwalletMain = _server->m_wallet_controller->m_wallets[0]->wallet().getWallet().get();

    const CAmount nValue = COIN * _amount * _risk;
    const CAmount curBalance = pwalletMain->GetBalance(0, true).m_mine_trusted;
    // Check amount
    if (nValue <= 0)
        return tr("Invalid amount");

    if (nValue > curBalance)
        return "Insufficient funds";

    if (pwalletMain->GetBroadcastTransactions() && !g_connman)
        return tr("Error: Peer-to-peer functionality missing or disabled");

    if (pwalletMain->IsLocked())
        return "Error: Wallet locked, unable to create transaction!";

    if (fWalletUnlockMintOnly)
        return tr("Error: Wallet unlocked for block minting only, unable to create transaction.");
    return {};
}
void RandPayRequest::correctTimeout() {
	if(0 == _timeout) {//not specified
		_timeout = _config._timeout;//from config
		return;
	}
	const auto maxAllowed = 10 * _config._timeout;
	if(_timeout >= maxAllowed) {
		_timeout = maxAllowed;
	}
}
void RandPayRequest::emitMessage(PaymentServer* server, const QString & s) {
	server->message(tr("URI handling"), s, CClientUIInterface::MSG_WARNING);
}
void RandPayRequest::process(const QUrl & url, PaymentServer* server) {
	if(url.host() != QStringLiteral("randpay")) {
		emitMessage(server, tr("Not a randpay query"));
		return;
	}
	RandPayRequest r(url, server);
	r.process_(server);
	if(!r._error.isEmpty())
		emitMessage(server, r._error);
}
void RandPayRequest::process_(PaymentServer* server) {
	_error = parse();
	if(!_error.isEmpty())
		return;
	correctTimeout();
	if(needConfirmation()) {
		if(!askConfirmation()) {
			return;
		}
	}
	if(makePayment()) {
		//sucess dialog will be shown after network reply finishes
	}
	if(!_error.isEmpty()) {
		emitMessage(_server, _error);
	}
}
struct RandPayRequest::Dialog: public QMessageBox {
	int _secsLeft = 0;
	QString _defaultText;
	QPushButton* _cancel = 0;
	Dialog(int secs, bool defaultYes) {
		setWindowTitle(tr("Payment confirmation"));
		//setDetailedText(tr("Actual payment' is average payment expectation"));
		{
			auto ok = new QPushButton(tr("Confirm payment"));
			_cancel = new QPushButton(tr("Cancel"));
			ok->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-apply-32.png"));
			_cancel->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-cancel-32.png"));
			addButton(ok, QMessageBox::AcceptRole);
			addButton(_cancel, QMessageBox::RejectRole);
			//somehow AcceptRole/RejectRole returns the opposite, so just used this:
			connect(ok, &QPushButton::clicked, this, &QDialog::accept);
			connect(_cancel, &QPushButton::clicked, this, &QDialog::reject);

			auto btn = defaultYes ? ok : _cancel;
			setDefaultButton(btn);
			_defaultText = btn->text();
		}
		if(secs>0) {
			_secsLeft = secs + 1;//+1 for first ca;;
			auto timer = new QTimer(this);
			timer->start(1000);
			connect(timer, &QTimer::timeout, this, &Dialog::updateTimeLeft);
			updateTimeLeft();
		}
	}
	void updateTimeLeft() {
		_secsLeft--;
		if(_secsLeft==0) {
			defaultButton()->click();
			return;
		}
		defaultButton()->setText(_defaultText + QString(" (%1)").arg(_secsLeft));
	}
	void setTextBy(const RandPayRequest & r) {
		setText(tr(R"STR(Actual payment: %1 EMC
TX amount: %2 EMC
Probability: 1/%3
Timeout: %4s.)STR")
			.arg(r._amount)
			.arg(r._amount*r._risk)
			.arg(r._risk)
			.arg(r._timeout));
	}
};
bool RandPayRequest::askConfirmation()const {
	Dialog dlg(_timeout, _config._defaultYes);
	dlg.setTextBy(*this);
	int ret = dlg.exec();
	return ret == QDialog::Accepted;
}
void RandPayRequest::showSuccess(const QNetworkRequest & r) {

}
/* void RandPayRequest::showSuccess() {
	//"Randpay sent" с параметрами, подобными п 4, и чтоб оно исчезло после timio секунд, или нажатии кнопки OK.
	Dialog d(_timeout, true);
	d._cancel->hide();
	d.setWindowTitle(tr("Randpay sent"));
	d.exec();
}*/
bool RandPayRequest::makePayment() {
#ifdef ENABLE_BIP70
	QString s = QNameCoin::randPayCreateTx(*this, _error);
	if(!_error.isEmpty()) {
		return false;
	}
	if(!_submit.isEmpty() && _submit.isValid()) {
		_server->postRandpayRequest(_submit, s.toLocal8Bit());
	}
	return true;
#else
    return false;
#endif
}
bool RandPayRequest::needConfirmation()const {
	Q_ASSERT(_risk!=0);//_risk checked before
	return (_amount > _config._maxAmount || _amount / _risk > _config._maxPayment);
}
void RandPayRequest::readConfig() {
	ConfigFile config;
	_error =  config.load();
	if(!_error.isEmpty())
		return;
	_config._timeout = config.randPayTimeout();
	_config._maxAmount = config.randPayMaxAmount();
	_config._maxPayment = config.randPayMaxPayment();
	_config._defaultYes = config.randPaySubmit();
}
bool RandPayRequest::isRandPayUrl(const QUrl& url) {
	return url.isValid()
			&& url.scheme() == QStringLiteral("emercoin")
			&& url.host() == QStringLiteral("randpay");
}
