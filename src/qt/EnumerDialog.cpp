//EnumerDialog.cpp by Emercoin developers
#include "EnumerDialog.h"
#include "PhoneNumberLineEdit.h"
#include <QFormLayout>
#include <QIcon>
#include <QLabel>
#include <cassert>

EnumerDialog::EnumerDialog(WalletModel* model) {
    assert(model);
	setWindowTitle(tr("ENUMER"));
	setWindowIcon(QIcon(":/icons/Enumer-32.png"));

	auto lay = new QFormLayout(this);
    _NVEdit = new NameValueLineEdits(model);
	_NVEdit->setValueMultiline(true);
	_NVEdit->setValueReadOnly(false);
	_phone = new PhoneNumberLineEdit;
	connect(_phone, &QLineEdit::textChanged, this, &EnumerDialog::generateNVPair);
	connect(_antiSquatter, static_cast<void(QSpinBox::*)(int)>(&QSpinBox::valueChanged), this, &EnumerDialog::generateNVPair);
	_phone->setFocus();

	auto href = new QLabel(tr("<a href=\"https://emercoin.com/en/documentation/blockchain-services/enumer\">ENUMER</a> is a free VoIP system, based on emercoin blockchain"
		"<br>\nStep 1: create ENUM record"));
	href->setOpenExternalLinks(true);
	lay->addRow(href);
	//Good russian article, maybe translate it to english: https://habr.com/company/emercoin/blog/337034/
	lay->addRow(tr("Phone number:"), _phone);//E.164 format https://en.wikipedia.org/wiki/E.164
	{
		QString str = tr("If someone created record with same phone number, just add random number suffix to create unique name and verify it's you by email");
		_antiSquatter->setToolTip(str);
		auto desc = new QLabel(tr("Suffix (?):"));
		desc->setToolTip(str);
		lay->addRow(desc, _antiSquatter);
	}

	{
		QString str = tr(R"DEMO(Add several lines here to value, like E2U+sip=Priority|Preference|Regex (i. e., E2U+sip=100|10|!^(.*)$!sip:17772325555@in.callcentric.com!) or signature records from steps below)DEMO");
		_NVEdit->setValuePlaceholder(str);
	}
	lay->addRow(_NVEdit);
	lay->addRow(new QLabel("Step 2: add this name-value pair to the emercoin blockchain"));

	auto labelEmail = new QLabel("Step 3: verify it by writing to <a href=\"mailto:enumer@emercoin.com\">enumer@emercoin.com</a>, get verification record and update value");
	labelEmail->setOpenExternalLinks(true);
	lay->addRow(labelEmail);
	lay->addRow(new QLabel(tr("Step 4: ")));
}
void EnumerDialog::generateNVPair() {
	QString phone = _phone->toPhoneNumber();
	QString name = QString("enum:%1:%2").arg(phone).arg(_antiSquatter->text());
	_NVEdit->setName(name);
}
