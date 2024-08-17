//DpoCreateRecordWidget.cpp by Emercoin developers
#include "DpoCreateRecordWidget.h"
#include "EmailLineEdit.h"
#include "PhoneNumberLineEdit.h"
#include "SelectableTextEdit.h"
#include "NameEqValueTextEdit.h"
#include "QNameCoin.h"
#include "NameCoinStrings.h"
#include <QFormLayout>
#include <QSettings>
#include <QLabel>

DpoCreateRecordWidget::DpoCreateRecordWidget(WalletModel* model) : model(model) {
	setWindowTitle(tr("2) Register in organization"));
	auto lay = new QVBoxLayout(this);
    _NVPair = new NameValueLineEdits(model);
	_NVPair->setValueMultiline(true);

	lay->addWidget(newLabel(
		tr("Create a record with your name/nickname that is recognized in the organization you work for. "
		   "Or this may be another organization as well.")));

	auto form = new QFormLayout;
	lay->addLayout(form);
	_editName = addLineEdit(form, {}, tr("Organisation abbreviation (?)"),
		tr("This must be already registered DPO root record, like dpo:NDI"));
	form->addRow(_rootAvailable = new QLabel());
	_editSN = addLineEdit(form, {}, tr("Your name or nickname (?)"),
		tr("If this name is already registered, add any number after it (like ':1234')"));
	form->addRow(_NVPair->availabilityLabel());
	form->addRow(newLabel(tr("Send the following text to your organization:")));

	_askSignature = new SelectableTextEdit;
	_askSignature->setReadOnly(true);
	_askSignature->setPlaceholderText(tr("Text above is not filled"));
	form->addRow(_askSignature);

	_signature = addLineEdit(form, "Signature", tr("Received signature:"), {});
	_signature->setPlaceholderText(tr("Like Hyy39/xmrf7aYasLiK1TZdRSHkVq8US1w8K6rHIlb5DSFiINsX46H7HzBIn3R5uDfjFQNqo4voMYLMu8MisUIhk="));

	_NVPair->hide();
	lay->addWidget(_NVPair);
	lay->addWidget(newLabel(tr("This record must be created by person who's rights are recorded.\n"
		"After you create this name record, email this name to organization so they can sign it.")));
    lay->addStretch();
	updateSettings(false);
}
QLabel* DpoCreateRecordWidget::newLabel(const QString & s) {
	auto l = new QLabel(s);
	l->setWordWrap(true);
	l->setOpenExternalLinks(true);
	return l;
}
void DpoCreateRecordWidget::updateSettings(bool save) {
	QSettings sett;
	sett.beginGroup("DpoCreateRecordWidget");
	if(save)
		sett.setValue("name", _editName->text());
	else
		_editName->setText(sett.value("name").toString());

	if(save)
		sett.setValue("nick", _editSN->text());
	else
		_editSN->setText(sett.value("nick").toString());

	if(save)
		sett.setValue("SIG", _signature->text());
	else
		_signature->setText(sett.value("SIG").toString());
}
void DpoCreateRecordWidget::recalcValue() {
	QString name = _editName->text().trimmed();
	_rootAvailable->setText(NameCoinStrings::nameExistOrError(name, "dpo:"));
	const QString serial = _editSN->text().trimmed();
    if(name.isEmpty() || serial.isEmpty()) {
		_NVPair->setName({});//to display placeholderText
		_askSignature->setPlainText({});
	} else {
		QString s = name + ':' + serial;
        _NVPair->setName(s);
		_askSignature->setPlainText(tr("Hi! I want to participate in your program, please sign my name:\n%1\n"
			"and then send signature back to me. Thanks.").arg(s));
	}

	QStringList parts;
    for(auto e: _edits) {
        QString value = e->text().trimmed();
		if(auto tel = dynamic_cast<PhoneNumberLineEdit*>(e))
			value = tel->toPhoneNumber();
        if(!value.isEmpty())
            parts << e->objectName() + "=" + value;
    }
	parts << QString("name=") + serial;
	for(auto & s: parts)
		s = s.trimmed();
	QString v = parts.join('\n');
	if(v.isEmpty())
		v += "Signature=";
	_NVPair->setValue(v);
}
QLineEdit* DpoCreateRecordWidget::addLineEdit(QFormLayout*form, const QString& name,
	const QString& text, const QString& tooltip, bool readOnly)
{
	QLineEdit* edit = 0;
	if(readOnly) {
		edit = new SelectableLineEdit;
		edit->setReadOnly(true);
	} else {
		edit = new QLineEdit;
	}
    edit->setObjectName(name);
    edit->setClearButtonEnabled(true);
    connect(edit, &QLineEdit::textChanged, this, &DpoCreateRecordWidget::recalcValue);
	auto label = new QLabel(text);
	label->setToolTip(tooltip);
    edit->setToolTip(tooltip);
    form->addRow(label, edit);
	if(!name.isEmpty())
		_edits << edit;
    return edit;
}
