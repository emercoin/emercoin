//DpoCreateRootWidget.cpp by Emercoin developers
#include "DpoCreateRootWidget.h"
#include "EmailLineEdit.h"
#include "PhoneNumberLineEdit.h"
#include "SelectableLineEdit.h"
#include "NameEqValueTextEdit.h"
#include <QFormLayout>
#include <QSettings>
#include <QLabel>
#include <cassert>

DpoCreateRootWidget::DpoCreateRootWidget(WalletModel* model) : model(model) {
    assert(model);
	setWindowTitle(tr("1) Organization registration"));
	auto lay = new QVBoxLayout(this);
    _NVPair = new NameValueLineEdits(model);
	_NVPair->setValueMultiline(true);

	auto description = new QLabel(tr("Create a root record for an organization:"));
    description->setOpenExternalLinks(true);
    lay->addWidget(description);

	auto form = new QFormLayout;
	lay->addLayout(form);
	_editName = addLineEdit(form, QString(), tr("Organization abbreviation for blockchain"),
		tr("Use short name preferably. If this abbreviation is already registered, you can modify name (for example, add city name) to prevent conflicts"));
	form->addRow(_NVPair->availabilityLabel());
	addLineEdit(form, "brand", tr("Full organization name)"), {})
		->setPlaceholderText(tr("or brand name. Any text here."));
    addLineEdit(form, "url", tr("Web-site address"), tr("Your organization website address"));
	{
		auto lay = new QVBoxLayout;
		auto email = new EmailLineEdit;
		email->setObjectName("email");
		_edits << email;
		connect(email, &QLineEdit::textChanged, this, &DpoCreateRootWidget::recalcValue);
		lay->addWidget(email);

		QLabel* errorDesc = new QLabel;
		lay->addWidget(errorDesc);
		email->validator()->setErrorLabel(errorDesc);
		errorDesc->hide();

		form->addRow(tr("E-mail:"), lay);
	}
	{
		auto tel = new PhoneNumberLineEdit;
		tel->setObjectName("tel");
		connect(tel, &QLineEdit::textChanged, this, &DpoCreateRootWidget::recalcValue);
		_edits << tel;
		form->addRow(tr("Telephone"), tel);
	}
	form->addRow(new QLabel("Any other data:"));
	_editOther = new NameEqValueTextEdit;
	_editOther->setPlaceholderText("Format: key=value (like 'country=UK'), each 'name=value' pair on a new line");
	connect(_editOther, &QPlainTextEdit::textChanged, this, &DpoCreateRootWidget::recalcValue);
	form->addRow(_editOther);
	_NVPair->hide();
	lay->addWidget(_NVPair);
    lay->addStretch();
	updateSettings(false);
}
void DpoCreateRootWidget::updateSettings(bool save) {
	QSettings sett;
	sett.beginGroup("DpoCreateRecordWidget");
	if(save)
		sett.setValue("name", _editName->text());
	else
		_editName->setText(sett.value("name").toString());
}
void DpoCreateRootWidget::recalcValue() {
	const QString name = _editName->text().trimmed();
    if(name.isEmpty()) {
        _NVPair->setName(QString());//to display placeholderText
	} else {
        _NVPair->setName("dpo:" + name);
	}

	QStringList parts;
    for(auto e: _edits) {
        QString value = e->text().trimmed();
		if(auto tel = dynamic_cast<PhoneNumberLineEdit*>(e))
			value = tel->toPhoneNumber();
        if(!value.isEmpty())
            parts << e->objectName() + "=" + value;
    }
	parts << _editOther->toPlainText().split('\n', QString::SkipEmptyParts);
	for(auto & s: parts)
		s = s.trimmed();
	_NVPair->setValue(parts.join('\n'));
}
QLineEdit* DpoCreateRootWidget::addLineEdit(QFormLayout*form, const QString& name,
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
    connect(edit, &QLineEdit::textChanged, this, &DpoCreateRootWidget::recalcValue);
	auto label = new QLabel(text);
	label->setToolTip(tooltip);
    edit->setToolTip(tooltip);
    form->addRow(label, edit);
	if(!name.isEmpty())
		_edits << edit;
    return edit;
}
