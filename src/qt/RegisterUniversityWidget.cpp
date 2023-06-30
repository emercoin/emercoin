//RegisterUniversityWidget.cpp by Emercoin developers
#include "RegisterUniversityWidget.h"
#include "EmailLineEdit.h"
#include "PhoneNumberLineEdit.h"
#include "CheckDiplomaWidget.h"
#include "SelectableLineEdit.h"
#include "NameEqValueTextEdit.h"
#include <QVBoxLayout>
#include <QFormLayout>
#include <QLabel>
#include <QIcon>
#include <cassert>

RegisterUniversityWidget::RegisterUniversityWidget(WalletModel* model) : model(model) {
    assert(model);
    setWindowTitle(tr("Register university"));
	setWindowIcon(QIcon(":/icons/Trusted-diploma-16-monochrome.png"));
	auto lay = new QVBoxLayout(this);
    _NVPair = new NameValueLineEdits(model);
	_NVPair->setValueMultiline(true);

	auto description = new QLabel(tr("You must first create root record (register university) to sign diplomas"));
    description->setOpenExternalLinks(true);
    lay->addWidget(description);

	auto form = new QFormLayout;
	lay->addLayout(form);
	_editName = addLineEdit(form, QString(), tr("University abbreviation for blockchain"),
		tr("Use short name preferably. If this abbreviation is already registered, you can modify it (for example, add city name) to prevent conflicts"));
	form->addRow(_NVPair->availabilityLabel());
	addLineEdit(form, "brand", tr("Full university name"), {})
		->setPlaceholderText(tr("or brand name. Any text here."));
    addLineEdit(form, "url", tr("Web-site address"), tr("Your university website address"));
	{
		auto lay = new QVBoxLayout;
		auto email = new EmailLineEdit;
		email->setObjectName("email");
		_edits << email;
		connect(email, &QLineEdit::textChanged, this, &RegisterUniversityWidget::recalcValue);
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
		connect(tel, &QLineEdit::textChanged, this, &RegisterUniversityWidget::recalcValue);
		_edits << tel;
		form->addRow(tr("Telephone"), tel);
	}
	form->addRow(new QLabel("Any other data:"));
	_editOther = new NameEqValueTextEdit;
	_editOther->setPlaceholderText("Format: key=value (like 'country=UK'), each 'name=value' pair on a new line");
	connect(_editOther, &QPlainTextEdit::textChanged, this, &RegisterUniversityWidget::recalcValue);
	form->addRow(_editOther);
	{
		_hrefForSite = addLineEdit(form, {}, tr("Hyperlink for your site (?)"),
			tr("You can place this hyperlink to your site, so visitors can check verified diplomas by it."), true);
		_hrefForSite->setPlaceholderText(tr("This field will contain web address to check your university diplomas"));
	}
	lay->addWidget(_NVPair);
	_NVPair->hide();
    lay->addStretch();
}
void RegisterUniversityWidget::recalcValue() {
	const QString name = _editName->text().trimmed();
    if(name.isEmpty()) {
        _NVPair->setName(QString());//to display placeholderText
		_hrefForSite->setText({});
	} else {
        _NVPair->setName("dpo:" + name);
		_hrefForSite->setText(CheckDiplomaWidget::s_checkUniversity.arg(name));
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
QLineEdit* RegisterUniversityWidget::addLineEdit(QFormLayout*form, const QString& name,
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
    connect(edit, &QLineEdit::textChanged, this, &RegisterUniversityWidget::recalcValue);
	auto label = new QLabel(text);
	label->setToolTip(tooltip);
    edit->setToolTip(tooltip);
    form->addRow(label, edit);
	if(!name.isEmpty())
		_edits << edit;
    return edit;
}
