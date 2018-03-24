//ManageDnsPage.cpp.cpp by emercoin developers
#include "ManageDnsPage.h"
#include "IPv4LineEdit.h"
#include <QToolButton>
#include <QHBoxLayout>
#include <QFormLayout>
#include <QToolTip>
#include <QApplication>
#include <QClipboard>
#include <QLabel>
#include <QPushButton>
#include <QCommandLinkButton>

class SelectableLineEdit: public QLineEdit {
	public:
		SelectableLineEdit() {
		}
		virtual void mousePressEvent(QMouseEvent *e)override {
			QLineEdit::mousePressEvent(e);
			selectAll();
		}
};
ManageDnsPage::ManageDnsPage(QWidget*parent): QDialog(parent) {
	setWindowTitle(tr("DNS names"));
	{
		_editName = new QLineEdit;
		_editA = new IPv4LineEdit;
		_editAAAA = new QLineEdit;
		_editMx = new QLineEdit;
		_resultingName = new SelectableLineEdit;
		_resultingValue = new SelectableLineEdit;

        _editName->setClearButtonEnabled(true);
        _editA->setClearButtonEnabled(true);
        _editAAAA->setClearButtonEnabled(true);
        _editMx->setClearButtonEnabled(true);
    }
	auto lay = new QVBoxLayout(this);

    auto description = new QLabel(tr(
      "<a href=\"https://wiki.emercoin.com/en/EMCDNS\">EmerDNS</a> "
      "is a decentralized <a href=\"https://en.wikipedia.org/wiki/Domain_Name_System\">domain names system</a>"
      " supporting a full range of DNS <a href=\"https://en.wikipedia.org/wiki/List_of_DNS_record_types\">records.</a><br/>"
      "On this page you can prepare EmerDNS name-value pairs to use them in 'Manage names' tab."));
    description->setOpenExternalLinks(true);
    lay->addWidget(description);

	auto form = new QFormLayout;
	lay->addLayout(form);
	addHtmlRow(form, tr("DNS name"), _editName, tr("Like mysite.com"));
	addHtmlRow(form, tr("A record"), _editA, tr("IPv4 address, like 185.31.209.8"));
	addHtmlRow(form, tr("AAAA record"), _editAAAA, tr("IPv6 address, like 2a04:5340:1:1::3"));
	addHtmlRow(form, tr("MX record"), _editMx, tr("Mail exchange, like mx.yandex.ru:10"));

    connect(_editName, &QLineEdit::textChanged, this, &ManageDnsPage::recalcValue);
    connect(_editA, &QLineEdit::textChanged, this, &ManageDnsPage::recalcValue);
    connect(_editAAAA, &QLineEdit::textChanged, this, &ManageDnsPage::recalcValue);
    connect(_editMx, &QLineEdit::textChanged, this, &ManageDnsPage::recalcValue);

	form->addRow(new QLabel(tr("Resulting values to insert to blockchain:")));
	{
		auto w = new QWidget;
		auto lay = new QHBoxLayout(w);
		lay->setSpacing(0);
		lay->setMargin(0);
		
        _resultingName->setPlaceholderText(tr("This field will contain name to insert to 'Manage names' panel"));
		_resultingName->setReadOnly(true);
		lay->addWidget(_resultingName);
		
		auto copy = new QToolButton;
		copy->setText(tr("Copy to clipboard"));
		connect(copy, &QAbstractButton::clicked, this, [=] () {
			_resultingValue->deselect();
			_resultingName->selectAll();
			QApplication::clipboard()->setText(_resultingName->text());
			auto pt = copy->rect().bottomLeft();
			QToolTip::showText(copy->mapToGlobal(pt), tr("Copied"));
		});
		lay->addWidget(copy);
		form->addRow(tr("Name:"), w);
	}
	{
		auto w = new QWidget;
		auto lay = new QHBoxLayout(w);
		lay->setSpacing(0);
		lay->setMargin(0);

		_resultingValue->setReadOnly(true);
        _resultingValue->setPlaceholderText(tr("This field will contain value to insert to 'Manage names' panel"));
		lay->addWidget(_resultingValue);

		auto copy = new QToolButton;
		copy->setText(tr("Copy to clipboard"));
		connect(copy, &QAbstractButton::clicked, this, [=] () {
			_resultingName->deselect();
			_resultingValue->selectAll();
			QApplication::clipboard()->setText(_resultingValue->text());
			auto pt = copy->rect().bottomLeft();
			QToolTip::showText(copy->mapToGlobal(pt), tr("Copied"));
		});
		lay->addWidget(copy);
		form->addRow(tr("Value:"), w);
	}
    {
		auto lay = new QHBoxLayout();
		auto btnOk = new QCommandLinkButton(tr("OK"), tr("Copy name and value to 'Manage names' page and close this window"));
		btnOk->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-apply-32.png"));
		connect(btnOk, &QAbstractButton::clicked, this, [this] () {
            previewName(_resultingName->text());
            previewValue(_resultingValue->text());
			accept();
        });
		lay->addWidget(btnOk);

		auto btnCancel = new QCommandLinkButton(tr("Close window"));
		btnCancel->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-cancel-32.png"));
		connect(btnCancel, &QAbstractButton::clicked, this, &QDialog::reject);
		lay->addWidget(btnCancel);

		form->addRow(lay);
    }
    lay->addStretch();
}
void ManageDnsPage::recalcValue() {
    const QString dns = _editName->text().trimmed();
    if(dns.isEmpty())
        _resultingName->setText(QString());//to display placeholderText
    else
        _resultingName->setText("dns:" + dns);

	const QString A = _editA->text().trimmed();
	const QString AAAA = _editAAAA->text().trimmed();
	const QString MX = _editMx->text().trimmed();
	QStringList parts;
	if(!A.isEmpty())
		parts << "A=" + A;
	if(!AAAA.isEmpty())
		parts << "AAAA=" + AAAA;
	if(!MX.isEmpty())
		parts << "MX=" + MX;
	_resultingValue->setText(parts.join('|'));
}
void ManageDnsPage::addHtmlRow(QFormLayout*form, QString text, QLineEdit*line, QString tooltip) {
	auto label = new QLabel(text);
	label->setToolTip(tooltip);
	line->setPlaceholderText(tooltip);
	form->addRow(label, line);
}
