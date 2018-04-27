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
    _resultingName = new SelectableLineEdit;
    _resultingValue = new SelectableLineEdit;
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
    _editName = addLineEdit(form, "", tr("DNS name"), tr("Like mysite.com"));
    addLineEdit(form, "A", tr("A record"), tr("IPv4 address, like 185.31.209.8"));
    addLineEdit(form, "AAAA", tr("AAAA record"), tr("IPv6 address, like 2a04:5340:1:1::3"));
    addLineEdit(form, "MX", tr("MX record"), tr("Mail exchanger, like mx.yandex.ru:10"));
    addLineEdit(form, "NS", tr("NS record"), tr("Name server; delegates a DNS zone to use the given authoritative name servers"));
    addLineEdit(form, "CNAME", tr("CNAME"), tr("Canonocal name; alias of one name to another: the DNS lookup will continue by retrying the lookup with the new name."));
    addLineEdit(form, "PTR", tr("PTR"), tr("Pointer to a canonical name. Unlike a CNAME, DNS processing stops and just the name is returned."));
    addLineEdit(form, "TXT", tr("TXT"), tr("Arbitrary human-readable text. Nowdays more often carries machine-readable data, such as Policy Framework, DKIM, DMARC, DNS-SD, etc."));
    addLineEdit(form, "SD", tr("SD"), tr("Subdomain - EmerDns feature"));


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

    QStringList parts;
    for(auto e: _edits) {
        if(e==_editName)
            continue;
        QString value = e->text().trimmed();
        if(!value.isEmpty())
            parts << e->_dnsRecord + "=" + value;
    }
	_resultingValue->setText(parts.join('|'));
}
ManageDnsPage::LineEdit* ManageDnsPage::addLineEdit(QFormLayout*form, QString dnsRecord, QString text, QString tooltip) {
    auto edit = new LineEdit;
    edit->_dnsRecord = dnsRecord;
    edit->setClearButtonEnabled(true);
    connect(edit, &QLineEdit::textChanged, this, &ManageDnsPage::recalcValue);
	auto label = new QLabel(text);
	label->setToolTip(tooltip);
    edit->setToolTip(tooltip);
    form->addRow(label, edit);
    _edits << edit;
    return edit;
}
