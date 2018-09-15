//NameValueLineEdits.cpp by Emercoin developers
#include "NameValueLineEdits.h"
#include <QPlainTextEdit>
#include <QFormLayout>
#include <QHBoxLayout>
#include <QVBoxLayout>
#include <QToolButton>
#include <QApplication>
#include <QClipboard>
#include <QToolTip>
#include <QLabel>

class SelectableTextEdit: public QPlainTextEdit {
	public:
		SelectableTextEdit() {}

		QPointer<QWidget> _buddyToShowToolip;//use this window if not set
		virtual void mousePressEvent(QMouseEvent *e)override {
			QPlainTextEdit::mousePressEvent(e);
			if(isReadOnly())
				selectAll();
		}
		void copyAndShowTooltip(QLineEdit*toDeselect = 0) {
			if(toDeselect)
				toDeselect->deselect();
			selectAll();
			QApplication::clipboard()->setText(toPlainText());
			QWidget* wNear = _buddyToShowToolip;
			if(!wNear)
				wNear = this;
			auto pt = wNear->rect().bottomLeft();
			QToolTip::showText(wNear->mapToGlobal(pt), tr("Copied"));
		}
};
NameValueLineEdits::NameValueLineEdits() {
	_resultingName = new SelectableLineEdit;
    _resultingValue = new SelectableLineEdit;
	_resultingMultiline = new SelectableTextEdit;

	auto form = new QFormLayout(this);
	form->setMargin(0);//usually this widget is embedded to other so no need
	form->addRow(new QLabel(tr("If you have filled in all the fields, open Emercoin wallet and copy value below in emercoin blockchain ('Manage names' tab in wallet):")));
	{
		auto w = new QWidget;
		auto lay = new QHBoxLayout(w);
		lay->setSpacing(0);
		lay->setMargin(0);
		
		QString namePlaceholder = tr("This field will contain name to insert to 'Manage names' panel");
        _resultingName->setPlaceholderText(namePlaceholder);
		_resultingName->setToolTip(tr("Read-only") + ". " +  namePlaceholder);
		_resultingName->setReadOnly(true);
		lay->addWidget(_resultingName);
		
		auto copy = new QToolButton;
		copy->setText(tr("Copy to clipboard"));
		_resultingName->_buddyToShowToolip = copy;
		connect(copy, &QAbstractButton::clicked, this, [=] () {
			_resultingName->copyAndShowTooltip(_resultingValue);
		});
		lay->addWidget(copy);
		form->addRow(tr("Name:"), w);
	}
	auto layValue = new QVBoxLayout;
	{
		_w1Line = new QWidget;
		auto lay = new QHBoxLayout(_w1Line);
		lay->setSpacing(0);
		lay->setMargin(0);

		_resultingValue->setReadOnly(true);
        _resultingValue->setPlaceholderText(tr("This field will contain value to insert to 'Manage names' panel"));
		lay->addWidget(_resultingValue);

		auto copy = new QToolButton;
		copy->setText(tr("Copy to clipboard"));
		connect(copy, &QAbstractButton::clicked, this, [=]() {
			_resultingValue->copyAndShowTooltip(_resultingName);
		});
		lay->addWidget(copy);
		layValue->addWidget(_w1Line);
	}
	{
		_wMultiLine = new QWidget;
		auto lay = new QHBoxLayout(_wMultiLine);
		lay->setSpacing(0);
		lay->setMargin(0);

		_resultingMultiline->setReadOnly(true);
        _resultingMultiline->setPlaceholderText(tr("This field will contain value to insert to 'Manage names' panel"));
		lay->addWidget(_resultingMultiline);

		auto copy = new QToolButton;
		copy->setText(tr("Copy to clipboard"));
		_resultingMultiline->_buddyToShowToolip = copy;
		connect(copy, &QAbstractButton::clicked, this, [=]() {
			_resultingMultiline->copyAndShowTooltip(_resultingName);
		});
		lay->addWidget(copy);
		layValue->addWidget(_wMultiLine);
	}
	form->addRow(tr("Value:"), layValue);
	if(_multiline)
		_w1Line->hide();
	else
		_wMultiLine->hide();
}
void NameValueLineEdits::setName(const QString & s) {
	_resultingName->setText(s);
}
void NameValueLineEdits::setValuePlaceholder(const QString & s) {
	_resultingValue->setPlaceholderText(s);
	_resultingMultiline->setPlaceholderText(s);
}
void NameValueLineEdits::copyValue() {
	if(_multiline) {
		_resultingMultiline->copyAndShowTooltip(_resultingName);
		return;
	}
	_resultingValue->copyAndShowTooltip(_resultingName);
}
void NameValueLineEdits::setValue(const QString & s) {
	_resultingValue->setText(s);
	_resultingMultiline->setPlainText(s);
}
void NameValueLineEdits::setValueMultiline(bool multi) {
	if(_multiline==multi)
		return;
	_multiline = multi;
	_wMultiLine->setVisible(_multiline);
	_w1Line->setVisible(!_multiline);
}
void NameValueLineEdits::setValueReadOnly(bool b) {
	_resultingValue->setReadOnly(b);
	_resultingMultiline->setReadOnly(b);
}
QString NameValueLineEdits::name()const {
	return _resultingName->text();
}
QString NameValueLineEdits::value()const {
	if(_multiline)
		return _resultingMultiline->toPlainText();
	return _resultingValue->text();
}
