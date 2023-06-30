//DocNotarWidget.cpp by Emercoin developers
#include "DocNotarWidget.h"
#include "DpoUseCaseScheme.h"
#include "DpoCreateRootWidget.h"
#include "DpoCreateRecordWidget.h"
#include "DpoRegisterDocWidget.h"
#include <QVBoxLayout>
#include <QHBoxLayout>
#include <QCommandLinkButton>
#include <QSettings>
#include <QLabel>
#include <cassert>

DocNotarWidget::DocNotarWidget(WalletModel* model, QWidget*parent) : model(model), QDialog(parent) {
    assert(model);
	setWindowTitle(tr("DPO"));
	setWindowIcon(QIcon(":/icons/DPO-32.png"));

	auto lay = new QVBoxLayout(this);
    auto description = new QLabel(tr(
		R"STR(DPO is <a href="https://emercoin.com/en/emerdpo">Digital Proof of Ownership</a>)STR"
		));
    description->setOpenExternalLinks(true);
    lay->addWidget(description);

	_tab = new QTabWidget;
	lay->addWidget(_tab);
	auto addTab = [this](QWidget*w) {
		_tab->addTab(w, w->windowIcon(), w->windowTitle());
	};
	addTab(new DpoUseCaseScheme);
    addTab(_createRoot = new DpoCreateRootWidget(model));
    addTab(_createRecord = new DpoCreateRecordWidget(model));
    addTab(_registerDoc = new DpoRegisterDocWidget(model));

	{
		auto lay2 = new QHBoxLayout();
		lay->addLayout(lay2);
		auto btnOk = new QCommandLinkButton(tr("OK"), tr("Copy name and value to 'Manage names' page and close this window"));
		btnOk->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-apply-32.png"));
		connect(btnOk, &QAbstractButton::clicked, this, &QDialog::accept);
		lay2->addWidget(btnOk);

		auto btnCancel = new QCommandLinkButton(tr("Close window"));
		btnCancel->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-cancel-32.png"));
		connect(btnCancel, &QAbstractButton::clicked, this, &QDialog::reject);
		lay2->addWidget(btnCancel);
	}

	QSettings sett;
	int index = sett.value("DocNotarWidget.tabIndex", 0).toInt();
	index = qBound(0, index, _tab->count()-1);
	_tab->setCurrentIndex(index);
}
DocNotarWidget::~DocNotarWidget() {
	QSettings sett;
	sett.setValue("DocNotarWidget.tabIndex", _tab->currentIndex());
	_createRoot->updateSettings(true);
	_createRecord->updateSettings(true);
}
QString DocNotarWidget::name()const {
	auto w = _tab->currentWidget();
	if(w==_createRoot)
		return _createRoot->_NVPair->name();
	if(w==_registerDoc)
		return _registerDoc->_NVPair->name();
	if(w==_createRecord)
		return _createRecord->_NVPair->name();
	return {};
}
QString DocNotarWidget::value()const {
	auto w = _tab->currentWidget();
	if(w==_createRoot)
		return _createRoot->_NVPair->value();
	if(w==_registerDoc)
		return _registerDoc->_NVPair->value();
	if(w==_createRecord)
		return _createRecord->_NVPair->value();
	return {};
}
