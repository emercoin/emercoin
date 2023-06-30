//DiplomaWidget.cpp by Emercoin developers
#include "DiplomaWidget.h"
#include "CheckDiplomaWidget.h"
#include "RegisterDiplomaWidget.h"
#include "RegisterUniversityWidget.h"
#include <QVBoxLayout>
#include <QSettings>
#include <QLabel>
#include <QCommandLinkButton>
//#include "AboutTrustedDiplomaWidget.h"
#include <cassert>

DiplomaWidget::DiplomaWidget(WalletModel* model, QWidget* parent) : model(model), QDialog(parent) {
    assert(model);
	setWindowTitle(tr("Trusted diploma"));
	setWindowIcon(QIcon(":/icons/TrustedDiploma-32.png"));

	auto lay = new QVBoxLayout(this);
    auto description = new QLabel(tr(
		"<a href=\"https://trusted-diploma.com/\">Trusted diploma</a> allows to store academic certificates in blockchain.<br>\n"
		"<a href=\"https://www.youtube.com/watch?v=ltP57wyIOd8\">Watch video</a>"
		));
    description->setOpenExternalLinks(true);
    lay->addWidget(description);

	_tab = new QTabWidget;
	lay->addWidget(_tab);
	auto addTab = [this](QWidget*w) { _tab->addTab(w, w->windowTitle()); };
	addTab(_CheckDiplomaWidget = new CheckDiplomaWidget());
    addTab(_RegisterUniversityWidget = new RegisterUniversityWidget(model));
    addTab(_RegisterDiplomaWidget = new RegisterDiplomaWidget(model));

	QSettings sett;
	int index = sett.value("DiplomaWidget.tabIndex", 0).toInt();
	index = qBound(0, index, _tab->count()-1);
	_tab->setCurrentIndex(index);

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
}
DiplomaWidget::~DiplomaWidget() {
	QSettings sett;
	sett.setValue("DiplomaWidget.tabIndex", _tab->currentIndex());
}
QString DiplomaWidget::name()const {
	auto w = _tab->currentWidget();
	if(w==_CheckDiplomaWidget)
		return {};
	if(w==_RegisterUniversityWidget)
		return _RegisterUniversityWidget->_NVPair->name();
	if(w==_RegisterDiplomaWidget)
		return _RegisterDiplomaWidget->_NVPair->name();
	return {};
}
QString DiplomaWidget::value()const {
	auto w = _tab->currentWidget();
	if(w==_CheckDiplomaWidget)
		return {};
	if(w==_RegisterUniversityWidget)
		return _RegisterUniversityWidget->_NVPair->value();
	if(w==_RegisterDiplomaWidget)
		return _RegisterDiplomaWidget->_NVPair->value();
	return {};
}
