//InfoCardsWidget.cpp by Emercoin developers
#include "InfoCardsWidget.h"
#include "InfoCardDialog.h"
#include "InfoCardTableView.h"
#include "InfoCardTableModel.h"
#include "CertLogger.h"
#include "ShellImitation.h"
#include "Settings.h"
#include "OpenSslExecutable.h"
#include "InfoCardDialog.h"
#include "InfoCardExample.h"
#include <QVBoxLayout>
#include <QPushButton>
#include <QSplitter>
#include <QTimer>
#include <QCryptographicHash>
#include <QUuid>

InfoCardsWidget::InfoCardsWidget(QWidget*parent): QDialog(parent) {
	setWindowTitle(tr("InfoCard"));
	setWindowIcon(QIcon(":/icons/InfoCard-32.png"));
	_logger = new CertLogger();
	auto lay = new QVBoxLayout(this);
	auto label = new QLabel(
		"<a href=\"https://emercoin.com/documentation/blockchain-services/emerssl/emerssl-infocard/\">InfoCards</a> is a decentralized distributed 'business card' system on the Emercoin blockchain that complements EmerSSL's passwordless login");
	label->setOpenExternalLinks(true);
	lay->addWidget(label);
	_view = new InfoCardTableView(_logger);
	{
		auto lay2 = new QHBoxLayout;
		lay->addLayout(lay2);

		auto btnNew = new QPushButton(tr("New InfoCard"));
		btnNew->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/file-32.png"));
		btnNew->setShortcut(QKeySequence("Ctrl+N"));
		connect(btnNew, &QAbstractButton::clicked, this, &InfoCardsWidget::onCreate);
		lay2->addWidget(btnNew);

		_btnDelete = new QPushButton(tr("Delete selected"));
		_btnDelete->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-cancel-32.png"));
		connect(_btnDelete, &QAbstractButton::clicked, this, &InfoCardsWidget::onDelete);
		lay2->addWidget(_btnDelete);

		_btnOpenFolder = new QPushButton(tr("Open folder"));
		_btnOpenFolder->setToolTip(tr("Reveal InfoCard file in folder"));
		_btnOpenFolder->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-open-32.png"));
		connect(_btnOpenFolder, &QAbstractButton::clicked, _view, &InfoCardTableView::showInExplorer);
		lay2->addWidget(_btnOpenFolder);

		lay2->addStretch();
	}

	auto splitter = new QSplitter(Qt::Vertical);
	lay->addWidget(splitter);

	connect(_view->selectionModel(), &QItemSelectionModel::selectionChanged, this, &InfoCardsWidget::enableButtons);
	enableButtons();
	splitter->addWidget(_view);
	splitter->addWidget(_logger);
}
void InfoCardsWidget::enableButtons() {
	bool selected = _view->selectionModel()->hasSelection();
	_btnDelete->setEnabled(selected);
	//_btnGenerate->setEnabled(selected);
	_btnOpenFolder->setEnabled(selected);
}
QString InfoCardsWidget::randName() {
	//rand key chosed to be 64-bit so EmerSSL can optimize hashes processing etc;
	//also in plain C 64bit integers are much easier to manipulate than strings, son int64 are used;
	//we can't use std::random_device because it's deterministic on MinGW https://sourceforge.net/p/mingw-w64/bugs/338/
	QByteArray uid = QUuid::createUuid().toByteArray();
	uid = QCryptographicHash::hash(uid, QCryptographicHash::Sha256);
	uid.truncate(8);
	return uid.toHex();
}
void InfoCardsWidget::onCreate() {
	const QString fileName = randName() + ".info";
	const QDir dir = Settings::certDir();
	const QString path = dir.absoluteFilePath(fileName);
	_logger->setFileNear(dir, fileName);
	QString error;
	if(!Shell(_logger).write(path, "", error))
		return;
	auto model = _view->model();
	model->reload();
	const int row = _view->model()->indexByFile(path);
	Q_ASSERT(row!=-1);
	if(-1==row)
		return;
	_view->selectRow(row);
	_view->setFocus();

	InfoCardDialog dlg(*_view->model()->itemBy(row), _logger, this);
	dlg.setText(InfoCardExample::emptyDoc);
	if(dlg.exec() == QDialog::Accepted) {
		_view->dataChanged(row);
	} else {
		onDelete();
	}
}
void InfoCardsWidget::onDelete() {
	auto rows = _view->selectionModel()->selectedRows();
	if(rows.isEmpty())
		return;
	_logger->clear();
	_view->model()->removeRows(rows);
}
QString InfoCardsWidget::name()const {
	return {};
}
QString InfoCardsWidget::value()const {
	return {};
}
