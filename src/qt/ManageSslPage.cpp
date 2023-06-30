//ManageSslPage.cpp by Emercoin developers
#include <qt/ManageSslPage.h>
#include <qt/Settings.h>
#include <qt/CertTableModel.h>
#include <qt/EmailLineEdit.h>
#include <qt/CertTableView.h>
#include <qt/CertLogger.h>
#include <qt/ShellImitation.h>
#include <qt/OpenSslConfigWriter.h>
#include <qt/OpenSslExecutable.h>

#include <QVBoxLayout>
#include <QHBoxLayout>
#include <QFormLayout>
#include <QLabel>
#include <QTimer>
#include <QSplitter>
#include <QPushButton>
#include <QUuid>
#include <QDialogButtonBox>
#include <QMessageBox>
#include <QCryptographicHash>

ManageSslPage::ManageSslPage(QWidget*parent): QDialog(parent) {
	setWindowTitle(tr("EmerSSL certificates"));
	setWindowIcon(QIcon(":/icons/EmerSSL-32.png"));
	_logger = new CertLogger();
	auto lay = new QVBoxLayout(this);
	//https://cryptor.net/tutorial/sozdaem-ssl-sertifikat-emcssl-dlya-avtorizacii-na-saytah
	auto label = new QLabel(
		"<a href=\"https://docs.emercoin.com/en/Blockchain_Services/EmerSSL/EmerSSL_Introduction.html\">EmerSSL</a> allows you to automatically login without passwords on many sites using certificate, stored in Emercoin blockchain.");
	label->setOpenExternalLinks(true);
	lay->addWidget(label);
	_view = new CertTableView(_logger);
	{
		auto lay2 = new QHBoxLayout;
		lay->addLayout(lay2);

		auto btnNew = new QPushButton(tr("New cerificate"));
		btnNew->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/file-32.png"));
		btnNew->setShortcut(QKeySequence("Ctrl+N"));
		connect(btnNew, &QAbstractButton::clicked, this, &ManageSslPage::onCreate);
		lay2->addWidget(btnNew);

		_btnDelete = new QPushButton(tr("Delete selected"));
		_btnDelete->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-cancel-32.png"));
		connect(_btnDelete, &QAbstractButton::clicked, this, &ManageSslPage::onDelete);
		lay2->addWidget(_btnDelete);

		_btnGenerate = new QPushButton(tr("Generate again"));
		_btnGenerate->setToolTip(tr("Regenerate certificate (for same nickname and email) if it has been expired or has been compromised"));
		_btnGenerate->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/refresh-24.png"));
		connect(_btnGenerate, &QAbstractButton::clicked, _view, &CertTableView::generateCertForSelectedRow);
		lay2->addWidget(_btnGenerate);

		_btnOpenFolder = new QPushButton(tr("Open folder"));
		_btnOpenFolder->setToolTip(tr("Reveal certificate file in folder"));
		_btnOpenFolder->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-open-32.png"));
		connect(_btnOpenFolder, &QAbstractButton::clicked, _view, &CertTableView::showInExplorer);
		lay2->addWidget(_btnOpenFolder);

		lay2->addStretch();
	}

	auto splitter = new QSplitter(Qt::Vertical);
	lay->addWidget(splitter);

	connect(_view->selectionModel(), &QItemSelectionModel::selectionChanged, this, &ManageSslPage::enableButtons);
	enableButtons();
	splitter->addWidget(_view);

	splitter->addWidget(_logger);
	OpenSslConfigWriter(_logger).checkAndWrite();
	QTimer::singleShot(1, &OpenSslExecutable::isFoundOrMessageBox);
}
void ManageSslPage::enableButtons() {
	bool selected = _view->selectionModel()->hasSelection();
	_btnDelete->setEnabled(selected);
	_btnGenerate->setEnabled(selected);
	_btnOpenFolder->setEnabled(selected);
}
struct ManageSslPage::TemplateDialog: public QDialog {
	QLineEdit* _name = new QLineEdit;
	EmailLineEdit* _email = new EmailLineEdit;
	QLineEdit* _ecard = new QLineEdit;
	QPushButton* _okBtn = 0;
	TemplateDialog(QWidget*parent): QDialog(parent) {
		setWindowTitle(tr("New certificate template"));
#if QT_VERSION > QT_VERSION_CHECK(5, 9, 0)
		setWindowFlag(Qt::WindowContextHelpButtonHint, false);
#endif
		auto lay = new QVBoxLayout(this);
		auto form = new QFormLayout;
		lay->addLayout(form);
		const QString strMandatoryField = tr("Mandatory field");
		_name->setPlaceholderText(strMandatoryField);
		form->addRow(tr("Name or nickname:"), _name);
		{
			auto lay = new QVBoxLayout;
			lay->addWidget(_email);
			_email->setPlaceholderText(strMandatoryField);

			QLabel* errorDesc = new QLabel;
			lay->addWidget(errorDesc);
			_email->validator()->setErrorLabel(errorDesc);
			errorDesc->hide();

			form->addRow(tr("E-mail:"), lay);
		}
		form->addRow(tr("Your UID to retrieve InfoCard info:"), _ecard);
		_ecard->setPlaceholderText(tr("Optional field"));

		auto box = new QDialogButtonBox;
		lay->addWidget(box);
		_okBtn = box->addButton(QDialogButtonBox::Ok);
		auto cancel = box->addButton(QDialogButtonBox::Cancel);
		_okBtn->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-apply-32.png"));
		cancel->setIcon(QIcon(":/qt-project.org/styles/commonstyle/images/standardbutton-cancel-32.png"));
		connect(_okBtn, &QAbstractButton::clicked, this, &QDialog::accept);
		connect(cancel, &QAbstractButton::clicked, this, &QDialog::reject);
		connect(_email, &QLineEdit::textChanged, this, &TemplateDialog::enableOk);
		connect(_name, &QLineEdit::textChanged, this, &TemplateDialog::enableOk);
		connect(_ecard, &QLineEdit::textChanged, this, &TemplateDialog::enableOk);
		lay->addStretch();
		_okBtn->setEnabled(false);
	}
	bool allValid()const {
		if(_name->text().trimmed().isEmpty())
			return false;
		if(_email->text().isEmpty())//first - simplified check to prevent detailed description
			return false;
		return _email->hasAcceptableInput();
	}
	void enableOk() {
		_okBtn->setEnabled(allValid());
	}
	virtual void accept()override {
		if(allValid())
			QDialog::accept();
	}
};
QString ManageSslPage::randName() {
	//rand key chosed to be 64-bit so EmerSSL can optimize hashes processing etc;
	//also in plain C 64bit integers are much easier to manipulate than strings, so int64 are used;
	//we can't use std::random_device because it's deterministic on MinGW https://sourceforge.net/p/mingw-w64/bugs/338/
	QByteArray uid = QUuid::createUuid().toByteArray();
        int x = 0;
        do {
            uid[0] = uid[0] + (++x); // to mitigate low-probable case, when h(x) == x
            uid = QCryptographicHash::hash(uid, QCryptographicHash::Sha256);
        } while(uid[0] < (char)0x10); // To preserve 0-prefix
        uid.truncate(8);
	return uid.toHex();
}
void ManageSslPage::onCreate() {
	TemplateDialog dlg(this);
	if(dlg.exec()!=QDialog::Accepted)
		return;
	const QString name = dlg._name->text().trimmed();
	const QString mail = dlg._email->text().trimmed();
	const QString ecard = dlg._ecard->text().trimmed();
	QString contents = QString("/CN=%1/emailAddress=%2")
		.arg(name).arg(mail);
	if(!ecard.isEmpty())
		contents += "/UID=" + ecard;
	contents += '\n';
	QString fileName = randName() + ".tpl";
	QDir dir = Settings::certDir();
	QString path = dir.absoluteFilePath(fileName);
	QString error;
	_logger->setFileNear(dir, fileName);
	if(!Shell(_logger).write(path, contents.toUtf8(), error))
		return;
	_view->model()->reload();
	int index = _view->model()->indexByFile(path);
	Q_ASSERT(index!=-1);
	if(-1==index)
		return;
	_view->selectRow(index);
	_view->setFocus();
	_view->generateCertForSelectedRow();
}
void ManageSslPage::onDelete() {
	auto rows = _view->selectionModel()->selectedRows();
	if(rows.isEmpty())
		return;
	_logger->clear();
	_view->model()->removeRows(rows);
}
QString ManageSslPage::name()const {
	int row = _view->selectedRow();
	if(-1==row)
		return {};
	const auto & item = _view->model()->_rows[row];
	QString sha;
	QString err = item.sha256FromCertificate(sha);
	if(!err.isEmpty())
		return {};
	return "ssl:" + item._baseName;
}
QString ManageSslPage::value()const {
	int row = _view->selectedRow();
	if(-1==row)
		return {};
	const auto & item = _view->model()->_rows[row];
	QString sha;
	QString err = item.sha256FromCertificate(sha);
	if(!err.isEmpty()) {
		QMessageBox::warning(0, tr("Certificate not ready"), err);
		return {};
	}
	return "sha256=" + sha;
}
