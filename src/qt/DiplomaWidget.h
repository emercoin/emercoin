//DiplomaWidget.h by Emercoin developers
#pragma once
#include <QTabWidget>
#include <QDialog>

class RegisterUniversityWidget;
class RegisterDiplomaWidget;
class WalletModel;

class DiplomaWidget: public QDialog {
	public:
        DiplomaWidget(WalletModel* model, QWidget*parent = nullptr);
		~DiplomaWidget();
		QString name()const;
		QString value()const;
	protected:
		QTabWidget* _tab = nullptr;
		RegisterUniversityWidget* _RegisterUniversityWidget = nullptr;
		RegisterDiplomaWidget* _RegisterDiplomaWidget = nullptr;
    private:
        WalletModel* model;
};
