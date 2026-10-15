//RegisterUniversityWidget.h by Emercoin developers
#pragma once
#include <qt/NameValueLineEdits.h>

#include <QPlainTextEdit>

class QFormLayout;
class WalletModel;

class RegisterUniversityWidget: public QWidget {
	public:
        RegisterUniversityWidget(WalletModel* model);

		NameValueLineEdits* _NVPair = 0;
    protected:
		QLineEdit* _editName = 0;
		QPlainTextEdit* _editOther = 0;
		QList<QLineEdit*> _edits;
		void recalcValue();
		QLineEdit* addLineEdit(QFormLayout*form, const QString& name, const QString& text, const QString& tooltip, bool readOnly = false);
    private:
        WalletModel* model;
};
