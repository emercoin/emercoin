﻿//ManageDnsPage.h by emercoin developers
#pragma once
#include <QDialog>
class QLineEdit;
class QFormLayout;
class QString;

class ManageDnsPage: public QDialog {
    Q_OBJECT
    public:
	    ManageDnsPage(QWidget*parent);

        QLineEdit* _editName = 0;
        QLineEdit* _editA = 0;
        QLineEdit* _editAAAA = 0;
        QLineEdit* _editMx = 0;
        QLineEdit* _resultingName = 0;
        QLineEdit* _resultingValue = 0;
    Q_SIGNALS:
        void previewName(const QString & s);
        void previewValue(const QString & s);
    protected:
        void recalcValue();
        void addHtmlRow(QFormLayout*form, QString text, QLineEdit*w, QString tooltip);
};
