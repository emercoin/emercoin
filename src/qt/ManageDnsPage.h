//ManageDnsPage.h by emercoin developers
#pragma once
#include <QDialog>
#include <QLineEdit>
class QLineEdit;
class QFormLayout;
class QString;

class ManageDnsPage: public QDialog {
    Q_OBJECT
    public:
	    ManageDnsPage(QWidget*parent);

        QLineEdit* _editName = 0;
        struct LineEdit: public QLineEdit {
            QString _dnsRecord;
        };
        QList<LineEdit*> _edits;

        QLineEdit* _resultingName = 0;
        QLineEdit* _resultingValue = 0;
    Q_SIGNALS:
        void previewName(const QString & s);
        void previewValue(const QString & s);
    protected:
        void recalcValue();
        LineEdit* addLineEdit(QFormLayout*form, QString dnsParam, QString text, QString tooltipq);
};
