//NameValueLineEdits.h by Emercoin developers
#pragma once
#include "SelectableLineEdit.h"
class SelectableTextEdit;

//Displays NVS (Name-value storage) name and value in line edits, allows to copy them easily.
class NameValueLineEdits: public QWidget {
	public:
		NameValueLineEdits();
		void setName(const QString & s);
		void setValue(const QString & s);
		void setValuePlaceholder(const QString & s);
		void setValueMultiline(bool b);
		void setValueReadOnly(bool b);
		QString name()const;
		QString value()const;
	protected:
		SelectableLineEdit* _resultingName = 0;
		bool _multiline = false;
		QWidget* _w1Line = 0;
		QWidget* _wMultiLine = 0;
        SelectableLineEdit* _resultingValue = 0;
		SelectableTextEdit* _resultingMultiline = 0;

		void copyValue();
};
