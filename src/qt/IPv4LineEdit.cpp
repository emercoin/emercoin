//IPv4LineEdit.cpp by emercoin developers
#include "IPv4LineEdit.h"

IPv4LineEdit::Validator::Validator(QObject*parent): QRegExpValidator(parent) {
	const QString ipPart = "(?:[0-1]?[0-9]?[0-9]|2[0-4][0-9]|25[0-5])";
	const QRegExp ipRegex("^" + ipPart
		+ "\\." + ipPart
		+ "\\." + ipPart
		+ "\\." + ipPart + "$");
	setRegExp(ipRegex);
}
IPv4LineEdit::IPv4LineEdit() {
	QRegExpValidator *ipValidator = new Validator(this);
	setValidator(ipValidator);
}
