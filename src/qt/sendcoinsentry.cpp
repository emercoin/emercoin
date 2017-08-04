// Copyright (c) 2011-2013 The Bitcoin developers
// Distributed under the GPL3 software license, see the accompanying
// file COPYING or http://www.gnu.org/licenses/gpl.html.

#include "sendcoinsentry.h"
#include "ui_sendcoinsentry.h"

#include "addressbookpage.h"
#include "addresstablemodel.h"
#include "guiutil.h"
#include "optionsmodel.h"
#include "walletmodel.h"
#include "../namecoin.h"
#include "bitcoinunits.h"
#include <QStandardItemModel>

#include <QApplication>
#include <QClipboard>

SendCoinsEntry::SendCoinsEntry(QWidget *parent) :
    QStackedWidget(parent),
    ui(new Ui::SendCoinsEntry),
    model(0)
{
    ui->setupUi(this);

    setCurrentWidget(ui->SendCoins);

#ifdef Q_OS_MAC
    ui->payToLayout->setSpacing(4);
#endif
#if QT_VERSION >= 0x040700
    ui->addAsLabel->setPlaceholderText(tr("Enter a label for this address to add it to your address book"));
#endif

    // normal bitcoin address field
    GUIUtil::setupAddressWidget(ui->payTo, this);
    // just a label for displaying bitcoin address(es)
    ui->payTo_is->setFont(GUIUtil::bitcoinAddressFont());

    // Connect signals
    connect(ui->payAmount, SIGNAL(valueChanged()), this, SIGNAL(payAmountChanged()));
    connect(ui->deleteButton, SIGNAL(clicked()), this, SLOT(deleteClicked()));
    connect(ui->deleteButton_is, SIGNAL(clicked()), this, SLOT(deleteClicked()));
    connect(ui->deleteButton_s, SIGNAL(clicked()), this, SLOT(deleteClicked()));

    ui->payTo->setValidator(0);  // iTecoCoin: disable validator so that we can type names
    ui->payAmountExch->setValidator( new QDoubleValidator(0, 1e20, 8, this) );
    qsExchInfo = "<html><head/><body><p><span style=\" font-weight:600;\">"+
            tr("WARNING: You're using external service! iTecoCoin is not responsible for functionality and correct behavior of this service.")+"</span><br/>"+
            tr("Usage: Enter amount, currency type and address. Press Request Payment and select desired exchange service.")+"<br/>"+
            tr("After creating transaction you can view details by double clicking that transaction in transaction list tab.")+"</p></body></html>";
    ui->infoExchLabel->setText(qsExchInfo);
    ui->exchWidget->setVisible(false);
}

SendCoinsEntry::~SendCoinsEntry()
{
    delete ui;
}

void SendCoinsEntry::on_pasteButton_clicked()
{
    // Paste text from clipboard into recipient field
    ui->payTo->setText(QApplication::clipboard()->text());
}

void SendCoinsEntry::on_addressBookButton_clicked()
{
    if(!model)
        return;
    AddressBookPage dlg(AddressBookPage::ForSelection, AddressBookPage::SendingTab, this);
    dlg.setModel(model->getAddressTableModel());
    if(dlg.exec())
    {
        ui->payTo->setText(dlg.getReturnValue());
        ui->payAmount->setFocus();
    }
}

void SendCoinsEntry::on_payTo_textChanged(const QString &address)
{
    updateLabel(address);
}

void SendCoinsEntry::setModel(WalletModel *model)
{
    this->model = model;

    if (model && model->getOptionsModel())
        connect(model->getOptionsModel(), SIGNAL(displayUnitChanged(int)), this, SLOT(updateDisplayUnit()));

    clear();

    // iTecoCoin: initialize exchange box
    // initialize with refund address:
    std::string sAddress;
    if (this->model)
    {
        if (this->model->getAddressForChange(sAddress))
            this->eBox.Reset(sAddress);
        else
        {
            ui->checkBoxExch->setDisabled(true);
            ui->exchWidget->setVisible(false);
            ui->exchWidget->setDisabled(true);
        }
    }
}

void SendCoinsEntry::clear()
{
    // clear UI elements for normal payment
    ui->payTo->clear();
    ui->addAsLabel->clear();
    ui->payAmount->clear();
    ui->messageTextLabel->clear();
    ui->messageTextLabel->hide();
    ui->messageLabel->hide();
    // clear UI elements for insecure payment request
    ui->payTo_is->clear();
    ui->memoTextLabel_is->clear();
    ui->payAmount_is->clear();
    // clear UI elements for secure payment request
    ui->payTo_s->clear();
    ui->memoTextLabel_s->clear();
    ui->payAmount_s->clear();

    // update the display unit, to not use the default ("BTC")
    updateDisplayUnit();
}

void SendCoinsEntry::deleteClicked()
{
    emit removeEntry(this);
}

bool SendCoinsEntry::validate()
{
    if (!model)
        return false;

    // Check input validity
    bool retval = true;

    // Skip checks for payment request
    if (recipient.paymentRequest.IsInitialized())
        return retval;

    if (!model->validateAddress(ui->payTo->text()))
    {
        ui->payTo->setValid(false);
        retval = false;
    }

    if (!ui->payAmount->validate())
    {
        retval = false;
    }

    // Sending a zero amount is invalid
    if (ui->payAmount->value(0) <= 0)
    {
        ui->payAmount->setValid(false);
        retval = false;
    }

    // Reject dust outputs:
    if (retval && GUIUtil::isDust(ui->payTo->text(), ui->payAmount->value())) {
        ui->payAmount->setValid(false);
        retval = false;
    }

    return retval;
}

SendCoinsRecipient SendCoinsEntry::getValue()
{
    // Payment request
    if (recipient.paymentRequest.IsInitialized())
        return recipient;

    // Normal payment
    recipient.address = ui->payTo->text();
    recipient.label = ui->addAsLabel->text();
    recipient.amount = ui->payAmount->value();
    recipient.message = ui->messageTextLabel->text();
    recipient.comment = this->comment;
    recipient.commentto = this->commentto;

    return recipient;
}

QWidget *SendCoinsEntry::setupTabChain(QWidget *prev)
{
    QWidget::setTabOrder(prev, ui->payTo);
    QWidget::setTabOrder(ui->payTo, ui->addAsLabel);
    QWidget *w = ui->payAmount->setupTabChain(ui->addAsLabel);
    QWidget::setTabOrder(w, ui->addressBookButton);
    QWidget::setTabOrder(ui->addressBookButton, ui->pasteButton);
    QWidget::setTabOrder(ui->pasteButton, ui->deleteButton);
    return ui->deleteButton;
}

void SendCoinsEntry::setValue(const SendCoinsRecipient &value)
{
    recipient = value;

    if (recipient.paymentRequest.IsInitialized()) // payment request
    {
        if (recipient.authenticatedMerchant.isEmpty()) // insecure
        {
            ui->payTo_is->setText(recipient.address);
            ui->memoTextLabel_is->setText(recipient.message);
            ui->payAmount_is->setValue(recipient.amount);
            ui->payAmount_is->setReadOnly(true);
            setCurrentWidget(ui->SendCoins_InsecurePaymentRequest);
        }
        else // secure
        {
            ui->payTo_s->setText(recipient.authenticatedMerchant);
            ui->memoTextLabel_s->setText(recipient.message);
            ui->payAmount_s->setValue(recipient.amount);
            ui->payAmount_s->setReadOnly(true);
            setCurrentWidget(ui->SendCoins_SecurePaymentRequest);
        }
    }
    else // normal payment
    {
        // message
        ui->messageTextLabel->setText(recipient.message);
        ui->messageTextLabel->setVisible(!recipient.message.isEmpty());
        ui->messageLabel->setVisible(!recipient.message.isEmpty());

        ui->addAsLabel->clear();
        ui->payTo->setText(recipient.address); // this may set a label from addressbook
        if (!recipient.label.isEmpty()) // if a label had been set from the addressbook, dont overwrite with an empty label
            ui->addAsLabel->setText(recipient.label);
        ui->payAmount->setValue(recipient.amount);
    }
}

void SendCoinsEntry::setAddress(const QString &address)
{
    ui->payTo->setText(address);
    ui->payAmount->setFocus();
}

bool SendCoinsEntry::isClear()
{
    return ui->payTo->text().isEmpty() && ui->payTo_is->text().isEmpty() && ui->payTo_s->text().isEmpty();
}

void SendCoinsEntry::setFocus()
{
    ui->payTo->setFocus();
}

void SendCoinsEntry::updateDisplayUnit()
{
    if(model && model->getOptionsModel())
    {
        // Update payAmount with the current unit
        ui->payAmount->setDisplayUnit(model->getOptionsModel()->getDisplayUnit());
        ui->payAmount_is->setDisplayUnit(model->getOptionsModel()->getDisplayUnit());
        ui->payAmount_s->setDisplayUnit(model->getOptionsModel()->getDisplayUnit());
    }
}

bool SendCoinsEntry::updateLabel(const QString &address)
{
    if(!model)
        return false;

    // Fill in label from address book, if address has an associated label
    QString associatedLabel = model->getAddressTableModel()->labelForAddress(address);
    if(!associatedLabel.isEmpty())
    {
        ui->addAsLabel->setText(associatedLabel);
        return true;
    }

    return false;
}

void SendCoinsEntry::on_payTo_editingFinished()
{
    QString name = ui->payTo->text();
    if (name.isEmpty())
        return;

    std::string strName = name.toStdString();
    std::vector<unsigned char> vchName(strName.begin(), strName.end());

    std::string error;
    CBitcoinAddress address;
    if (!GetNameCurrentAddress(vchName, address, error))
        return;

    QString qstrAddress = QString::fromStdString(address.ToString());

    if (QMessageBox::Yes != QMessageBox::question(this, tr("Confirm name as address"),
            tr("This name exist and still active. Do you wish to use address of its current owner - %1?").arg(qstrAddress),
            QMessageBox::Yes | QMessageBox::Cancel, QMessageBox::Cancel))
        return;
    else
        ui->payTo->setText(qstrAddress);
}

void SendCoinsEntry::on_checkBoxExch_toggled(bool checked)
{
    this->comment = "";
    this->commentto = "";
    ui->exchWidget->setVisible(checked);
}

void SendCoinsEntry::on_requestPaymentButton_clicked()
{
    this->comment = "";
    this->commentto = "";

    if (eBox.m_v_exch.empty())
        return;

    double dPay = 0;
    bool ok = false;
    dPay = ui->payAmountExch->text().toDouble(&ok);
    if (!ok)
    {
        QMessageBox::warning(this, tr("Incorrect pay amount."), tr("Please enter valid positive number as pay amount."));
        return;
    }

    if (ui->payTypeExch->text().isEmpty())
    {
        QMessageBox::warning(this, tr("Empty currency name."), tr("Please enter currency short name (like BTC)."));
        return;
    }

    if (ui->payToExch->text().isEmpty())
    {
        QMessageBox::warning(this, tr("Empty address."), tr("Please enter valid %1 address.").arg(ui->payTypeExch->text().toLower()));
        return;
    }

    // loop over exchanges to populate combobox
    multimap<double, pair<Exch *, bool> > mapExch;   // double: emc per 1 btc
    bool validExist = false;
    foreach (Exch* exch, eBox.m_v_exch)
    {
        string err(exch->MarketInfo(ui->payTypeExch->text().toStdString()));
        if (!err.empty())
            continue;

        bool valid = exch->m_min <= dPay && exch->m_limit >= dPay;
        if (valid)
            validExist = true;

        mapExch.insert(pair<double, pair<Exch *, bool> >(exch->EstimatedEMC(dPay), pair<Exch *, bool>(exch, valid)));
    }

    ui->exchComboBox->clear();
    if (validExist)
        ui->exchComboBox->addItem(tr("Select exchange here:"));
    else
        ui->exchComboBox->addItem(tr("No exchange can make your request: try different currency/amount/address."));

    // http://stackoverflow.com/a/21740341/1199550
    foreach (const PAIRTYPE(double, PAIRTYPE(Exch *, bool)) &p, mapExch)
    {
        QString qsEntry;
        bool valid = p.second.second;
        if (valid)
            qsEntry = QString::number(p.first)+"emc ["+QString::fromStdString(p.second.first->Name())+"]";
        else
            qsEntry = tr("%1 out of bounds: min=%2, max=%3 [%4]").arg(ui->payTypeExch->text()).arg(p.second.first->m_min).arg(p.second.first->m_limit).arg(QString::fromStdString(p.second.first->Name()));
        ui->exchComboBox->addItem(qsEntry, qVariantFromValue((void *) p.second.first));

        // disable added item if not valid
        if (!valid)
        {
            const QStandardItemModel* imodel = qobject_cast<const QStandardItemModel*>(ui->exchComboBox->model());
            QStandardItem* item = imodel->item(imodel->rowCount()-1);

            item->setFlags(item->flags() & ~(Qt::ItemIsSelectable|Qt::ItemIsEnabled));
            // visually disable by greying out - works only if combobox has been painted already and palette returns the wanted color
            item->setData(ui->exchComboBox->palette().color(QPalette::Disabled, QPalette::Text), Qt::TextColorRole);
        }
    }
}

void SendCoinsEntry::on_payAmountExch_editingFinished()
{
    CAmount val;
    BitcoinUnits::parse(BitcoinUnits::BTC, ui->payAmountExch->text(), &val);
    ui->payAmountExch->setText(BitcoinUnits::format(BitcoinUnits::BTC, val, false, BitcoinUnits::separatorAlways));
}

#include "sendcoinsdialog.h"

void SendCoinsEntry::on_exchComboBox_currentIndexChanged(int index)
{
    this->comment = "";
    this->commentto = "";

    if (index <= 0)
        return;

    double dPay = 0;
    bool ok = false;
    dPay = ui->payAmountExch->text().toDouble(&ok);
    if (!ok)
    {
        QMessageBox::warning(this, tr("Incorrect pay amount."), tr("Please enter valid positive number as pay amount."));
        return;
    }

    QVariant data = ui->exchComboBox->itemData(index);
    Exch *exch = (Exch *) data.value<void *>();
    QString qsHost = QString::fromStdString(exch->Name());

    // remove previous request and clear info label
    exch->Cancel("");
    ui->infoExchLabel->setText(qsExchInfo);

    string err = exch->Send(ui->payToExch->text().toStdString(), dPay);
    if (!err.empty())
    {
        ui->infoExchLabel->setText(tr("Error: Send request to %1 failed:\n%2").arg(qsHost, QString::fromStdString(err)));
        return;
    }
    LogPrintf("Exchange.Send() : m_depAddr=%s, m_outAddr=%s m_depAmo=%lf m_outAmo=%lf m_txKey=%s\n",
        exch->m_depAddr, exch->m_outAddr, exch->m_depAmo, exch->m_outAmo, exch->m_txKey);

    if (exch->m_outAddr != ui->payToExch->text().toStdString())
    {
        ui->infoExchLabel->setText(tr("Error: Send request to %1 failed:\nAddress returned from exchange does not match requested address").arg(qsHost));
        exch->Cancel(exch->m_txKey);
        return;
    }

    int ttl = exch->Remain(exch->m_txKey);
    if (ttl <= 0)
    {
        ui->infoExchLabel->setText(tr("Error: payment time is expired for %1").arg(qsHost));
        return;
    }

    QMessageBox msgBox;
    msgBox.setStyleSheet("QLabel{min-width: 650px;}");
    msgBox.setWindowTitle(tr("Payment confirmation."));
    msgBox.setText(tr("%1 will send %2%3 to %4\n").arg(qsHost, QString::number(exch->m_outAmo), ui->payTypeExch->text().toLower(), QString::fromStdString(exch->m_outAddr))+
                   tr("You will need to send %1emc to %2\n").arg(QString::number(exch->m_depAmo), QString::fromStdString(exch->m_depAddr))+
                   tr("Payment id: %1\n").arg(QString::fromStdString(exch->m_txKey))+
                   tr("Time to complete: %1 minutes").arg(ttl/60));
    QAbstractButton* pButtonSend = msgBox.addButton(tr("Send Now"), QMessageBox::YesRole);
    QAbstractButton* pButtonCopy = msgBox.addButton(tr("Copy to GUI"), QMessageBox::YesRole);
    QAbstractButton* pButtonCancel = msgBox.addButton(tr("Cancel"), QMessageBox::RejectRole);
    msgBox.exec();

    if (msgBox.clickedButton() == pButtonSend || msgBox.clickedButton() == pButtonCopy)
    {
        ui->payTo->setText(QString::fromStdString(exch->m_depAddr));
        ui->payAmount->setDisplayUnit(BitcoinUnits::BTC);
        ui->payAmount->setString(QString::number(exch->m_depAmo));
        this->comment = exch->m_txKey;
        this->commentto = exch->Name();
        ui->infoExchLabel->setText(tr("Payment id: %1, Time to complete: %2 minutes").arg(QString::fromStdString(exch->m_txKey), QString::number(ttl/60)));
        if (msgBox.clickedButton() == pButtonSend)
            emit sendNow();
    }
    else if (msgBox.clickedButton() == pButtonCancel)
    {
        exch->Cancel(exch->m_txKey);
    }
}
