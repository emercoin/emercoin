#pragma once
#include <QDialog>
#include <QSortFilterProxyModel>

namespace Ui {
    class ManageNamesPage;
}
class WalletModel;
class NameTableModel;

QT_BEGIN_NAMESPACE
class QMenu;
class QModelIndex;
QT_END_NAMESPACE

class NameFilterProxyModel : public QSortFilterProxyModel
{
    Q_OBJECT

public:
    explicit NameFilterProxyModel(QObject *parent = 0);

    void setNameSearch(const QString &search);
    void setValueSearch(const QString &search);
    void setAddressSearch(const QString &search);

protected:
    bool filterAcceptsRow(int sourceRow, const QModelIndex &sourceParent) const;
    bool lessThan(const QModelIndex &left, const QModelIndex &right) const;

private:
    QString nameSearch, valueSearch, addressSearch;
};

/** Page for managing names */
class ManageNamesPage : public QWidget
{
    Q_OBJECT

public:
    explicit ManageNamesPage(QWidget *parent = 0);
    ~ManageNamesPage();

    void setModel(WalletModel *walletModel);
    std::vector<unsigned char> importedAsBinaryFile;
    QString               importedAsTextFile;
    void setDisplayedName(const QString & n);
    void setDisplayedValue(const QString & v);
private:
    Ui::ManageNamesPage *ui;
    NameTableModel *model;
    WalletModel *walletModel;
    NameFilterProxyModel *proxyModel;
    QMenu *contextMenu;

public Q_SLOTS:
    void exportClicked();

    void changedNameFilter(const QString &filter);
    void changedValueFilter(const QString &filter);
    void changedAddressFilter(const QString &filter);

private Q_SLOTS:
    void on_submitNameButton_clicked();
	void showNameAvailable();
    bool eventFilter(QObject *object, QEvent *event);
    void selectionChanged();

    /** Spawn contextual menu (right mouse menu) for name table entry */
    void contextualMenu(const QPoint &point);

    void onCopyNameAction();
    void onCopyValueAction();
    void onCopyAddressAction();
    void onCopyAllAction();
    void onSaveValueAsBinaryAction();

    void on_txTimeTypeSelector_currentIndexChanged(int index);
    void on_txTypeSelector_currentIndexChanged(const QString &txType);
    void on_cbMyNames_stateChanged(int arg1);
    void on_cbOtherNames_stateChanged(int arg1);
    void on_cbExpired_stateChanged(int arg1);
    void on_importValueButton_clicked();
    void on_registerValue_textChanged();
    void onManageDomainsClicked();
	void onManageDpoClicked();
	void onTrustedDiplomaClicked();
	void onSslClicked();
	void onInfoCardClicked();
    void on_registerAddress_editingFinished();

Q_SIGNALS:
    void doubleClicked(const QModelIndex&);
};
