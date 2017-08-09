#include "nametablemodel.h"

#include "guiutil.h"
#include "walletmodel.h"
#include "guiconstants.h"
#include "../wallet.h"
#include "../namecoin.h"

#include <vector>

using namespace std;

// ExpiresIn column is right-aligned as it contains numbers
static int column_alignments[] = {
        Qt::AlignLeft|Qt::AlignVCenter,     // Name
        Qt::AlignLeft|Qt::AlignVCenter,     // Value
        Qt::AlignLeft|Qt::AlignVCenter,     // Address
        Qt::AlignRight|Qt::AlignVCenter     // Expires in
    };

struct NameTableEntryLessThan
{
    bool operator()(const NameTableEntry &a, const NameTableEntry &b) const
    {
        return a.name < b.name;
    }
    bool operator()(const NameTableEntry &a, const QString &b) const
    {
        return a.name < b;
    }
    bool operator()(const QString &a, const NameTableEntry &b) const
    {
        return a < b.name;
    }
};

// Private implementation
class NameTablePriv
{
public:
    CWallet *wallet;
    QList<NameTableEntry> cachedNameTable;
    NameTableModel *parent;

    NameTablePriv(CWallet *wallet, NameTableModel *parent):
        wallet(wallet), parent(parent) {}

    void refreshNameTable(bool fMyNames, bool fOtherNames, bool fExpired)
    {
        parent->beginResetModel();
        cachedNameTable.clear();

        CNameVal nameUniq;
        map<CNameVal, NameTxInfo> mapNames, mapPending;
        GetNameList(nameUniq, mapNames, mapPending);

        // add info about existing names
        BOOST_FOREACH(const PAIRTYPE(CNameVal, NameTxInfo)& item, mapNames)
        {
            // name is mine and user asked to hide my names
            if (item.second.fIsMine && !fMyNames)
                continue;
            // name is _not_ mine and user asked to hide other names
            if (!item.second.fIsMine && !fOtherNames)
                continue;
            // name have expired and users asked to hide expired names
            if (item.second.nExpiresAt - chainActive.Height() <= 0 && !fExpired)
                continue;

            NameTableEntry nte(stringFromNameVal(item.second.name), stringFromNameVal(item.second.value), item.second.strAddress, item.second.nExpiresAt, item.second.fIsMine);
            cachedNameTable.append(nte);
        }

        // add pending name operations
        BOOST_FOREACH(const PAIRTYPE(CNameVal, NameTxInfo)& item, mapPending)
        {
            // name is mine and user asked to hide my names
            if (item.second.fIsMine && !fMyNames)
                continue;
            // name is _not_ mine and user asked to hide other names
            if (!item.second.fIsMine && !fOtherNames)
                continue;

            int nHeightStatus = NameTableEntry::NAME_NON_EXISTING;
            if (item.second.op == OP_NAME_NEW)
                nHeightStatus = NameTableEntry::NAME_NEW;
            else if (item.second.op == OP_NAME_UPDATE)
                nHeightStatus = NameTableEntry::NAME_UPDATE;
            else if (item.second.op == OP_NAME_DELETE)
                nHeightStatus = NameTableEntry::NAME_DELETE;

            NameTableEntry nte(stringFromNameVal(item.second.name), stringFromNameVal(item.second.value), item.second.strAddress, nHeightStatus, item.second.fIsMine);
            cachedNameTable.append(nte);
        }

        // qLowerBound() and qUpperBound() require our cachedNameTable list to be sorted in asc order
        qSort(cachedNameTable.begin(), cachedNameTable.end(), NameTableEntryLessThan());
        parent->endResetModel();
    }

    void updateEntry(const NameTableEntry &nameObj, int status, int *outNewRowIndex = NULL)
    {
        updateEntry(nameObj.name, nameObj.value, nameObj.address, nameObj.nExpiresAt, status, outNewRowIndex);
    }

    void updateEntry(const QString &name, const QString &value, const QString &address, int nExpiresAt, int status, int *outNewRowIndex = NULL)
    {
        // Find name in model
        QList<NameTableEntry>::iterator lower = qLowerBound(
            cachedNameTable.begin(), cachedNameTable.end(), name, NameTableEntryLessThan());
        QList<NameTableEntry>::iterator upper = qUpperBound(
            cachedNameTable.begin(), cachedNameTable.end(), name, NameTableEntryLessThan());
        int lowerIndex = (lower - cachedNameTable.begin());
        int upperIndex = (upper - cachedNameTable.begin());
        bool inModel = (lower != upper);

        switch(status)
        {
        case CT_NEW:
            if (inModel)
            {
                if (outNewRowIndex)
                {
                    *outNewRowIndex = parent->index(lowerIndex, 0).row();
                    // HACK: ManageNamesPage uses this to ensure updating and get selected row,
                    // so we do not write warning into the log in this case
                }
                else
                    LogPrintf("Warning: NameTablePriv::updateEntry: Got CT_NEW, but entry is already in model\n");
                break;
            }
            parent->beginInsertRows(QModelIndex(), lowerIndex, lowerIndex);
            cachedNameTable.insert(lowerIndex, NameTableEntry(name, value, address, nExpiresAt));
            parent->endInsertRows();
            if (outNewRowIndex)
                *outNewRowIndex = parent->index(lowerIndex, 0).row();
            break;
        case CT_UPDATED:
            if (!inModel)
            {
                LogPrintf("Warning: NameTablePriv::updateEntry: Got CT_UPDATED, but entry is not in model\n");
                break;
            }
            lower->name = name;
            lower->value = value;
            lower->address = address;
            lower->nExpiresAt = nExpiresAt;
            parent->emitDataChanged(lowerIndex);
            break;
        case CT_DELETED:
            if (!inModel)
            {
                LogPrintf("Warning: NameTablePriv::updateEntry: Got CT_DELETED, but entry is not in model\n");
                break;
            }
            parent->beginRemoveRows(QModelIndex(), lowerIndex, upperIndex-1);
            cachedNameTable.erase(lower, upper);
            parent->endRemoveRows();
            break;
        }
    }

    int size()
    {
        return cachedNameTable.size();
    }

    NameTableEntry *index(int idx)
    {
        if (idx >= 0 && idx < cachedNameTable.size())
        {
            return &cachedNameTable[idx];
        }
        else
        {
            return NULL;
        }
    }
};


NameTableModel::NameTableModel(CWallet *wallet, WalletModel *parent) :
    QAbstractTableModel(parent), walletModel(parent), wallet(wallet), priv(0), cachedNumBlocks(0)
{
    columns << tr("Name") << tr("Value") << tr("Address") << tr("Expires in");
    priv = new NameTablePriv(wallet, this);

    fMyNames = true;
    fOtherNames = false;
    fExpired = false;
    priv->refreshNameTable(fMyNames, fOtherNames, fExpired);
}

NameTableModel::~NameTableModel()
{
    delete priv;
}

void NameTableModel::update(bool forced)
{
    // just do a complete table refresh, for simplicity sake
    // TODO: redo this to allow increment updates, just like in TransactionTableModel::updateTransaction
    priv->refreshNameTable(fMyNames, fOtherNames, fExpired);
}

int NameTableModel::rowCount(const QModelIndex &parent /* = QModelIndex()*/) const
{
    Q_UNUSED(parent);
    return priv->size();
}

int NameTableModel::columnCount(const QModelIndex &parent /* = QModelIndex()*/) const
{
    Q_UNUSED(parent);
    return columns.length();
}

QVariant NameTableModel::data(const QModelIndex &index, int role) const
{
    if (!index.isValid())
        return QVariant();

    NameTableEntry *rec = static_cast<NameTableEntry*>(index.internalPointer());

    switch (role)
    {
    case Qt::DisplayRole:
    case Qt::EditRole:
        switch (index.column())
        {
        case Name:
            return rec->name;
        case Value:
            return rec->value;
        case Address:
            return rec->address;
        case ExpiresIn:
            if (!rec->HeightValid())
            {
                if (rec->nExpiresAt == NameTableEntry::NAME_NEW)
                    return QString("pending (new)");
                if (rec->nExpiresAt == NameTableEntry::NAME_UPDATE)
                    return QString("pending (update)");
                if (rec->nExpiresAt == NameTableEntry::NAME_DELETE)
                    return QString("pending (delete)");
            }
            else
            {
                float days = (rec->nExpiresAt - chainActive.Height()) / 175.0;  // 175 - number of blocks per day on average
                return days < 0 ? QString("%1 hours").arg(days * 24, 0, 'f', 1) : QString("%1 days").arg(days, 0, 'f', 1);
            }
        }
        break;
    case Qt::TextAlignmentRole: return column_alignments[index.column()];
    case Qt::FontRole: {
        QFont font;
        if (index.column() == Address)
            font = GUIUtil::bitcoinAddressFont();
        return font;
    }
    case Qt::BackgroundRole:
        if (index.column() == ExpiresIn && rec->nExpiresAt - chainActive.Height() <= 0)
            return QVariant(QColor(Qt::yellow));
        else if (index.column() != ExpiresIn && !rec->fIsMine)
            return QVariant(QColor(255,70,70));
        break;
    }

    return QVariant();
}

QVariant NameTableModel::headerData(int section, Qt::Orientation orientation, int role) const
{
    if (orientation == Qt::Horizontal)
    {
        if (role == Qt::DisplayRole)
        {
            return columns[section];
        }
        else if (role == Qt::TextAlignmentRole)
        {
            return column_alignments[section];
        }
        else if (role == Qt::ToolTipRole)
        {
            switch (section)
            {
            case Name:
                return tr("Name registered using iTecoCoin.");
            case Value:
                return tr("Data associated with the name.");
            case Address:
                return tr("iTecoCoin address to which the name is registered.");
            case ExpiresIn:
                return tr("Number of blocks, after which the name will expire. Update name to renew it.");
            }
        }
    }
    return QVariant();
}

Qt::ItemFlags NameTableModel::flags(const QModelIndex &index) const
{
    if (!index.isValid())
        return 0;
    //NameTableEntry *rec = static_cast<NameTableEntry*>(index.internalPointer());

    return Qt::ItemIsSelectable | Qt::ItemIsEnabled;
}

QModelIndex NameTableModel::index(int row, int column, const QModelIndex &parent /* = QModelIndex()*/) const
{
    Q_UNUSED(parent);
    NameTableEntry *data = priv->index(row);
    if (data)
    {
        return createIndex(row, column, priv->index(row));
    }
    else
    {
        return QModelIndex();
    }
}

void NameTableModel::updateEntry(const QString &name, const QString &value, const QString &address, int nHeight, int status, int *outNewRowIndex /* = NULL*/)
{
    priv->updateEntry(name, value, address, nHeight, status, outNewRowIndex);
}

void NameTableModel::emitDataChanged(int idx)
{
    emit dataChanged(index(idx, 0), index(idx, columns.length()-1));
}
