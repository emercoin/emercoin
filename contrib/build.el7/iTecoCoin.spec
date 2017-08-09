Name:           emercoin
Version:        0.6.2.1
Release:        1%{dist}
Summary:        Emercoin Wallet
Group:          Applications/Internet
Vendor:         Emercoin
License:        GPLv3
URL:            http://www.emercoin.com
Source0:        %{name}.tar.gz
BuildRoot:      %(mktemp -ud %{_tmppath}/%{name}-%{version}-%{release}-XXXXXX)
BuildRequires:  autoconf automake libtool gcc-c++ openssl-devel >= 1:1.0.2d libdb4-devel libdb4-cxx-devel miniupnpc-devel boost-devel boost-static
Requires:       openssl >= 1:1.0.2d libdb4 libdb4-cxx miniupnpc logrotate

%description
Emercoin Wallet

%prep
%setup -q -n emercoin

%build
./autogen.sh
./configure
make

%install
%{__rm} -rf $RPM_BUILD_ROOT
%{__mkdir} -p $RPM_BUILD_ROOT%{_bindir} $RPM_BUILD_ROOT/etc/emercoin $RPM_BUILD_ROOT/etc/ssl/emc $RPM_BUILD_ROOT/var/lib/emc/.emercoin $RPM_BUILD_ROOT/usr/lib/systemd/system $RPM_BUILD_ROOT/etc/logrotate.d
%{__mv} -f bin/emc $RPM_BUILD_ROOT%{_bindir}
%{__install} -m 755 src/emercoind $RPM_BUILD_ROOT%{_bindir}
%{__install} -m 755 src/emercoin-cli $RPM_BUILD_ROOT%{_bindir}
%{__install} -m 600 contrib/build.el7/emercoin.conf $RPM_BUILD_ROOT/var/lib/emc/.emercoin
%{__install} -m 644 contrib/build.el7/emercoind.service $RPM_BUILD_ROOT/usr/lib/systemd/system
%{__install} -m 644 contrib/build.el7/emercoind.logrotate $RPM_BUILD_ROOT/etc/logrotate.d/emercoind

%clean
%{__rm} -rf $RPM_BUILD_ROOT

%pretrans
getent passwd emc >/dev/null && { [ -f /usr/bin/emercoind ] || { echo "Looks like user 'emc' already exists and have to be deleted before continue."; exit 1; }; } || useradd -r -M -d /var/lib/emc -s /bin/false emc

%post
[ $1 == 1 ] && {
  sed -i -e "s/\(^rpcpassword=MySuperPassword\)\(.*\)/rpcpassword=$(cat /dev/urandom | tr -dc 'a-zA-Z0-9' | fold -w 32 | head -n 1)/" /var/lib/emc/.emercoin/emercoin.conf
  openssl req -nodes -x509 -newkey rsa:4096 -keyout /etc/ssl/emc/emercoin.key -out /etc/ssl/emc/emercoin.crt -days 3560 -subj /C=US/ST=Oregon/L=Portland/O=IT/CN=emercoin.emc
  ln -sf /var/lib/emc/.emercoin/emercoin.conf /etc/emercoin/emercoin.conf
  ln -sf /etc/ssl/emc /etc/emercoin/certs
  chown emc.emc /etc/ssl/emc/emercoin.key /etc/ssl/emc/emercoin.crt
  chmod 600 /etc/ssl/emc/emercoin.key
} || exit 0

%posttrans
[ -f /var/lib/emc/.emercoin/addr.dat ] && { cd /var/lib/emc/.emercoin && rm -rf database addr.dat nameindex* blk* *.log .lock; }
sed -i -e 's|rpcallowip=\*|rpcallowip=0.0.0.0/0|' /var/lib/emc/.emercoin/emercoin.conf
systemctl daemon-reload
systemctl status emercoind >/dev/null && systemctl restart emercoind || exit 0

%preun
[ $1 == 0 ] && {
  systemctl is-enabled emercoind >/dev/null && systemctl disable emercoind >/dev/null || true
  systemctl status emercoind >/dev/null && systemctl stop emercoind >/dev/null || true
  pkill -9 -u emc > /dev/null 2>&1
  getent passwd emc >/dev/null && userdel emc >/dev/null 2>&1 || true
  rm -f /etc/ssl/emc/emercoin.key /etc/ssl/emc/emercoin.crt /etc/emercoin/emercoin.conf /etc/emercoin/certs
} || exit 0

%files
%doc COPYING
%attr(750,emc,emc) %dir /etc/emercoin
%attr(750,emc,emc) %dir /etc/ssl/emc
%attr(700,emc,emc) %dir /var/lib/emc
%attr(700,emc,emc) %dir /var/lib/emc/.emercoin
%attr(600,emc,emc) %config(noreplace) /var/lib/emc/.emercoin/emercoin.conf
%attr(4750,emc,emc) %{_bindir}/emercoin-cli
%defattr(-,root,root)
%config(noreplace) /etc/logrotate.d/emercoind
%{_bindir}/emercoind
%{_bindir}/emc
/usr/lib/systemd/system/emercoind.service

%changelog
* Tue Jun 21 2016 Sergii Vakula <sv@emercoin.com> 0.3.7
- No changelog available here. Please refer to https://github.com/emercoin/emercoin/releases
