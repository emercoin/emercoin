build_linux_SHA256SUM = sha256sum
build_linux_DOWNLOAD = curl --location --fail --connect-timeout $(DOWNLOAD_CONNECT_TIMEOUT) --speed-limit 1024 --speed-time $(DOWNLOAD_STALL_TIMEOUT) --retry $(DOWNLOAD_RETRIES) -o
