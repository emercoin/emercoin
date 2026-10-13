## Continuous integration

`.github/workflows/ci.yml` builds and tests every push and pull request to `develop` and
`master` on GitHub Actions. Each step is a stage of `ci/build.sh`, run in the image built from
`ci/Dockerfile` (Ubuntu 18.04 + gcc 8, the toolchain of the release builds), so a CI run can be
repeated locally with Docker:

    docker build -t emercoin-ci:bionic ci
    ci/docker.sh depends      # depends/ without Qt; slow the first time
    ci/docker.sh build        # emercoind, emercoin-cli, emercoin-tx, emercoin-wallet, unit tests
    ci/docker.sh check        # unit tests
    ci/docker.sh functional   # functional tests, without network access

Release packages, built the way `contrib/gitian-descriptors` builds releases (flags, security
and symbol checks, layout), headless for now:

    HOST=x86_64-linux-gnu  ci/docker.sh depends && HOST=x86_64-linux-gnu  ci/docker.sh package
    HOST=aarch64-linux-gnu ci/docker.sh depends && HOST=aarch64-linux-gnu ci/docker.sh package
    HOST=x86_64-w64-mingw32 ci/docker.sh depends && HOST=x86_64-w64-mingw32 ci/docker.sh package

The archive lands in `dist/` (`DISTNAME` sets its name). CI builds all three for every push and
pull request; after a push to `develop` whose tests pass, they replace the `nightly`
pre-release on GitHub, with `SHA256SUMS` and build provenance attestations
(`gh attestation verify <file> -R emercoin/emercoin`).

The build happens in the source tree; use one checkout per host. Functional tests listed in `test/functional/test_runner.py`
as not applicable or todo, and unit test suites in `EMERCOIN_TODO_TESTS`
(`src/Makefile.test.include`), are not part of the run.
