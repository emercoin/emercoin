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

The build happens in the source tree. Functional tests listed in `test/functional/test_runner.py`
as not applicable or todo, and unit test suites in `EMERCOIN_TODO_TESTS`
(`src/Makefile.test.include`), are not part of the run.
