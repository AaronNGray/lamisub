# Based on Debian Stretch
FROM debian:stretch

# Install Coq environment
RUN \
  apt-get update && \
  apt-get --no-install-recommends install -y coq make git ocaml-nox vim && \
  apt-get clean && \
  rm -Rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

# Compile ott
RUN \
  cd / && \
  GIT_SSL_NO_VERIFY=true git clone https://github.com/ott-lang/ott.git && \
  cd ott && git checkout 0.25 && make world && \
  cp bin/ott /usr/bin/ && \
  rm -Rf /ott

# Copy current directory to container
ADD . /lamisub

# Compile Coq scripts
RUN \
  cd /lamisub && make distclean && make

# Image metadata
CMD /bin/bash
WORKDIR /lamisub
