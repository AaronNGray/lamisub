# Based on Debian Stretch
FROM debian:stretch

# Basic tools
RUN \
  apt-get update && \
  apt-get --no-install-recommends install -y \
    make git ocaml-nox ocaml-findlib camlp5 vim wget && \
  apt-get clean && \
  rm -Rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

# Compile Coq
RUN \
  export COQVER=8.6.1 && \
  cd / && \
  wget --no-check-certificate \
    https://github.com/coq/coq/archive/V$COQVER.tar.gz \
    -O coq.tar.gz && \
  tar zxf coq.tar.gz && \
  cd coq-* && \
  ./configure -prefix /usr -nodoc -coqide no -usecamlp5 && \
  make -j$(grep -c ^processor /proc/cpuinfo) && \
  make install && \
  cd / && rm -Rf coq-* coq.tar.gz

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
