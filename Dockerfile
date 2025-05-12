FROM debian:stable-20250407-slim

LABEL version="0.0.1"
LABEL maintainer="rui.fernandes@mpi-sp.org" 

ARG USER="xmss-user"

ARG EASYCRYPT_RELEASE=r2025.03
ARG JASMIN_RELEASE=release-2025.02

SHELL ["/bin/bash", "-c"]

RUN apt-get --quiet --assume-yes update && \
    apt-get --quiet --assume-yes upgrade && \
    apt-get --quiet --assume-yes install apt-utils && \
    apt-get --quiet --assume-yes install \
      sudo wget curl git time xz-utils libicu-dev \
      ocaml ocaml-native-compilers camlp4-extra opam \
      autoconf debianutils libgmp-dev pkg-config zlib1g-dev \
      vim build-essential python3 python3-pip m4 libgsl-dev \ 
      libpcre3-dev jq parallel valgrind bash-completion \
      libtext-diff-perl libssl-dev

RUN apt-get --quiet --assume-yes clean

RUN echo "%sudo  ALL=(ALL) NOPASSWD: ALL" > /etc/sudoers.d/sudoers && \
    chown root:root /etc/sudoers.d/sudoers && \
    chmod 0400 /etc/sudoers.d/sudoers && \
    useradd --create-home --shell /bin/bash --home-dir /home/$USER --user-group --groups sudo --uid 1001 $USER

USER $USER
WORKDIR /home/$USER

RUN curl -L https://nixos.org/nix/install > nix-install && \
    sh nix-install

# Install EasyCrypt & SMT Solvers
RUN export OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=$(nproc) && \
    opam init --disable-sandboxing && \
    opam install opam-depext && \
    opam pin add -n alt-ergo 2.5.2 && \
    opam install alt-ergo && \
    opam clean

RUN wget --no-verbose --show-progress --progress=bar:force:noscroll --timeout=10 --waitretry=5 --tries=5 \
    -O cvc4 https://github.com/CVC4/CVC4-archived/releases/download/1.8/cvc4-1.8-x86_64-linux-opt && \ 
    sudo install -D cvc4 /usr/local/bin/

RUN wget --no-verbose --show-progress --progress=bar:force:noscroll --timeout=10 --waitretry=5 --tries=5 \
    https://github.com/Z3Prover/z3/releases/download/z3-4.13.0/z3-4.13.0-x64-glibc-2.35.zip && \
    unzip -j z3-4.13.0-x64-glibc-2.35.zip z3-4.13.0-x64-glibc-2.35/bin/z3 && \
    sudo install -D z3 /usr/local/bin/

RUN eval $(opam env) && \
    export OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=$(nproc) && \
    opam pin -n add easycrypt https://github.com/EasyCrypt/easycrypt.git#${EASYCRYPT_RELEASE} && \ 
    opam depext easycrypt && \
    opam install easycrypt && \
    easycrypt why3config

# Install Jasmin & set ECLib
RUN git clone https://gitlab.com/jasmin-lang/jasmin-compiler.git jasmin-compiler && \
    cd jasmin-compiler && git checkout ${JASMIN_RELEASE} && \
    USER=$USER source /home/$USER/.nix-profile/etc/profile.d/nix.sh && \
    nix-channel --update && \
    cd compiler/ && nix-shell --command "make" && \
    sudo install -D jasmin* /usr/local/bin/ && \
    cd - && echo -e "[general]\nidirs = Jasmin:$(pwd)/eclib" > ~/.config/easycrypt/easycrypt.conf

COPY --chown=$USER:$USER . /home/$USER/xmss-jasmin
WORKDIR /home/$USER/xmss-jasmin

ENTRYPOINT ["opam", "exec", "--"]
CMD ["/bin/bash", "--login"]
