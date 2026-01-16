FROM debian:trixie-slim

ARG USER="xmss-user"
ARG DEBIAN_FRONTEND=noninteractive

ARG EASYCRYPT_RELEASE=f8fab1dc5541a84b416df172522809efe8419c37
ARG JASMIN_RELEASE=release-2025.06
ARG OCAML_RELEASE=ocaml.5.4.0

SHELL ["/bin/bash", "-c"]

RUN apt-get --quiet --assume-yes update && \
    apt-get --quiet --assume-yes upgrade && \
    apt-get --quiet --assume-yes install apt-utils && \
    apt-get --quiet --assume-yes install wget sudo build-essential valgrind && \
    apt-get --quiet --assume-yes clean

RUN dpkg --add-architecture amd64 && \
    apt-get --quiet --assume-yes update && \
    apt-get --quiet --assume-yes install libc6:amd64 libstdc++6:amd64 && \
    apt-get --quiet --assume-yes clean

# Install opam system packages
RUN sudo apt-get --quiet --assume-yes install opam && \
    sudo apt-get --quiet --assume-yes clean

# Setup final user
COPY --chown=root:root --chmod=0400 docker-parts/sudoers /etc/sudoers.d/
RUN useradd -ms /bin/bash -d /home/$USER -g root -G sudo -u 1001 $USER

USER $USER
WORKDIR /home/$USER

ENV PATH="/home/${USER}/bin:$PATH"

# Install nix
COPY --chown=root:root --chmod=0755 docker-parts/nix.conf /etc/nix/nix.conf
RUN sh <(wget -O - https://nixos.org/nix/install)

# Install opam
ENV OPAMYES=true
ENV OPAMJOBS=2
ENV OPAMVERBOSE=1

RUN opam init --disable-sandboxing --compiler=${OCAML_RELEASE} --auto-setup && \
    opam clean

# Install Alt-Ergo
COPY --chmod=0755 --chown=1001:0 docker-parts/alt-ergo bin/run-alt-ergo

RUN \
    version=2.5.2 && \
    opam switch create --no-switch alt-ergo-${version} ocaml-system && \
    opam pin     --switch=alt-ergo-${version} add -n alt-ergo ${version} && \
    opam install --switch=alt-ergo-${version} --deps-only --confirm-level=unsafe-yes alt-ergo && \
    opam install --switch=alt-ergo-${version} alt-ergo && \
    opam clean   --switch=alt-ergo-${version} && \
    ln -s run-alt-ergo ~/bin/alt-ergo-${version}

# Install CVC4
RUN \
    version=1.8 && \
    wget -O cvc4 https://github.com/CVC4/CVC4-archived/releases/download/${version}/cvc4-${version}-x86_64-linux-opt && \
    install -m 0755 cvc4 ~/bin/cvc4-${version} && \
    rm -f cvc4

# Install Z3
RUN \
    version=4.13.0 && glibc=2.35 && \
    wget -O z3.zip https://github.com/Z3Prover/z3/releases/download/z3-${version}/z3-${version}-x64-glibc-${glibc}.zip && \
    unzip -j z3.zip z3-${version}-x64-glibc-${glibc}/bin/z3 && \
    install -m 0755 z3 ~/bin/z3-${version} && \
    rm -f z3 z3.zip

# Install EasyCrypt
RUN eval $(opam env) && \
    opam pin -n add easycrypt https://github.com/EasyCrypt/easycrypt.git#${EASYCRYPT_RELEASE} && \ 
    opam install --deps-only --depext-only --confirm-level=unsafe-yes easycrypt && \
    opam install --deps-only easycrypt && \
    opam install easycrypt && \
    opam clean && \
    easycrypt why3config

# Install Jasmin && EcLib
RUN git clone https://gitlab.com/jasmin-lang/jasmin-compiler.git jasmin-compiler && \
    cd jasmin-compiler && git checkout ${JASMIN_RELEASE} && \
    USER=$USER source /home/$USER/.nix-profile/etc/profile.d/nix.sh && \
    nix-channel --update && \
    { cd compiler/ && nix-shell --command "make" && install -D jasmin* ~/bin; }

COPY --chown=$USER:0 docker-parts/easycrypt.conf /home/$USER/.config/easycrypt/easycrypt.conf
RUN sed -i s/__USER__/${USER}/g ~/.config/easycrypt/easycrypt.conf

# Install test system dependencies
RUN sudo apt-get --quiet --assume-yes install time valgrind libssl-dev python3-yaml && \
    sudo apt-get --quiet --assume-yes clean

# Copy repository
COPY --chown=$USER:0 . /home/$USER/xmss-jasmin
WORKDIR /home/$USER/xmss-jasmin

# Configure entry point
ENTRYPOINT ["opam", "exec", "--"]
CMD ["/bin/bash", "--login"]
