FROM ubuntu:latest

RUN apt-get update && apt-get install -y wget
RUN wget https://mirrors.mit.edu/sage/src/sage-9.8-Ubuntu_22.04-x86_64.tar.xz && \
    tar -xvf sage-9.8-Ubuntu_22.04-x86_64.tar.xz && \
    mv sage-9.8-Ubuntu_22.04-x86_64 /opt/sage

ENV PATH="/opt/sage:$PATH"

RUN apt-get install -y cabal-install
RUN cabal update
RUN cabal install hspec
RUN cabal install hspec-discover

# docker build -t sagemath-hspec-env .
# docker run -it -v $(pwd)/topology_project:/app sagemath-hspec-env /bin/bash
