FROM ubuntu:jammy

RUN apt-get update
RUN apt-get install -y git build-essentials 


RUN git clone https://github.com/angr/angr-dev.git /angr-dev

WORKDIR /angr-dev
RUN ./setup.sh -i -e angr