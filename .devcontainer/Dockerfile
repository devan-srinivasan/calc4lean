# Base pytorch image with GPU suport
FROM pytorch/pytorch:2.3.1-cuda11.8-cudnn8-runtime

# Basic package update
RUN apt-get update && apt upgrade -y

# The flag is set to avoid unnecesarry questions during installation
# Example: It asks to set timezone during instalation of python.
ARG DEBIAN_FRONTEND=noninteractive

# Install VIM (For Convenience)
RUN apt-get install -y vim
RUN apt-get -y install git
RUN apt-get -y update; apt-get -y install curl

RUN bash -c 'curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:v4.11.0 || (echo && read -n 1 -s -r -p "Install failed, press ENTER to continue...")' && exit

# RUN pip install python-sat[aiger,approxmc,cryptosat]
# COPY requirements.txt .
# RUN pip install -r requirements.txt