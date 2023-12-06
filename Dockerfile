FROM debian:12
COPY . /cdmo_project
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update -yq
RUN apt-get -yq install python3 pip minizinc bash coinor-cbc coinor-libcbc-dev glpk-utils wget nano bash
RUN apt-get -yq install wget cmake g++ m4 xz-utils libgmp-dev unzip zlib1g-dev libboost-program-options-dev libboost-serialization-dev \
 libboost-regex-dev libboost-iostreams-dev libtbb-dev libreadline-dev pkg-config git liblapack-dev libgsl-dev flex bison libcliquer-dev gfortran \
 file dpkg-dev libopenblas-dev rpm

RUN apt-get -yq install build-essential libreadline-dev libz-dev libgmp3-dev lib32ncurses5-dev libboost-program-options-dev libblas-dev

# SCIP installation
RUN cp /cdmo_project/docker_bins/scip /usr/local/bin

# chuffed installation
RUN git clone https://github.com/chuffed/chuffed
WORKDIR /chuffed
RUN mkdir build && cd build &&  cmake .. && cmake --build . -- -j8 &&  cmake --build . --target install
WORKDIR /

# HIGHS installation
RUN mkdir highs
RUN cd highs
RUN wget https://github.com/JuliaBinaryWrappers/HiGHSstatic_jll.jl/releases/download/HiGHSstatic-v1.6.0%2B0/HiGHSstatic.v1.6.0.x86_64-linux-gnu-cxx11.tar.gz
RUN tar -xzvf HiGHSstatic.v1.6.0.x86_64-linux-gnu-cxx11.tar.gz bin/highs -C highs
RUN cp bin/highs /usr/local/bin

# solves PEP 668
RUN rm /usr/lib/python3.11/EXTERNALLY-MANAGED

RUN pip install z3-solver numpy pulp scipy minizinc uuid typing more-itertools cython pebble pysmt
RUN pysmt-install --msat --confirm-agreement
RUN git clone https://github.com/cython/cython
RUN rm -rf /usr/local/lib/python3.11/dist-packages/pyximport/
RUN mv /cython/pyximport /usr/local/lib/python3.11/dist-packages

CMD [ "bash" ]