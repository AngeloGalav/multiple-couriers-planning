FROM debian:12
COPY . /mine
RUN apt-get update -y
RUN apt-get -y install python3 pip minizinc bash coinor-cbc coinor-libcbc-dev glpk-utils wget
RUN apt-get -y install build-essential libreadline-dev libz-dev libgmp3-dev lib32ncurses5-dev libboost-program-options-dev libblas-dev
RUN dpkg -i --force-all SCIPOptSuite-8.0.4-Linux-debian.deb
# solves PEP 668
RUN rm /usr/lib/python3.11/EXTERNALLY-MANAGED
RUN pip install z3-solver numpy pulp scipy uuid typing more-itertools
CMD [ "bash" ]