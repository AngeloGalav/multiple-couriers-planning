FROM debian:12
COPY . /mine
RUN apt-get update -y
RUN apt-get -y install python3 pip minizinc bash
RUN pip install z3-solver numpy pulp scipy uuid typing more-itertools
CMD [ "bash" ]