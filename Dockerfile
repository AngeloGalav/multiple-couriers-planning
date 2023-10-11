FROM debian:12
COPY . /mine
RUN apt-get update -y
RUN apt-get -y install python3 pip minizinc bash ps
RUN pip install z3-solver numpy pulp
CMD [ "bash" ]