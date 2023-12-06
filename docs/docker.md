# How to use the docker container

## Building the container
To use the docker container, you must have first installed the Docker application.
After that, use the following commands:
```
docker build . -t progetto-palli-galavotti-freddi
```

## Running the container
Once the container image has been built, you can start the container without any worries (and without building the container anymore, unless you've made modifications to the Dockerfile).
To start the container, use the following command:
```
docker run -d -it --name="cdmo" progetto-palli-galavotti-freddi:latest
```
If everything went right, when executing the command `docker ps`, you should see a single container process called `cdmo`.

## Using the container
After that, we need to enter inside of the container. To do that, just use:
```
docker exec -it cdmo bash
```
After you've run the command, you should be able to get inside the container and run the required scripts.
You can find the scripts inside of the docker container by using `cd /cdmo_project && ls -al`.

### Running models inside of the container
When inside of the container, you need to use `python3` instead of the standard python command.
In this way you can run a model by first getting inside of the `cdmo_project` folder using `cd cdmo_project`.
After that, simply run the model by using, for example:
```
python3 cp_python.py -i 5 -so chuffed
```
__N.B.__: You __have__ to use `python3` instead of `python` as that is the name of the executable in debian. 

## Killing the container
After you're done with your work, you'll have to stop the container and removing it.
```
docker kill cdmo
docker rm cdmo
```
Next time you'll need to start the container, simply use the command that you've use to start the container.
To be sure that you have killed the container, use the command `docker ps -a`. If you see any active container, it means that the container was not shutdown properly.

## Copying files
If you need any of the generated files, such as results files, you can simply copy the files by opening another `bash` console on your local machine (not the container), and then typing

```
docker cp cdmo:/cdmo_project/res ./res
```

#### About the `docker_bins` folder
The `docker_bins` folder contains a special version of the `scip` solver, which was compiled on a Debian container in order to work inside of other Debian containers. It's not very special, however it is needed as the official `.dpkg` provided by the Zuse Institute Berlin (ZIB) did not seem to work properly and would require some obsolete dependencies.