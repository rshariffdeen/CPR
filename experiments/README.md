# Experiment Replication

CPR successfully generates correct patches for most of the defects in our data-set which are curated from three benchmarks; ManyBugs, 
ExtractFix and SVCOMP. For each defect, we provide an url that contains the developer patch and the generated patch by CPR at
https://cpr-tool.github.io. 

In our replication package, we include scripts to reproduce the experiment setup which can be evaluated using our tool. 
This directory includes scripts and Dockerfile to re-create the experiment setup, you can also use our pre-built Docker 
which can be downloaded from following repository

Dockerhub Repo: https://hub.docker.com/repository/docker/rshariffdeen/cpr:experiments-cpr

# Getting Started

## Building the environment
Setup environment can be built using the Dockerfile provided within, which will encompass the dependencies, configurations
and setup scripts. Use the following command:

``
docker build -t cpr-experiment .
``

Note that the build process can be time-consuming, hence you can also use the pre-built docker image using the command:

``
docker pull rshariffdeen/cpr:experiments-cpr
``

Having the image, you can now start a Docker container. We recommend linking the container to folders in the filesystem,
so that it is possible to check the logs and generated outputs also outside of the Docker container. 

``
docker run --name cpr-container -it cpr bash
``

## Test Run
You can check if everything is working well, by running a simple test-case from our test-suite. 

``
pypy3 CPR.py --conf=/CPR/tests/bug-types/div-zero/div-zero-1/repair.conf
``

The program /CPR/tests/bug-types/div-zero/div-zero-1/test.c contains a simple division-by-zero error, which we want to fix with CPR.

### CPR Output
The output message at the end of the execution should look similar to the following:

	Startup: 0.003 minutes
	Build: 0.009 minutes
	Testing: 0.054 minutes
	Synthesis: 0.010 minutes
	Explore: 0.167 minutes
	Refine: 0.463 minutes
	Reduce: 0.875 minutes
	Iteration Count: 4
	Patch Start Count: 85
	Patch End Seed Count: 42
	Patch End Count: 42
	Template Start Count: 5
	Template End Seed Count: 5
	Template End Count: 5
	Paths Detected: 2
	Paths Explored: 2
	Paths Skipped: 0
	Paths Hit Patch Loc: 3
	Paths Hit Observation Loc: 2
	Paths Hit Crash Loc: 2
	Paths Crashed: 1
	Component Count: 6
	Component Count Gen: 4
	Component Count Cus: 2
	Gen Limit: 40


For more examples refer [this guide](../doc/Examples.md)


# Example Run
Following details how to run the scripts and the tool to replicate the results of our experiments.
Once you build the docker image, you spin up a container as mentioned above. 

Inside the container the following directories will be used
- /CPR - this will be the tool directory
- /experiments - all experiment setups will be deployed in this directory


In /experiments directory a python driver is provided to run all experiments. 
You can run all the experiments using the following command

``
python3.7 driver.py
``

You can specify the driver to setup the environment and manually run the tool later by using following command, which will 
setup the experiment data in /data directory. 

``
python3.7 driver.py --only-setup
``

You can also select a single test-case you want to replicate by running the following command, where the bug ID is the id specified in our benchmark.

``
python3.7 driver.py --bug-id=BUG_ID
``

Alternatively, you can run the experiment manually (after setting up)

``
pypy3 CPR.py --conf=/path/to/configuration
``

