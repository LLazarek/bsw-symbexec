## Requirements
[Docker](https://docs.docker.com/engine/install/) (install and set up according to your environment).
Alternatively [Podman](https://podman.io/docs/installation), in which case execute the below instructions with `podman` instead of `docker`.

## Environment setup
Clone the repo:

``` shell
git clone https://github.com/LLazarek/bsw-symbexec.git
```

Build the docker image:

``` shell
cd bsw-symbexec
docker build -t bswse .
```

Launch the container:

``` shell
docker run -it -v "$(pwd)":/sym -w /sym bswse
```

And in the shell thus launched, check that everything is working:

``` shell
python env_test.py
```

You should see output like:

``` shell
[y = 0, x = 7]
```

You're all set!

