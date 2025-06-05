FROM python:3.12

# Install system dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        wget \
        ca-certificates \
        libgmp-dev \
        unzip \
        && rm -rf /var/lib/apt/lists/*

# Download and install the latest Z3 release (pre-built binary)
RUN wget -q -O z3-4.15.0-x64-glibc-2.39.zip https://github.com/Z3Prover/z3/releases/download/z3-4.15.0/z3-4.15.0-x64-glibc-2.39.zip && \
    unzip z3-4.15.0-x64-glibc-2.39.zip -d /opt/z3 && \
    cp /opt/z3/z3-4.15.0-x64-glibc-2.39/bin/z3 /usr/local/bin/ && \
    rm -rf z3-4.15.0-x64-glibc-2.39.zip /opt/z3

# Install Python Z3 API
RUN pip install z3-solver

CMD ["bash"]