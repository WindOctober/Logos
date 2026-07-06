FROM rust:1.88-bookworm

USER root

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        postgresql \
        postgresql-client \
        ca-certificates \
        curl \
        nodejs \
        npm \
        openjdk-17-jdk-headless \
        python3 \
        python3-venv \
        tar \
    && rm -rf /var/lib/apt/lists/*

RUN npm install -g @openai/codex

RUN ln -sf /usr/local/cargo/bin/cargo /usr/local/bin/cargo \
    && ln -sf /usr/local/cargo/bin/rustc /usr/local/bin/rustc \
    && ln -sf /usr/local/cargo/bin/rustup /usr/local/bin/rustup

WORKDIR /workspace

ENTRYPOINT []
CMD ["bash"]
