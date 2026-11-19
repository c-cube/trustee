ARG NODE_VERSION=22

FROM node:${NODE_VERSION}-alpine AS ui
WORKDIR /ui
COPY webui/package.json webui/pnpm-lock.yaml webui/pnpm-workspace.yaml ./
RUN corepack enable && pnpm install --frozen-lockfile --filter trustee-webui
COPY webui/ .
RUN pnpm --config.verify-deps-before-run=false build
# ^ without this flag, pnpm reconciles the workspace on `pnpm run` and
# headless-installs the e2e package (puppeteer) into the prod image

FROM ghcr.io/c-cube/c-cube-commmon/ci-5.5:latest AS build
RUN apt-get update && \
    apt-get install -y --no-install-recommends zlib1g-dev && \
    rm -rf /var/lib/apt/lists/*
RUN opam install --no-depexts \
      containers pp_loc iter trace sha trace-tef logs lru \
      tiny_httpd tiny_httpd_camlzip camlzip opentelemetry-client-ocurl
WORKDIR /src
COPY . .
COPY --from=ui /ui/dist/ src/opentheory/tool/_webui/
RUN opam exec -- dune build --profile=release src/opentheory/tool/trustee_ot.exe && \
    strip _build/default/src/opentheory/tool/trustee_ot.exe

FROM debian:trixie-slim AS prod
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      libcurl4t64 zlib1g ca-certificates curl && \
    rm -rf /var/lib/apt/lists/*
COPY --from=build /src/_build/default/src/opentheory/tool/trustee_ot.exe /usr/local/bin/trustee_ot
ENV PORT=8089 \
    ADDR=0.0.0.0
HEALTHCHECK --interval=30s --timeout=5s --start-period=300s --retries=3 \
  CMD curl -fs http://127.0.0.1:${PORT}/ || exit 1
CMD exec /usr/local/bin/trustee_ot --serve --dir /data --proof-zip /ot-data.zip --port "$PORT" --addr "$ADDR"
