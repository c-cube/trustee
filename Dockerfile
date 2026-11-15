ARG ALPINE_VERSION=3.22
ARG OCAML_VERSION=5.4.1
ARG OPAM_REPO_COMMIT=3ca11aaa3b437179fd587ebcbe006b6aa2c21683
ARG NODE_VERSION=22

FROM node:${NODE_VERSION}-alpine AS ui
WORKDIR /ui
ENV PUPPETEER_SKIP_DOWNLOAD=1
COPY webui/package.json webui/pnpm-lock.yaml webui/pnpm-workspace.yaml ./
RUN corepack enable && pnpm install --frozen-lockfile
COPY webui/ .
RUN pnpm build

FROM alpine:${ALPINE_VERSION} AS build
ARG OCAML_VERSION
ARG OPAM_REPO_COMMIT
RUN apk add --no-cache ca-certificates curl git unzip build-base pkgconf m4 \
      opam zlib-dev curl-dev openssl-dev
ENV OPAMROOT=/root/.opam OPAMSWITCH=/root/w OPAMYES=1 OPAMCONFIRMLEVEL=unsafe-yes
# deterministically setup switch from a commit of opam-repo
RUN git init /tmp/opam-repo && cd /tmp/opam-repo && \
    git remote add origin https://github.com/ocaml/opam-repository.git && \
    git fetch --depth 1 origin $OPAM_REPO_COMMIT && \
    git checkout FETCH_HEAD && \
    opam init --disable-sandboxing --bare --no-setup -k local /tmp/opam-repo && \
    opam switch create /root/w --packages=ocaml-base-compiler.$OCAML_VERSION && \
    opam install --no-depexts \
      dune ocamlfind containers pp_loc iter trace sha trace-tef logs lru \
      tiny_httpd tiny_httpd_camlzip camlzip opentelemetry-client-ocurl && \
    rm -rf /tmp/opam-repo

WORKDIR /src
COPY . .
COPY --from=ui /ui/dist/ src/opentheory/tool/_webui/
RUN opam exec -- dune build --profile=release src/opentheory/tool/trustee_ot.exe && \
    strip _build/default/src/opentheory/tool/trustee_ot.exe

FROM alpine:${ALPINE_VERSION} AS prod
RUN apk add --no-cache libcurl zlib ca-certificates
COPY --from=build /src/_build/default/src/opentheory/tool/trustee_ot.exe /usr/local/bin/trustee_ot
ENV PORT=8089 \
    ADDR=0.0.0.0
HEALTHCHECK --interval=30s --timeout=5s --start-period=300s --retries=3 \
  CMD wget -q --spider http://127.0.0.1:${PORT}/ || exit 1
CMD exec /usr/local/bin/trustee_ot --serve --dir /data --proof-zip /ot-data.zip --port "$PORT" --addr "$ADDR"
