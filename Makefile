OPTS?=-j 3 --profile=release

all:
	@dune build @all $(OPTS)

opentheory:
	@dune build @src/opentheory/all $(OPTS)

WATCH?=@check
watch:
	@dune build $(OPTS) $(WATCH) -w

test:
	@dune runtest $(OPTS) --force --no-buffer

clean:
	@dune clean

doc:
	@dune build @doc

format:
	@dune fmt --auto-promote

format-check:
	@dune fmt --display=quiet

webui:
	@pnpm --dir webui install --frozen-lockfile
	@pnpm --dir webui build
	@mkdir -p src/opentheory/tool/_webui
	@cp webui/dist/trustee-ui.js webui/dist/trustee-ui.js.map src/opentheory/tool/_webui/
	@dune build @all

E2E_LOG?=_build/e2e-server.log

e2e: webui
	@test -f ot-data.zip || ./build_proofs.sh
	@set -e; \
	pid=; \
	trap 'test -z "$$pid" || kill -TERM -$$pid 2>/dev/null || true' EXIT; \
	setsid ./run_server.sh > $(E2E_LOG) 2>&1 & pid=$$!; \
	for _ in $$(seq 1 120); do \
	  curl -fs -o /dev/null http://127.0.0.1:8089/ 2>/dev/null && break; \
	  sleep 1; \
	done; \
	curl -fsS -o /dev/null http://127.0.0.1:8089/; \
	pnpm --dir webui run e2e

.PHONY: format clean webui e2e

KERNEL_DIR=$${HOME}/.local/share/jupyter/kernels/trustee_script/

install_kernel:
	mkdir -p $(KERNEL_DIR)
	cp data/kernel.json $(KERNEL_DIR)/

