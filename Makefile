
check:
	@cargo check

build:
	@cargo build --release

clean:
	@cargo clean

test:
	@dune runtest --force --no-buffer
