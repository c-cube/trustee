
build:
	@cargo build --release

all: build test

clean:
	@cargo clean

check:
	@cargo check

test:
	@cargo test
