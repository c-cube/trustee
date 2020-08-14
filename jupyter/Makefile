
release:
	@cargo build --release

check:
	@cargo check

install: release
	@cargo install --path .
	@cargo run -- --install

clean:
	@cargo clean
