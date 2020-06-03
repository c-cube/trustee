all: release

release:
	@cargo build --release
	@ln -sf target/release/libtrustee_py.so trustee.so

check:
	@cargo check

debug:
	@cargo build
	@ln -sf target/debug/libtrustee_py.so trustee.so

clean:
	@cargo clean
