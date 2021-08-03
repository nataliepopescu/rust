# How to Build and Test Custom NADER pass

## Setup

```sh
cp config.toml.example config.toml
```

and make the following changes: 

```
line 265 | extended = true
line 271 | tools = ["cargo"]
line 316 | prefix="/path/to/prefix"
```

## Build and Install

Build and install Rust: 

```sh
./x.py build && ./x.py install
```

Create a rustup toolchain pointing to your local Rust build: 

```sh
rustup toolchain link <tchain-name> /path/to/rust/root/build/<target-triple>/stage2
```

Note that `/path/to/rust/root` is the root of where your Rust repository is 
cloned, and not the prefix path in your `cargo.toml`. 

## Test

Clone [this](https://github.com/nataliepopescu/assume_true)
repository and: 

```sh
cd assume_true/forpaper/
```

Override the default toolchain for the `forpaper/` directory with the custom one you 
created earlier: 

```sh
rustup override set <tchain-name>
```

Finally, compile and run the test code: 

```sh
RUSTFLAGS="-Z convert-unchecked-indexing -Z dump-mir=perf_mot" cargo bench
```

There are many print statements, so consider piping or redirecting 
stdout and stderr to files like so: 

```sh
RUSTFLAGS="-Z convert-unchecked-indexing -Z dump-mir=perf_mot" cargo bench > out 2> err
```
