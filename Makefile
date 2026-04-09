# Source and target directories
SRC_DIRS := Overview Distillate FPCourse

# Find all source files recursively across all source directories
SRC_FILES := $(shell find $(SRC_DIRS) -type f -name '*.lean')
# Derive corresponding output files with .md extension under src/
BUILD_FILES := $(patsubst %.lean,src/%.md,$(SRC_FILES))

# Default target: convert all .lean files to .md, then build the book
all: $(BUILD_FILES)
	mdbook build

# Rule: .lean → src/%.md
$(BUILD_FILES): src/%.md: %.lean
	@mkdir -p $(dir $@)
	echo "Converting $< into $@"
	@if command -v runhaskell >/dev/null 2>&1; then \
		scripts/convert.hs $< $@; \
	else \
		python3 scripts/convert.py $< $@; \
	fi

# Convert only (no mdbook build)
convert: $(BUILD_FILES)

# Build the book (assumes convert has been run)
build:
	mdbook build

# Serve locally with live reload
serve:
	mdbook serve

# Clean generated markdown (but keep src/SUMMARY.md and src/introduction.md)
clean-md:
	rm -rf src/Overview src/FPCourse src/Distillate

# Clean everything including the built book
clean:
	rm -rf src/Overview src/FPCourse src/Distillate book/

.PHONY: all convert build serve clean-md clean
