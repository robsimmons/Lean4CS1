# Source and target directories
SRC_DIR := FPCourse
BUILD_DIR := src/FPCourse

# Find all source files recursively
SRC_FILES := $(shell find $(SRC_DIR) -type f -name '*.lean')
# Derive corresponding output files with .md extension
BUILD_FILES := $(patsubst $(SRC_DIR)/%.lean,$(BUILD_DIR)/%.md,$(SRC_FILES))

# Default target: convert all .lean files to .md, then build the book
all: $(BUILD_FILES)
	mdbook build

# Rule: .lean → .md
# Uses convert.hs (Haskell) if runhaskell is available, else convert.py (Python)
$(BUILD_DIR)/%.md: $(SRC_DIR)/%.lean
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
	rm -rf $(BUILD_DIR)

# Clean everything including the built book
clean:
	rm -rf $(BUILD_DIR) book/

.PHONY: all convert build serve clean-md clean
