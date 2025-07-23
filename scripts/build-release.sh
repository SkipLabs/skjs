#!/bin/bash

# SKJS Release Builder
# Builds SKJS binaries for release with proper versioning and metadata

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored output
log() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

# Configuration
DEFAULT_OUTPUT_DIR="./dist"
DEFAULT_PLATFORM="linux"
DEFAULT_ARCH="amd64"
PROJECT_VERSION="0.1.0"

# Function to show usage
usage() {
    cat << EOF
Usage: $0 [OPTIONS]

Build SKJS release binaries with proper versioning and metadata.

OPTIONS:
    -o, --output DIR        Output directory (default: ./dist)
    -p, --platform PLATFORM Platform (default: linux)
    -a, --arch ARCH         Architecture (default: amd64)
    -v, --version VERSION   Version string (default: 0.1.0)
    --skip-tests            Skip running tests before build
    --clean                 Clean output directory before build
    -h, --help              Show this help message

EXAMPLES:
    # Build with defaults
    $0

    # Build to specific directory
    $0 --output ./release

    # Build with version
    $0 --version 1.0.0

    # Clean build
    $0 --clean --output ./release
EOF
}

# Default values
OUTPUT_DIR="$DEFAULT_OUTPUT_DIR"
PLATFORM="$DEFAULT_PLATFORM"
ARCH="$DEFAULT_ARCH"
VERSION="$PROJECT_VERSION"
SKIP_TESTS=false
CLEAN=false

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -o|--output)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        -p|--platform)
            PLATFORM="$2"
            shift 2
            ;;
        -a|--arch)
            ARCH="$2"
            shift 2
            ;;
        -v|--version)
            VERSION="$2"
            shift 2
            ;;
        --skip-tests)
            SKIP_TESTS=true
            shift
            ;;
        --clean)
            CLEAN=true
            shift
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            error "Unknown option: $1"
            usage
            exit 1
            ;;
    esac
done

# Function to get git information
get_git_info() {
    if git rev-parse --git-dir > /dev/null 2>&1; then
        git rev-parse HEAD
    else
        echo "unknown"
    fi
}

get_git_branch() {
    if git rev-parse --git-dir > /dev/null 2>&1; then
        git branch --show-current 2>/dev/null || echo "unknown"
    else
        echo "unknown"
    fi
}

# Function to check if Skip repository exists
check_skip_repo() {
    if [[ ! -d "../skip" ]]; then
        log "Skip repository not found at ../skip"
        log "Cloning Skip repository..."
        git clone --depth=1 --shallow-submodules --recurse-submodules https://github.com/SkipLabs/skip ../skip
    else
        log "Skip repository found at ../skip"
    fi
}

# Function to run tests
run_tests() {
    if [[ "$SKIP_TESTS" == true ]]; then
        warn "Skipping tests as requested"
        return 0
    fi
    
    log "Running tests..."
    
    # Check formatting
    log "Checking code formatting..."
    make check-fmt
    
    # Check shell scripts
    log "Checking shell scripts..."
    make check-sh
    
    # Run type checking
    log "Running type checks..."
    skargo check
    
    # Run test suite
    log "Running test suite..."
    skargo test --jobs 8
    
    success "All tests passed!"
}

# Function to build binary
build_binary() {
    log "Building release binary..."
    skargo build --release
    
    if [[ ! -f "target/host/release/skjs" ]]; then
        error "Build failed: binary not found at target/host/release/skjs"
        return 1
    fi
    
    success "Binary built successfully"
}

# Function to create release package
create_release_package() {
    local commit_sha
    local branch_name
    local timestamp
    
    commit_sha=$(get_git_info)
    branch_name=$(get_git_branch)
    timestamp=$(date -u +%Y-%m-%dT%H:%M:%SZ)
    
    # Create versioned binary name
    local binary_name="skjs_${commit_sha}_${PLATFORM}_${ARCH}"
    local binary_path="${OUTPUT_DIR}/${binary_name}"
    
    log "Creating release package..."
    log "Binary: $binary_name"
    log "Output directory: $OUTPUT_DIR"
    
    # Create output directory
    mkdir -p "$OUTPUT_DIR"
    
    # Copy binary
    cp "target/host/release/skjs" "$binary_path"
    chmod +x "$binary_path"
    
    # Create metadata JSON
    cat > "${OUTPUT_DIR}/${binary_name}.json" << EOF
{
  "name": "skjs",
  "version": "${VERSION}",
  "commit": "${commit_sha}",
  "branch": "${branch_name}",
  "platform": "${PLATFORM}",
  "architecture": "${ARCH}",
  "timestamp": "${timestamp}",
  "build_type": "release",
  "builder": "$(whoami)@$(hostname)",
  "build_command": "$0"
}
EOF
    
    # Create latest symlinks
    ln -sf "$binary_name" "${OUTPUT_DIR}/skjs_${PLATFORM}_${ARCH}_latest"
    ln -sf "$binary_name" "${OUTPUT_DIR}/skjs_latest"
    
    # Create checksums
    log "Generating checksums..."
    (cd "$OUTPUT_DIR" && {
        sha256sum "$binary_name" > "${binary_name}.sha256"
        sha256sum "$binary_name" "${binary_name}.json" > "checksums.sha256"
    })
    
    success "Release package created in: $OUTPUT_DIR"
    log "Files created:"
    ls -la "$OUTPUT_DIR"
}

# Function to verify binary
verify_binary() {
    local binary_path="${OUTPUT_DIR}/skjs_latest"
    
    if [[ -f "$binary_path" ]] && [[ -x "$binary_path" ]]; then
        log "Verifying binary..."
        local help_output
        help_output=$("$binary_path" --help 2>&1 | head -3 || echo "Help check failed")
        log "Binary verification:"
        echo "$help_output"
        success "Binary verification completed"
    else
        error "Binary not found or not executable: $binary_path"
        return 1
    fi
}

# Main execution
main() {
    log "SKJS Release Builder"
    log "Version: $VERSION"
    log "Platform: ${PLATFORM}_${ARCH}"
    log "Output: $OUTPUT_DIR"
    
    # Clean if requested
    if [[ "$CLEAN" == true ]]; then
        log "Cleaning output directory..."
        rm -rf "$OUTPUT_DIR"
    fi
    
    # Check prerequisites
    if ! command -v skargo &> /dev/null; then
        error "skargo is not installed or not in PATH"
        error "Make sure you have the Skip toolchain installed"
        exit 1
    fi
    
    # Check Skip repository
    check_skip_repo
    
    # Run tests
    run_tests
    
    # Build binary
    build_binary
    
    # Create release package
    create_release_package
    
    # Verify binary
    verify_binary
    
    success "Release build completed successfully!"
    log "Release artifacts are in: $OUTPUT_DIR"
}

# Run main function
main "$@"