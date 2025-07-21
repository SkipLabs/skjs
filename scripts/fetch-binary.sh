#!/bin/bash

# SKJS Binary Fetcher
# Fetches pre-built SKJS binaries from GitHub Actions artifacts

set -euo pipefail

# Configuration
GITHUB_REPO="SkipLabs/skjs"
DEFAULT_PLATFORM="linux"
DEFAULT_ARCH="amd64"

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

# Function to show usage
usage() {
    cat << EOF
Usage: $0 [OPTIONS]

Fetch pre-built SKJS binaries from GitHub Actions artifacts.

OPTIONS:
    -b, --branch BRANCH     Branch to fetch from (default: main)  
    -c, --commit SHA        Specific commit SHA to fetch
    -p, --platform PLATFORM Platform (default: linux)
    -a, --arch ARCH         Architecture (default: amd64)
    -o, --output PATH       Output path for binary (default: ./skjs)
    -t, --token TOKEN       GitHub token (optional for public repos)
    -h, --help              Show this help message

EXAMPLES:
    # Fetch latest binary from main branch (public repo)
    $0

    # Fetch with GitHub token (higher rate limits)
    $0 --token YOUR_GITHUB_TOKEN

    # Fetch specific commit
    $0 --commit abc123def

    # Fetch to specific location
    $0 --output /usr/local/bin/skjs

ENVIRONMENT VARIABLES:
    GITHUB_TOKEN            GitHub token (optional)
EOF
}

# Default values
BRANCH="main"
COMMIT=""
PLATFORM="$DEFAULT_PLATFORM"
ARCH="$DEFAULT_ARCH"
OUTPUT_PATH="./skjs"
GITHUB_TOKEN="${GITHUB_TOKEN:-}"

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -b|--branch)
            BRANCH="$2"
            shift 2
            ;;
        -c|--commit)
            COMMIT="$2"
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
        -o|--output)
            OUTPUT_PATH="$2"
            shift 2
            ;;
        -t|--token)
            GITHUB_TOKEN="$2"
            shift 2
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

# Function to fetch binary from GitHub Actions
fetch_from_github() {
    local branch_or_commit="$1"
    
    log "Fetching binary from GitHub Actions for branch/commit: $branch_or_commit"
    
    # Set up authentication headers
    local auth_args=()
    if [[ -n "$GITHUB_TOKEN" ]]; then
        auth_args=(-H "Authorization: Bearer $GITHUB_TOKEN")
    fi
    
    # GitHub API base URL
    local api_base="https://api.github.com/repos/${GITHUB_REPO}"
    
    if [[ -n "$COMMIT" ]]; then
        # Fetch specific commit - get workflow runs for that commit
        log "Looking for workflow runs for commit: $COMMIT"
        local runs_url="${api_base}/actions/runs?head_sha=${COMMIT}&status=completed&conclusion=success"
    else
        # Fetch latest from branch
        log "Looking for latest successful workflow runs on branch: $branch_or_commit"
        local runs_url="${api_base}/actions/runs?branch=${branch_or_commit}&status=completed&conclusion=success"
    fi
    
    # Get recent successful workflow runs
    local workflow_run_id
    workflow_run_id=$(curl -s "${auth_args[@]}" "$runs_url" | \
                      jq -r '.workflow_runs[] | select(.name == "Build and Test SKJS") | .id' | head -1)
    
    if [[ -z "$workflow_run_id" || "$workflow_run_id" == "null" ]]; then
        error "No successful workflow runs found for branch/commit: $branch_or_commit"
        warn "Make sure the workflow has completed successfully"
        return 1
    fi
    
    log "Found workflow run ID: $workflow_run_id"
    
    # Get artifacts for the workflow run
    local artifacts_url="${api_base}/actions/runs/${workflow_run_id}/artifacts"
    local artifact_info
    artifact_info=$(curl -s "${auth_args[@]}" "$artifacts_url" | \
                    jq -r ".artifacts[] | select(.name | contains(\"skjs-${PLATFORM}-${ARCH}\")) | {id: .id, download_url: .archive_download_url}")
    
    if [[ -z "$artifact_info" || "$artifact_info" == "null" ]]; then
        error "No artifacts found for platform: ${PLATFORM}-${ARCH}"
        return 1
    fi
    
    local artifact_id
    local download_url
    artifact_id=$(echo "$artifact_info" | jq -r '.id')
    download_url=$(echo "$artifact_info" | jq -r '.download_url')
    
    log "Found artifact ID: $artifact_id"
    log "Downloading artifact..."
    
    # Create temporary directory for extraction
    local temp_dir
    temp_dir=$(mktemp -d)
    local zip_file="${temp_dir}/artifact.zip"
    
    # Download the artifact (it's a ZIP file)
    if [[ -n "$GITHUB_TOKEN" ]]; then
        curl -L -H "Authorization: Bearer $GITHUB_TOKEN" "$download_url" -o "$zip_file"
    else
        curl -L "$download_url" -o "$zip_file"
    fi
    
    if [[ ! -f "$zip_file" ]]; then
        error "Failed to download artifact"
        rm -rf "$temp_dir"
        return 1
    fi
    
    # Extract the ZIP file
    log "Extracting artifact..."
    unzip -q "$zip_file" -d "$temp_dir"
    
    # Find the binary file (look for skjs_* pattern, not .json)
    local binary_file
    binary_file=$(find "$temp_dir" -name "skjs_*" -type f ! -name "*.json" | head -1)
    
    if [[ -z "$binary_file" ]]; then
        error "No binary found in artifact"
        rm -rf "$temp_dir"
        return 1
    fi
    
    # Copy binary to output location
    cp "$binary_file" "$OUTPUT_PATH"
    chmod +x "$OUTPUT_PATH"
    
    # Clean up
    rm -rf "$temp_dir"
    
    success "Binary downloaded to: $OUTPUT_PATH"
    
    # Verify the binary
    if [[ -f "$OUTPUT_PATH" ]] && [[ -x "$OUTPUT_PATH" ]]; then
        local version
        version=$("$OUTPUT_PATH" --help 2>&1 | head -1 || echo "Version check failed")
        log "Binary version info: $version"
    fi
}


# Main execution
main() {
    log "SKJS Binary Fetcher"
    log "Platform: ${PLATFORM}_${ARCH}"
    log "Output: $OUTPUT_PATH"
    
    # Use GitHub Actions method
    local target
    if [[ -n "$COMMIT" ]]; then
        target="$COMMIT"
    else
        target="$BRANCH"
    fi
    
    if ! fetch_from_github "$target"; then
        error "Failed to fetch binary from GitHub Actions"
        exit 1
    fi
    
    success "Binary fetch completed successfully!"
}

# Check dependencies
if ! command -v curl &> /dev/null; then
    error "curl is required but not installed"
    exit 1
fi

if ! command -v jq &> /dev/null; then
    error "jq is required but not installed"
    exit 1
fi

if ! command -v unzip &> /dev/null; then
    error "unzip is required but not installed"
    exit 1
fi

# Run main function
main "$@"