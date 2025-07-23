#!/bin/bash

# SKJS Binary Fetcher
# Fetches pre-built SKJS binaries from CircleCI artifacts

set -euo pipefail

# Configuration  
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

Fetch pre-built SKJS binaries from CircleCI artifacts.

OPTIONS:
    -b, --branch BRANCH     Branch to fetch from (default: main)
    -c, --commit SHA        Specific commit SHA to fetch
    -p, --platform PLATFORM Platform (default: linux)
    -a, --arch ARCH         Architecture (default: amd64)
    -o, --output PATH       Output path for binary (default: ./skjs)
    -t, --token TOKEN       CircleCI API token (required)
    -h, --help              Show this help message

EXAMPLES:
    # Fetch latest binary from main branch
    $0 --token YOUR_CIRCLECI_TOKEN

    # Fetch specific commit
    $0 --commit abc123def --token YOUR_CIRCLECI_TOKEN

    # Fetch to specific location
    $0 --output /usr/local/bin/skjs --token YOUR_CIRCLECI_TOKEN

ENVIRONMENT VARIABLES:
    CIRCLECI_TOKEN          CircleCI API token
EOF
}

# Default values
BRANCH="main"
COMMIT=""
PLATFORM="$DEFAULT_PLATFORM"
ARCH="$DEFAULT_ARCH"
OUTPUT_PATH="./skjs"
CIRCLECI_TOKEN="${CIRCLECI_TOKEN:-}"

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
            CIRCLECI_TOKEN="$2"
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

# Function to fetch binary from CircleCI (using working Dockerfile approach)
fetch_from_circleci() {
    local branch_or_commit="$1"
    
    if [[ -z "$CIRCLECI_TOKEN" ]]; then
        error "CircleCI token is required. Set CIRCLECI_TOKEN environment variable or use --token option."
        return 1
    fi
    
    log "Fetching binary from CircleCI for branch: $branch_or_commit"
    log "Platform: ${PLATFORM}_${ARCH}"
    
    # Step 1: Get pipeline ID
    log "Getting pipeline ID..."
    local pipeline_id
    pipeline_id=$(curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
      "https://circleci.com/api/v2/project/github/SkipLabs/skjs/pipeline?branch=${branch_or_commit}" | \
      jq -r '.items[0].id // empty')
    
    if [[ -z "$pipeline_id" ]] || [[ "$pipeline_id" = "null" ]]; then
      error "No pipelines found for branch $branch_or_commit"
      return 1
    fi
    log "Pipeline ID: $pipeline_id"
    
    # Step 2: Get workflow ID  
    log "Getting workflow ID..."
    local workflow_id
    workflow_id=$(curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
      "https://circleci.com/api/v2/pipeline/${pipeline_id}/workflow" | \
      jq -r '.items[0].id // empty')
    
    if [[ -z "$workflow_id" ]] || [[ "$workflow_id" = "null" ]]; then
      error "No workflows found for pipeline $pipeline_id"  
      return 1
    fi
    log "Workflow ID: $workflow_id"
    
    # Step 3: Get job number for build_binaries job
    log "Getting job number..."
    local job_number
    job_number=$(curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
      "https://circleci.com/api/v2/workflow/${workflow_id}/job" | \
      jq -r '.items[] | select(.name == "build_binaries") | .job_number // empty')
    
    if [[ -z "$job_number" ]] || [[ "$job_number" = "null" ]]; then
      error "No build_binaries job found"
      log "Available jobs:"
      curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
        "https://circleci.com/api/v2/workflow/${workflow_id}/job" | \
        jq -r '.items[].name'
      return 1
    fi
    log "Job number: $job_number"
    
    # Step 4: Get artifact URL  
    log "Getting artifact URL..."
    local artifact_url
    artifact_url=$(curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
      "https://circleci.com/api/v2/project/github/SkipLabs/skjs/${job_number}/artifacts" | \
      jq -r ".items[] | select(.path | contains(\"skjs_\") and contains(\"${PLATFORM}_${ARCH}\") and (contains(\".json\") | not)) | .url // empty")
    
    if [[ -z "$artifact_url" ]] || [[ "$artifact_url" = "null" ]]; then
      error "No matching SKJS binary artifact found"
      log "Available artifacts:"
      curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
        "https://circleci.com/api/v2/project/github/SkipLabs/skjs/${job_number}/artifacts" | \
        jq -r '.items[].path'
      return 1
    fi
    
    # Step 5: Download binary
    log "Downloading SKJS binary..."
    if curl -L -H "Circle-Token: $CIRCLECI_TOKEN" "$artifact_url" -o "$OUTPUT_PATH"; then
        chmod +x "$OUTPUT_PATH" 
        success "Binary downloaded to: $OUTPUT_PATH"
        
        # Verify the binary
        if [[ -f "$OUTPUT_PATH" ]] && [[ -x "$OUTPUT_PATH" ]]; then
            local version
            version=$("$OUTPUT_PATH" --help 2>&1 | head -1 || echo "Binary ready")
            log "Binary info: $version"
        fi
        return 0
    else
        error "Failed to download binary"
        return 1
    fi
}


# Main execution
main() {
    log "SKJS Binary Fetcher"
    log "Platform: ${PLATFORM}_${ARCH}"
    log "Output: $OUTPUT_PATH"
    
    # Use CircleCI method
    local target
    if [[ -n "$COMMIT" ]]; then
        target="$COMMIT"
    else
        target="$BRANCH"
    fi
    
    if ! fetch_from_circleci "$target"; then
        error "Failed to fetch binary using CircleCI method"
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

# Run main function
main "$@"