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
    -r, --release TAG       Fetch release by tag (e.g., v1.0.0)
    --latest-release        Fetch latest release (any tag starting with 'v')
    -p, --platform PLATFORM Platform (default: linux)
    -a, --arch ARCH         Architecture (default: amd64)
    -o, --output PATH       Output path for binary (default: auto-generated)
    -t, --token TOKEN       CircleCI API token (required)
    -h, --help              Show this help message

EXAMPLES:
    # Fetch latest development build from main branch
    # → saves as: skjs-main-abc1234-linux-amd64
    $0 --token YOUR_CIRCLECI_TOKEN

    # Fetch specific release
    # → saves as: skjs-v1.0.0-linux-amd64
    $0 --release v1.0.0 --token YOUR_CIRCLECI_TOKEN

    # Fetch latest release
    # → saves as: skjs-latest-release-linux-amd64
    $0 --latest-release --token YOUR_CIRCLECI_TOKEN

    # Fetch from feature branch
    # → saves as: skjs-feature-parser-abc1234-linux-amd64
    $0 --branch feature-parser --token YOUR_CIRCLECI_TOKEN

    # Use custom filename
    $0 --output ./my-skjs --token YOUR_CIRCLECI_TOKEN

ENVIRONMENT VARIABLES:
    CIRCLECI_TOKEN          CircleCI API token
EOF
}

# Default values
BRANCH="main"
COMMIT=""
RELEASE_TAG=""
LATEST_RELEASE=false
PLATFORM="$DEFAULT_PLATFORM"
ARCH="$DEFAULT_ARCH"
OUTPUT_PATH=""  # Will be determined dynamically
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
        -r|--release)
            RELEASE_TAG="$2"
            shift 2
            ;;
        --latest-release)
            LATEST_RELEASE=true
            shift
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

# Function to generate default output filename
generate_output_filename() {
    local filename
    
    if [[ -n "$RELEASE_TAG" ]]; then
        # For releases: skjs-v1.0.0-linux-amd64
        filename="skjs-${RELEASE_TAG}-${PLATFORM}-${ARCH}"
    elif [[ "$LATEST_RELEASE" == true ]]; then
        # For latest release: skjs-latest-release-linux-amd64
        filename="skjs-latest-release-${PLATFORM}-${ARCH}"
    elif [[ -n "$COMMIT" ]]; then
        # For specific commit: skjs-abc1234-linux-amd64
        local short_commit="${COMMIT:0:7}"
        filename="skjs-${short_commit}-${PLATFORM}-${ARCH}"
    else
        # For branch: skjs-main-abc1234-linux-amd64 (will get commit from API)
        filename="skjs-${BRANCH}-${PLATFORM}-${ARCH}"
    fi
    
    echo "$filename"
}

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
    
    if [[ -n "$RELEASE_TAG" ]]; then
        # For specific release tag
        log "Looking for tag: $RELEASE_TAG"
        pipeline_id=$(curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
          "https://circleci.com/api/v2/project/github/SkipLabs/skjs/pipeline" | \
          jq -r ".items[] | select(.vcs.tag == \"${RELEASE_TAG}\") | .id" | head -1)
    elif [[ "$LATEST_RELEASE" == true ]]; then
        # For latest release (any tag starting with 'v')
        log "Looking for latest release tag..."
        pipeline_id=$(curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
          "https://circleci.com/api/v2/project/github/SkipLabs/skjs/pipeline" | \
          jq -r '.items[] | select(.vcs.tag and (.vcs.tag | startswith("v"))) | .id' | head -1)
    else
        # For branch-based builds
        pipeline_id=$(curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
          "https://circleci.com/api/v2/project/github/SkipLabs/skjs/pipeline?branch=${branch_or_commit}" | \
          jq -r '.items[0].id // empty')
    fi
    
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
    
    # Different search patterns for development vs release builds
    if [[ -n "$RELEASE_TAG" ]] || [[ "$LATEST_RELEASE" == true ]]; then
        # For release builds: skjs_{tag}_{platform}_{arch}
        local tag_pattern
        if [[ -n "$RELEASE_TAG" ]]; then
            tag_pattern="$RELEASE_TAG"
        else
            # Will be handled in pipeline selection
            tag_pattern="v[0-9]"  # Any version tag
        fi
        
        artifact_url=$(curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
          "https://circleci.com/api/v2/project/github/SkipLabs/skjs/${job_number}/artifacts" | \
          jq -r ".items[] | select(.path | contains(\"skjs_\") and contains(\"${PLATFORM}_${ARCH}\") and (contains(\".json\") | not) and (contains(\"${tag_pattern}\") or test(\"skjs_v[0-9]\"))) | .url // empty")
    else
        # For development builds: skjs_{commit}_{branch}_{platform}_{arch}
        artifact_url=$(curl -s -H "Circle-Token: $CIRCLECI_TOKEN" \
          "https://circleci.com/api/v2/project/github/SkipLabs/skjs/${job_number}/artifacts" | \
          jq -r ".items[] | select(.path | contains(\"skjs_\") and contains(\"${branch_or_commit}\") and contains(\"${PLATFORM}_${ARCH}\") and (contains(\".json\") | not)) | .url // empty")
    fi
    
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
        
        # Try to enhance filename with commit info if not already specified
        if [[ -z "$COMMIT" && "$BRANCH" != "main" && -z "$RELEASE_TAG" && "$LATEST_RELEASE" != true ]]; then
            # Get commit SHA from the artifact name to enhance the filename
            local artifact_commit
            artifact_commit=$(echo "$artifact_url" | grep -o 'skjs_[a-f0-9]\{40\}' | cut -d'_' -f2 | head -c7)
            if [[ -n "$artifact_commit" ]]; then
                local enhanced_filename="${OUTPUT_PATH%-"${PLATFORM}"-"${ARCH}"}-${artifact_commit}-${PLATFORM}-${ARCH}"
                if [[ "$enhanced_filename" != "$OUTPUT_PATH" ]]; then
                    mv "$OUTPUT_PATH" "$enhanced_filename"
                    OUTPUT_PATH="$enhanced_filename"
                    log "Enhanced filename with commit: $(basename "$OUTPUT_PATH")"
                fi
            fi
        fi
        
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
    
    # Validate options
    local mode_count=0
    [[ -n "$RELEASE_TAG" ]] && ((mode_count++))
    [[ "$LATEST_RELEASE" == true ]] && ((mode_count++))
    [[ -n "$COMMIT" ]] && ((mode_count++))
    
    if [[ $mode_count -gt 1 ]]; then
        error "Cannot specify multiple fetch modes (--release, --latest-release, --commit)"
        exit 1
    fi
    
    # Set default output path if not specified
    if [[ -z "$OUTPUT_PATH" ]]; then
        OUTPUT_PATH="$(generate_output_filename)"
        log "Using default filename: $OUTPUT_PATH"
    fi
    
    # Determine what we're fetching
    if [[ -n "$RELEASE_TAG" ]]; then
        log "Fetching release: $RELEASE_TAG"
        target="$RELEASE_TAG"
    elif [[ "$LATEST_RELEASE" == true ]]; then
        log "Fetching latest release"
        target="latest-release"
    elif [[ -n "$COMMIT" ]]; then
        log "Fetching commit: $COMMIT"
        target="$COMMIT"
    else
        log "Fetching latest from branch: $BRANCH"
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