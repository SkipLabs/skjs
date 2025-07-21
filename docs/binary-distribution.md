# SKJS Binary Distribution

This document describes the binary distribution system for SKJS, which automatically builds and publishes pre-compiled binaries through CircleCI.

## Overview

SKJS provides pre-built binaries through CircleCI:

- **CircleCI Artifacts** - 30-day retention with REST API access (requires authentication)
- **Private access** - All binaries require CircleCI token for access

This approach eliminates the need to commit binaries to the repository while maintaining control over binary distribution through authentication.

## Binary Naming Convention

All binaries follow this naming pattern:
```
skjs_{COMMIT_SHA}_{PLATFORM}_{ARCH}
```

Examples:
- `skjs_abc123def456_linux_amd64`
- `skjs_xyz789_linux_arm64`

Each binary is accompanied by a metadata JSON file with the `.json` extension containing build information.

## Distribution Method

### CircleCI Artifacts

**Access Method**: REST API with required authentication
**Retention**: 30 days
**Best for**: Controlled binary distribution

The CircleCI configuration (`.circleci/config.yml`) automatically:
- Builds release binaries on every push
- Creates versioned artifacts with metadata
- Stores them with 30-day retention
- Provides authenticated API access for downloading

#### Fetching from CircleCI

Use the provided script:
```bash
# Fetch latest binary (token required)
./scripts/fetch-binary.sh --token YOUR_CIRCLECI_TOKEN

# Fetch specific commit
./scripts/fetch-binary.sh --commit abc123def --token YOUR_CIRCLECI_TOKEN
```

Or manually via API:
```bash
# Get recent pipelines
curl -H "Circle-Token: YOUR_TOKEN" \
  "https://circleci.com/api/v2/project/github/SkipLabs/skjs/pipeline?branch=main"

# Download artifacts (see script for full flow)
```

## CI/CD Configuration

### CircleCI Setup

The `.circleci/config.yml` file contains two jobs:

1. **build_and_test**: Runs tests and code quality checks
2. **build_binaries**: Builds release binaries and stores as artifacts

Key features:
- Builds only after tests pass
- Creates artifacts with metadata
- Uses proper versioning and tagging
- Requires authentication for artifact access

### GitHub Actions

GitHub Actions (`.github/workflows/build-and-test.yml`) is used only for running tests on pull requests and pushes, without binary publishing.

## Local Development

### Building Locally

Use the provided build script:
```bash
# Basic build
./scripts/build-release.sh

# Custom output directory
./scripts/build-release.sh --output ./my-release

# Skip tests (faster)
./scripts/build-release.sh --skip-tests

# Clean build
./scripts/build-release.sh --clean
```

### Manual Build Process

```bash
# Ensure Skip repository is available
git clone https://github.com/SkipLabs/skip ../skip

# Build release binary
skargo build --release

# Binary will be at: target/host/release/skjs
```

## Integration with Consumer Projects

### Fetch Script Integration

Add the fetch script to your project and call it in your build process:

```dockerfile
# In Dockerfile
COPY scripts/fetch-binary.sh /tmp/
RUN /tmp/fetch-binary.sh --token $CIRCLECI_TOKEN --output /usr/local/bin/skjs
```

### Build Script Integration

```bash
# In your build script
./scripts/fetch-binary.sh --token $CIRCLECI_TOKEN
./skjs check src/*.ts
```

### Environment Variable Setup

```bash
# Set CircleCI token in your environment
export CIRCLECI_TOKEN="your-token-here"

# Then fetch without specifying token
./scripts/fetch-binary.sh
```

## Authentication and Security

### Required Tokens

**CircleCI Token** (Required):
- **Purpose**: Access to CircleCI artifacts
- **Scope**: Read-only project access
- **Set via**: Environment variable `CIRCLECI_TOKEN` or command-line `--token`
- **Note**: All binary downloads require authentication

### Security Best Practices

- Never commit tokens to repository
- Use read-only tokens where possible
- Rotate tokens regularly
- Use environment variables or secure secret management
- Verify binary checksums when possible

## Platform Support

### Currently Supported

- **Linux AMD64**: Primary platform, fully tested
- **Extensible Architecture**: Framework supports additional platforms

### Future Platforms

The system is designed to support:
- Linux ARM64
- macOS (x86_64 and ARM64)
- Windows (x86_64)

To add a new platform, update the CI/CD matrix configuration and ensure the Skip toolchain supports the target platform.

## Troubleshooting

### Common Issues

1. **"No binary found"**
   - Check if the build succeeded in CI
   - Verify platform/architecture parameters
   - Check token permissions

2. **"Binary download failed"**
   - Check CircleCI build status
   - Verify the branch/commit exists and has successful builds
   - Ensure artifact retention hasn't expired (30 days)

3. **"CircleCI API error"**
   - Verify token is valid and has correct permissions
   - Check if the project exists and builds are running
   - Ensure jq is installed for script usage

### Debug Mode

Enable verbose output in fetch script:
```bash
set -x  # Add to script for debug output
./scripts/fetch-binary.sh --token YOUR_TOKEN
```

### Fallback Options

If automated fetching fails:
1. Build locally using `./scripts/build-release.sh`
2. Download artifacts manually from CircleCI web interface (requires login)

## Monitoring and Maintenance

### Build Status

Monitor builds at:
- CircleCI: https://circleci.com/gh/SkipLabs/skjs
- GitHub Actions: Repository → Actions tab (tests only)

### Artifact Retention

- CircleCI artifacts: 30 days (configurable)

### Cleanup

Old artifacts are automatically cleaned up based on CircleCI's retention policies.

## Migration Guide

### From Manual Binary Management

If you currently manage SKJS binaries manually:

1. **Identify current usage**: Where and how you currently get/use SKJS
2. **Update build scripts**: Replace manual steps with fetch script calls
3. **Test integration**: Verify the automated approach works
4. **Remove manual binaries**: Clean up committed binaries from repositories

### Example Migration

Before (manual):
```bash
# Manual download and management
wget https://example.com/skjs-binary
chmod +x skjs-binary
```

After (automated):
```bash
# Automated fetch (requires token)
./scripts/fetch-binary.sh --token $CIRCLECI_TOKEN
```

## Contributing

### Adding New Platforms

1. Update CI/CD matrix to include new platform
2. Ensure Skip toolchain supports the platform
3. Test build process on target platform
4. Update documentation

### Improving Distribution

1. Consider adding checksums/signatures for security
2. Add support for version pinning
3. Create platform-specific optimizations
4. Implement retry logic for failed downloads

## Support

For issues with binary distribution:

1. Check this documentation
2. Review CI/CD build logs
3. Test with fetch scripts in debug mode
4. Open issues in the SKJS repository with:
   - Platform/architecture details
   - Error messages
   - Steps to reproduce