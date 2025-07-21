# SKJS Binary Distribution

This document describes the binary distribution system for SKJS, which automatically builds and publishes pre-compiled binaries through GitHub Actions.

## Overview

SKJS provides pre-built binaries through GitHub Actions:

- **GitHub Actions Artifacts** - 30-day retention with REST API access
- **GitHub Releases** - Permanent storage for tagged versions

This approach eliminates the need to commit binaries to the repository while providing reliable access to pre-built SKJS binaries.

## Binary Naming Convention

All binaries follow this naming pattern:
```
skjs_{COMMIT_SHA}_{PLATFORM}_{ARCH}
```

Examples:
- `skjs_abc123def456_linux_amd64`
- `skjs_xyz789_linux_arm64`

Each binary is accompanied by a metadata JSON file with the `.json` extension containing build information.

## Distribution Methods

### 1. GitHub Actions Artifacts

**Access Method**: REST API (optional authentication)
**Retention**: 30 days
**Best for**: Development and CI/CD workflows

The GitHub Actions workflow (`.github/workflows/build-and-test.yml`) automatically:
- Builds release binaries on every push
- Creates versioned artifacts with metadata
- Stores them with 30-day retention
- Provides API access for downloading

#### Fetching from GitHub Actions

Use the provided script:
```bash
# Public repo (no token needed)
./scripts/fetch-binary.sh

# With token (higher rate limits)
./scripts/fetch-binary.sh --token YOUR_GITHUB_TOKEN
```

Or manually via API:
```bash
# Get workflow runs
curl "https://api.github.com/repos/SkipLabs/skjs/actions/runs?branch=main&status=completed"

# Download artifacts (see script for full flow)
```

### 2. GitHub Releases

**Access Method**: Direct download (public)
**Retention**: Permanent
**Best for**: Stable releases, production use

Releases are automatically created for git tags and include:
- Versioned binaries for all platforms
- Release notes
- Public download links (no authentication required)

## CI/CD Configuration

### GitHub Actions Setup

The `.github/workflows/build-and-test.yml` file contains three jobs:

1. **test**: Runs tests and code quality checks
2. **build-binaries**: Builds release binaries and stores as artifacts
3. **create-release**: Creates GitHub releases for tagged versions

Key features:
- Builds only after tests pass
- Creates artifacts with metadata
- Matrix builds for multiple platforms (extensible)
- Artifact uploads with 30-day retention
- Automatic release creation for tagged versions
- Uses proper versioning and tagging

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
# In Dockerfile (public repo)
COPY scripts/fetch-binary.sh /tmp/
RUN /tmp/fetch-binary.sh --output /usr/local/bin/skjs

# With GitHub token for higher rate limits
RUN /tmp/fetch-binary.sh --token $GITHUB_TOKEN --output /usr/local/bin/skjs
```

### Build Script Integration

```bash
# In your build script (public repo)
./scripts/fetch-binary.sh
./skjs check src/*.ts

# With token for higher rate limits
./scripts/fetch-binary.sh --token $GITHUB_TOKEN
./skjs check src/*.ts
```

### Direct Release Download

```bash
# Download from GitHub releases (no token needed)
curl -L -o skjs https://github.com/SkipLabs/skjs/releases/latest/download/skjs_linux_amd64
chmod +x skjs
```

## Authentication and Security

### Required Tokens

**GitHub Token** (Optional):
- **Purpose**: Higher API rate limits, access to private repositories
- **Scope**: `repo` (for private repos) or `public_repo` (for public repos)
- **Set via**: Environment variable `GITHUB_TOKEN` or command-line `--token`
- **Note**: Public repositories work without tokens (with lower rate limits)

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
   - Check GitHub Actions build status
   - Verify the branch/commit exists and has successful workflows
   - Ensure artifact retention hasn't expired (30 days)

3. **"GitHub API error"**
   - Check API rate limits (use token for higher limits)
   - Verify token permissions if using private repository
   - Ensure the repository name and workflow names are correct
   - Check that jq and unzip are installed

### Debug Mode

Enable verbose output in fetch script:
```bash
set -x  # Add to script for debug output
./scripts/fetch-binary.sh
```

### Fallback Options

If automated fetching fails:
1. Build locally using `./scripts/build-release.sh`
2. Download artifacts manually from GitHub Actions web interface
3. Download from GitHub releases (for tagged versions)

## Monitoring and Maintenance

### Build Status

Monitor builds at:
- GitHub Actions: Repository → Actions tab
- Workflow status: https://github.com/SkipLabs/skjs/actions

### Artifact Retention

- GitHub Actions artifacts: 30 days (configurable)
- GitHub release assets: Permanent

### Cleanup

Old artifacts are automatically cleaned up based on GitHub's retention policies.

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
# Automated fetch (public repo)
./scripts/fetch-binary.sh

# Or from releases
curl -L -o skjs https://github.com/SkipLabs/skjs/releases/latest/download/skjs_linux_amd64
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