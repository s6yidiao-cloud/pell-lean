#!/usr/bin/env python3
"""Refresh the optional release manifests for the current checkout."""

import verify


def main():
    modules = verify.authored_modules()
    verify.scan_and_order(modules)
    verify.check_integrity(modules)
    vendor = verify.package_root() / "vendor/TauCeti"
    for base, manifest in [(vendor, vendor / "SOURCE_SHA256SUMS"),
                           (verify.ROOT, verify.ROOT / "checks/SOURCE_SHA256SUMS")]:
        files = sorted(path for path in verify.source_files()
                       if path.is_relative_to(base) and path != manifest)
        manifest.write_text("".join(f"{verify.digest(path)}  {path.relative_to(base)}\n"
                                    for path in files))
    verify.check_integrity(modules, frozen=True)
    print("Release manifests updated; Lean compilation is a separate check.")


if __name__ == "__main__":
    main()
