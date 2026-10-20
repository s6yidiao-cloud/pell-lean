# Source-only packaging review

The local packager passed its source/import and frozen-integrity checks.
The archive was inspected for safe unique regular-file paths, all required
public sources, compiler receipts, CI and licenses, and exclusion of Git
internals, caches, compiled objects, logs and macOS metadata.

A temporary extraction passed the source/import and integrity checks for all
851 local Lean modules. Its manuscript/configuration hashes and every source
hash in the fresh compiler receipts matched the extracted files. Only the
current manuscript and neutral public entry point are included.

The final archive was then produced twice and compared byte for byte to check
deterministic packaging, followed by another extraction/integrity check. The
archive checksum and file count are recorded in the local release receipt
under the ignored `build/` directory to avoid a self-referential archive hash.
No second Lean build is credited to this packaging check.
