#!/usr/bin/env bash
set -euo pipefail

install_dir="${1:-$(pwd)/.tla-tools}"
mkdir -p "$install_dir"

jar="$install_dir/tla2tools.jar"
curl -fL --retry 3 -o "$jar" \
  'https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar'
echo "7beec0f04818732a62fa193731711a99aa4f11279499b2360a7d156c519ea78d  $jar" | sha256sum -c -

archive="$install_dir/tlapm-linux.tar.gz"
curl -fL --retry 3 -o "$archive" \
  'https://github.com/tlaplus/tlapm/releases/download/1.6.0-pre/tlapm-1.6.0-pre-x86_64-linux-gnu.tar.gz'
echo "13eff4e3dd0a4570c1c33c46f052fd4eb3afad465eb201ebade607961f09d43c  $archive" | sha256sum -c -
tar -xzf "$archive" -C "$install_dir"

echo "TLA_TOOLS_JAR=$jar"
echo "TLAPM_BIN=$install_dir/tlapm/bin/tlapm"
"$install_dir/tlapm/bin/tlapm" --version
