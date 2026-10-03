# Source from any directory: source /workspace/shared/economics-next-proof/env.sh
_ECONOMICS_PROJECT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
export ELAN_HOME="$_ECONOMICS_PROJECT_DIR/.toolchain/elan"
export PATH="$ELAN_HOME/bin:$PATH"
export XDG_CACHE_HOME="$_ECONOMICS_PROJECT_DIR/.toolchain/cache"
unset _ECONOMICS_PROJECT_DIR
