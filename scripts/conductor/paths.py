"""Where the conductor tools work: the repository (two directories up),
the front end's sources, this directory, and a scratch directory for what
they write between steps (`CONDUCTOR_TMP`, else `target/conductor/`)."""
import os
X = os.path.dirname(os.path.abspath(__file__)) + '/'
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC = ROOT + '/crates/fixpt-fx26/src/'
T = os.environ.get('CONDUCTOR_TMP', ROOT + '/target/conductor') .rstrip('/') + '/'
os.makedirs(T, exist_ok=True)
# Runs a command, killing it (and its children) after a number of seconds.
TIMEOUT = X + 't'
