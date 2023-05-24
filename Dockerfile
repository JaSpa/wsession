# Use an older version than the latest nixos/nix:2.15.0 because it triggers a
# segmenatation fault while building the image.
FROM nixos/nix:2.14.1

# Enable the nix command and flakes.
RUN set -ex; \
  mkdir -p "$HOME/.config/nix"; \
  echo 'experimental-features = nix-command flakes' >> "$HOME/.config/nix/nix.conf"; 

# Start in a bash shell, not inside the nix repl.
CMD bash

# Install agda, agda stdlib and other supporting tools (see docker/flake.nix).
# docker/flake.lock pins the version to which agda, the stdlib etc. resolve.
WORKDIR /workspace/setup
COPY docker .
RUN set -ex; \
  nix profile install -L .; \
  nix store gc; \
  mkdir -p "$HOME/.agda"; \
  echo "standard-library" >> "$HOME/.agda/defaults";

# Copy agda files.
WORKDIR /workspace/wsession
COPY src/*.lagda src/*.lagda.* src/*.agda .

# Ensure that everything checks fine.
#
# This checks the part of standard library which is used in the agda files and
# won't have to be rechecked later.
#
# Should we keep the *.agdai files of local files around? For now we remove
# them.
RUN set -ex; \
  shopt -s nullglob; \
  for f in *.lagda *.lagda.* *.agda; do agda $f; done; \
  rm -f *.agdai

# Copy supporting files.
COPY src/Makefile .
COPY src/Control ./Control
