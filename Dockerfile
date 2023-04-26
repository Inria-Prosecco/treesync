FROM nixos/nix
RUN mkdir /artifact
WORKDIR /artifact
COPY flake.nix flake.lock /artifact/
RUN nix --extra-experimental-features nix-command --extra-experimental-features flakes develop -c true
COPY comparse /artifact/comparse
COPY dolev-yao-star /artifact/dolev-yao-star
COPY mls-star /artifact/mls-star
COPY README.md /artifact/README.md
CMD nix --extra-experimental-features nix-command --extra-experimental-features flakes develop
