# Asterix data format parsing and unparsing library for haskell

## Develop

```bash
nix-shell

# ghcid
ghcid "--command=ghci -Wall -ilib -iother lib/Asterix.hs"
ghcid "--command=ghci -Wall -ilib -iother test/test-asterix.hs"

# run tests
runhaskell -Wall -ilib -itest test/test-asterix.hs
```
