#!/bin/bash -eu
exec agda-pkg -i. -pstdlib -pcrypto-agda/agda-nplib -ilib explore.agda
