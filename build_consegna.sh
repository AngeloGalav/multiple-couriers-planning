#!/bin/bash

echo "Initiating consegna building..."
mkdir models
cp -r SMT MIP MAP SAT CP models

# run python scripts?

tar -czvf CDMO_Proj_GalavottiAngelo_FreddiDavide_PalliNicola.tar.gz models res Dockerfile instances docker_bins
rm -rf models
echo "All done!"