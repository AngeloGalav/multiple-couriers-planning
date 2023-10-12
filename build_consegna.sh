#!/bin/bash

echo "Initiating consegna building..."
mkdir models
cp SMT MIP MAP SAT CP models
cp

# run python scripts?

tar -czvf CDMO_Proj_GalavottiAngelo_FreddiDavide_PalliNicola.tar.gz models res Dockerfile instance
rm -rf models
echo "All done!"