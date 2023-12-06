#!/bin/bash

echo "Initiating consegna building..."

if [ -f .submissionignore ]; then
    # Create a temporary tarignore file
    tarignore=".tarignore"
    touch $tarignore

    # read each line from file
    while IFS= read -r line || [[ -n "$line" ]]; do
        echo "$line" >> $tarignore
    done < .submissionignore

    tar czf CDMO_Proj_FreddiDavide_GalavottiAngelo_PalliNicola.tar.gz -X $tarignore *
    
    rm $tarignore
else
    tar czf CDMO_Proj_FreddiDavide_GalavottiAngelo_PalliNicola.tar.gz *
fi

echo "Created archive: CDMO_Proj_FreddiDavide_GalavottiAngelo_PalliNicola.tar.gz"
