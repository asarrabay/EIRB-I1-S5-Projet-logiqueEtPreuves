#!/bin/bash


# Fonction

usage() {
    echo "usage: $0 c0 c1 ... c7"
    echo "cX doit représenter une contrainte : 00, NS,  EW, etc."
    exit 1
}


# Ensemble des positions possibles pour chaque pion
declaration_variables_propositionnelles() {
    for i in {0..7}
    do
	for j in {0..7}
	do
	    echo "(declare-const p${i}_${j} Bool)"
	done
    done
}


# Chaque pion est sur au moins une position
placement_1() {
    AND="(and"
    for i in {0..7}
    do
	OR="(or"
	for j in {0..7}
	do
	    OR="$OR p${i}_${j}"
	done
	AND="$AND $OR)"
    done

    echo "(assert $AND))" 
}


# Chaque position est occupée par au plus un pion
placement_2() {
    AND1="(and"
    for i in {0..7}
    do
	for j in {0..7}
	do
	    
	    # On réalise une des implications
	    AND2="(and"
	    for k in {0..7}
	    do
		if [ $k -ne $i ]
		then
		    AND2="$AND2 (not p${k}_${j})"
		fi
	    done

	    IMPLIES="(implies p${i}_${j} $AND2))"
	    AND1="$AND1 $IMPLIES"
	done
    done

    echo "(assert $AND1))"	    
}


# $1 = Code de la contrainte
# $2 = Position traitée
verification_contrainte() {
    for i in 00 NS EW SW NE Nj Fj Cj
    do
	if [ $i = $1 ]
	then
	    return
	fi
    done

    echo "Contrainte inconnue en position $2"
    echo "Liste des contraintes disponibles : 00 NS EW SW NE Nj Fj Cj"
    exit 1
}


contrainte_00() {
    echo "TODO 00"
}


contrainte_NS() {
    echo "TODO NS"   
}


contrainte_EW() {
    echo "TODO EW"
}


contrainte_SW() {
    echo "TODO SW"
}


contrainte_NE() {
    echo "TODO NE"
}


contrainte_Nj() {
    echo "TODO Nj"
}


contrainte_Fj() {
    echo "TODO Fj"
}


contrainte_Cj() {
    echo "TODO Cj"
}


# Boucle principale (main)

if [ $# -ne 8 ]
then
    usage
else
    declaration_variables_propositionnelles

    # Assertions définissant la notion de placement
    placement_1
    placement_2

    # On parcourt l'ensembles des pions 
    # Et pour chacun d'eux on ajoute l'assertion correspondant à leur contrainte
    pion_i=0
    while [ $# -gt 0 ]
    do
	verification_contrainte $1 $pion_i
	contrainte_$1

	pion_i=$(($pion_i+1))
	shift
    done
fi
    






    
