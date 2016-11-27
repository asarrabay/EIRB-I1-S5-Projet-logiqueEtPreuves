#!/bin/bash

#############
# Fonctions #
#############

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
	    # Debut : implication, que l'on réalise pour chaque couple (i, j)
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
	    # Fin : implication
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



###############
# Contraintes #
###############

# $1 = pion_i
# $2 = pos_j (pour les contraintes complexes Nj, Fj et Cj)

# "Le pion i peut-etre placé à n'importe quelle position"
# Cela est déjà vérifié par l'assertion placement_1, pas besoin de rajouter une assertion
contrainte_00() {
    return
}


# "Le pion i est au nord (positions 0 et 1) ou au sud (position 5)"
contrainte_NS() {
    echo "(assert (or p$1_0 p$1_1 p$1_5))"  
}


# "Le pion i est à l'est (positions 2, 3 et 4) ou à l'ouest (positions 6 et 7)"
contrainte_EW() {
    echo "(assert (or p$1_2 p$1_3 p$1_4 p$1_6 p$1_7))"  
}


# "Le pion i est au sud (position 5) ou à l'ouest (positions 6 et 7)"
contrainte_SW() {
    echo "(assert (or p$1_5 p$1_6 p$1_7))"
}


# "Le pion i est au nord (positions 0 et 1) ou à l'est (positions 2, 3 et 4)"
contrainte_NE() {
    echo "(assert (or p$1_0 p$1_1 p$1_2 p$1_3 p$1_4))"  
}


contrainte_Nj() {
    echo "Contrainte Nj"
    echo "pion_i = $1"
    echo "pion_j = $2"
}


contrainte_Fj() {
    echo "Contrainte Fj"
    echo "pion_i = $1"
    echo "pion_j = $2"
}


contrainte_Cj() {
    echo "Contrainte Cj"
    echo "pion_i = $1"
    echo "pion_j = $2"
}



############################
# Boucle principale (main) #
############################


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
    # La variable pion_i indique le numéro du pion en cours de traitement
    pion_i=0
    while [ $# -gt 0 ]
    do
	if [[ $1 =~ ^[NFC][0-7]$ ]]
	then
	    # Contrainte complexe
	    type_contrainte=$(echo $1 | cut -c 1)
	    pion_j=$(echo $1 | cut -c 2)
	    contrainte_${type_contrainte}j $pion_i $pion_j
	else
	    # Contrainte simple
	    verification_contrainte $1 $pion_i
	    contrainte_$1 $pion_i
	fi
	
	pion_i=$(($pion_i+1))
	shift
    done
fi
    






    
