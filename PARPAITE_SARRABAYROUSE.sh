# Fichier : PARPAITE_SARRABAYROUSE.sh
# Date de dernière édition : dimanche 27 novembre
# Auteurs : PARPAITE Thibault, SARRABAYROUSE Alexis
# Description : Script générant le code Z3 permettant d'implémenter le jeu facetious pelican
# Dépot Github : https://github.com/basketteur-33/EIRB-I1-S5-Projet-logiqueEtPreuve


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


# verification_contrainte
# E :
# $1 = Contrainte
# $2 = Position
# S : vide, arrete l'execution du script si une contrainte passée en paramètre est invalide
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



#######################
# Contraintes simples #
#######################

# contrainte_XX
# E : $1 = pion_i
# S : vide, affiche l'assertion correspondante

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



#########################
# Contraintes complexes #
#########################

# contrainte_complexe
# E :
# $1 = pion_i
# $2 = pion_j
# $3 = type_contrainte
# S : vide, affiche l'assertion correspondante
contrainte_complexe() {
    i=$1
    j=$2
    R=$3

    AND="(and"

    for k in {0..7}
    do
	OR="(or"
	for l in {0..7}
	do
	    $(test_relation_${R} $k $l) # Le code de retour permet de connaitre le resultat du test
	    if [ $? -eq 1 ]
	    then
		OR="$OR p${i}_${l}"
	    fi
	done

	# Cas où on a une implication avec aucune pos valide dans le membre droit : P -> false
	# Par exemple la position 3 pour la relation coin, ou le sud pour les voisins
	if [ "$OR" = "(or" ]
	then
	    AND="$AND (implies p${j}_${k} false)" 
	else
	    AND="$AND (implies p${j}_${k} $OR))"
	fi
    done

    echo "(assert $AND))"
}


# test_relation_N
# E : k, l (deux positions)
# S : retourne 1 si les positions sont sur la meme face et adjacentes, 0 sinon
test_relation_N() {
    k=$1
    l=$2

    if [[ (($k -eq 0) && ($l -eq 1)) ||              # Voisins au N
	  (($k -eq 1) && ($l -eq 0)) ||              # Voisins au N
	  (($k -eq 2 || $k -eq 4) && ($l -eq 3)) ||  # Voisins à l'E
	  (($k -eq 3) && ($l -eq 2 || $l -eq 4)) ||  # Voisins à l'E
	  (($k -eq 6) && ($l -eq 7)) ||              # Voisins à l'W
	  (($k -eq 7) && ($l -eq 6)) ]]              # Voisins à l'W
    then
	return 1
    else
	return 0
    fi
}



# test_relation_F
# E : k, l (deux positions)
# S : retourne 1 si les positions sont sur deux faces opposées, 0 sinon
test_relation_F() {
    k=$1
    l=$2

    if [[ (($k -eq 0 || $k -eq 1) && ($l -eq 5)) ||                          # Si k est au N alors l est au S
	  (($k -eq 5) && ($l -eq 0 || $l -eq 1)) ||                          # Si k est au S alors l est au N
	  (($k -eq 6 || $k -eq 7) && ($l -eq 2 || $l -eq 3 || $l -eq 4)) ||  # Si k est à l'W alors l est à l'E
	  ((k -eq 2 || $k -eq 3 || $k -eq 4) && ($l -eq 6 || $l -eq 7))  ]]  # Si k est à l'E alors l est à l'W
    then
	return 1
    else
	return 0
    fi
}


# test_relation_C
# E : k, l (deux positions)
# S : retourne 1 si les positions sont dans un meme coin, 0 sinon
test_relation_C() {
    k=$1
    l=$2

    if [[ ($k -eq 1 && $l -eq 2) || # Coin 1-2
	  ($k -eq 2 && $l -eq 1) || # Coin 2-1
	  ($k -eq 4 && $l -eq 5) || # Coin 4-5
	  ($k -eq 5 && $l -eq 4) || # Coin 5-4
	  ($k -eq 5 && $l -eq 6) || # Coin 5-6
	  ($k -eq 6 && $l -eq 5) || # Coin 6-5
	  ($k -eq 7 && $l -eq 0) || # Coin 7-0
	  ($k -eq 0 && $l -eq 7) ]] # Coin 0-7
    then
	return 1
    else
	return 0
    fi
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
	    contrainte_complexe $pion_i $pion_j $type_contrainte
	else
	    # Contrainte simple
	    verification_contrainte $1 $pion_i
	    contrainte_$1 $pion_i
	fi

	pion_i=$(($pion_i+1))
	shift
    done
fi
