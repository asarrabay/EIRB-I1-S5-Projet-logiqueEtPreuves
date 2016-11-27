#!/bin/bash


# Fonction

usage() {
    echo "usage: $0 c0 c1 ... c7"
    echo "cX doit représenter une contrainte : 00, NS,  EW, etc."
    exit 1
}


declaration_variables() {
    for i in 00 NS EW SW NE Nj Fj Cj
    do
	echo "(declare-const $i Bool)"
    done
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
    declaration_variables

    pion_i=0
    while [ $# -gt 0 ]
    do
	verification_contrainte $1 $pion_i
	contrainte_$1

	pion_i=$(($pion_i+1))
	shift
    done
fi
    






    
