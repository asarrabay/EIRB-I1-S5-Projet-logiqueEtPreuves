# EIRB-I1-S5-Projet-logiqueEtPreuve
PARPAITE Thibault
SARRABAYROUSE Alexis

Ce dépot github contient le premier projet de l'UE logique et preuves de programme (I1 - S1).
Le but est de modéliser le jeu facetious pelican en utilisant la logique propositionnelle puis de le résoudre à l'aide du solveur Z3.

## Générer le fichier .smt2

Placez vous à la répertoire du projet, puis lancez le script
```
./PARPAITE_SARRABAYROUSE.sh NS F0 C1 NS NE 00 00 00 > facetious_pelican.smt2
```

On rajoute les lignes permettant de vérifier la solvabilité du problème, et récupérer le modèle
```
echo -e "(check-sat)\n(get-model)" >> facetious_pelican.smt2
```

## Exécution du solveur Z3 

Pour lancer la résolution du problème
```
./z3 -smt2 facetious_pelican.smt2
```

Pour un affichage plus agréable (voir directement les positions) avec grep
```
./z3 -smt2 facetious_pelican.smt2 | grep true -B 1
```


PS : Loupiac + foie gras FTW  
PPS : Coucou il est 1h22  
PPPS : R2i <3
