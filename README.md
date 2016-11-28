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


## Tests

Quelques tests non exhaustifs permettant de vérifier la véracité du générateur

On bloque le pion 1 (pos 3) entre les pions 0 et 2 puis on essaie de mettre le pion 3 dans le coin avec 1 (pos 2) ce qui est impossible
```
N1 N2 N1 C1 00 00 00 00
```

Message affiché :
```
unsat
```


On bloque le pion 1 (pos 3) entre les pions 0 et 2 puis on essaie de mettre le pion 3 au SW (ce qui est possible)
```
N1 N2 N1 SW 00 00 00 00
```

Solution proposée :
```
  (define-fun p1_3 () Bool
    true)
--
  (define-fun p0_2 () Bool
    true)
--
  (define-fun p4_1 () Bool
    true)
--
  (define-fun p5_0 () Bool
    true)
--
  (define-fun p7_6 () Bool
    true)
--
  (define-fun p3_5 () Bool
    true)
--
  (define-fun p2_4 () Bool
    true)
--
  (define-fun p6_7 () Bool
    true)
```


PS : Loupiac + foie gras FTW
PPS : Coucou il est 1h22
PPPS : R2i <3