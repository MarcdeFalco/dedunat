# Dedunat : assistant de preuve minimaliste pour la déduction naturelle

Programme de MPI/MP-option info.

## Compilation

Cela utilise la même interface terminal que `utop`, donc si `utop` est
installé, vous avez les dépendances et `dune build` suffit.

## Utilisation

Il s'agit d'une boucle interactive où on peut lancer des commandes :

* `Prove formule` lance la preuve de la formule
* `Qed` termine la preuve en cours si elle est bien achevée
* `Print` affiche la preuve, qu'elle soit achevée ou non, en LaTeX avec 
  des commandes compatibles avec le paquet `busproofs.sty`
* `Intro operateur args` pour appliquer une règle d'introduction
    * Pas d'arguments pour `/\`, `->` et `~`
    * `left` ou `right` pour `\/`
* `Elim operateur args` pour appliquer une règle d'élimination
    * `Elim -> A` pour appliquer la règle sur `G |- B` en utilisant `A -> B`
    * `Elim ~ A` pour appliquer la règle sur `A` et `~A`
    * `Elim /\` n'a pas d'arguments
    * `Elim _|_` n'a pas d'arguments
    * `Elim \/ A, B` pour faire une disjonction sur `A \/ B`
* `Axiom` pour appliquer une règle axiome
* `Undo` pour annuler la dernière règle appliquée


## Exemple de déroulé

```
Nothing to prove.
> Prove (~A \/ B) -> (A -> B)

Goal :  |- (~A \/ B) -> (A -> B)
> Intro ->

Goal : ~A \/ B |- A -> B
> Intro ->

Goal : A, ~A \/ B |- B
> Elim \/ ~A , B

Remaining Goal : ~A, A, ~A \/ B |- B
Remaining Goal : B, A, ~A \/ B |- B
Goal : A, ~A \/ B |- ~A \/ B
> Axiom

Remaining Goal : B, A, ~A \/ B |- B
Goal : ~A, A, ~A \/ B |- B
> Intro _|_

Remaining Goal : B, A, ~A \/ B |- B
Goal : ~A, A, ~A \/ B |- _|_
> Elim ~ A

Remaining Goal : ~A, A, ~A \/ B |- ~A
Remaining Goal : B, A, ~A \/ B |- B
Goal : ~A, A, ~A \/ B |- A
> Axiom

Remaining Goal : B, A, ~A \/ B |- B
Goal : ~A, A, ~A \/ B |- ~A
> Axiom

Goal : B, A, ~A \/ B |- B
> Axiom

No more goals to prove. Print or Qed.
> Qed
```
