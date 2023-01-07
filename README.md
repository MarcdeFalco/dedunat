# Dedunat : assistant de preuve minimaliste pour la déduction naturelle

Programme de MPI/MP-option info.

## Compilation

Cela utilise la même interface terminal que `utop`, donc si `utop` est
installé, vous avez les dépendances et `dune build` suffit.

## Utilisation

Il s'agit d'une boucle interactive où on peut lancer des commandes (les
mots-clés ne sont pas sensibles à la casse) :

* `Prove formule` lance la preuve de la formule
* `Qed` termine la preuve en cours si elle est bien achevée
* `Print affiche la preuve, qu'elle soit achevée ou non, en ascii.
* `LaTeX` affiche la preuve, qu'elle soit achevée ou non, en LaTeX avec 
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
> prove A /\ B -> B /\ A

Goal :  |- (A /\ B) -> (B /\ A)
> intro ->

Goal : A /\ B |- B /\ A
> intro /\

Remaining Goal : A /\ B |- A
Goal : A /\ B |- B
> elim /\ right A

Remaining Goal : A /\ B |- A
Goal : A /\ B |- A /\ B
> axiom

Goal : A /\ B |- A
> elim /\ left B

Goal : A /\ B |- A /\ B
> axiom

No more goals to prove. Print or Qed.
> print
    ----------------ax      ----------------ax
     A /\ B |- A /\ B        A /\ B |- A /\ B
  ------------------/\ed  ------------------/\eg
       A /\ B |- B             A /\ B |- A
 ----------------------------------------------/\i
                 A /\ B |- B /\ A
-------------------------------------------------->i
               |- (A /\ B) -> (B /\ A)
No more goals to prove. Print or Qed.
> qed

Nothing to prove.
>
```
