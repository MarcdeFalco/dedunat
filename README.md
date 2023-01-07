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
    * `Intro \/ left/right` pour l'opérande à préserver
    * `Intro \-/ x` pour introduire un pour tout en faisant une
      alpha-conversion vers x de la variable liée
    * `Intro -] t` pour une introduction de il existe en remplaçant la variable
      liée par le terme `t`
* `Elim operateur args` pour appliquer une règle d'élimination
    * `Elim -> A` pour appliquer la règle sur `G |- B` en utilisant `A -> B`
    * `Elim ~ A` pour appliquer la règle sur `A` et `~A`
    * `Elim /\ left/right f` pour passer de `g` à `g /\ f` si `left`, et `f /\ g`
      si `right`
    * `Elim _|_` n'a pas d'arguments
    * `Elim \/ A, B` pour faire une disjonction sur `A \/ B`
    * `Elim \-/ x t` pour éliminer un pour tout en passant de `|- f` à `|- f[x\t]`
    * `Elim -] x f` pour éliminer un il existe en faisant apparaitre `-]x.f`
* `Axiom` pour appliquer une règle axiome
* `Undo` pour annuler la dernière règle appliquée

**Remarque** pour l'instant pas de tests de variables libres sur les règles de
pour tout et il existe.

## Exemple de déroulé

### Preuve de `A /\ B -> B /\ A`
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

### Preuve de `(\-/x.P(x)) -> -]x.P(x)`

```
Nothing to prove.
> prove (\-/x.P(x)) -> -]x.P(x)

```
Nothing to prove.
> prove (\-/x.P(x)) -> -]x.P(x)

Goal :  |- (\-/x. P(x)) -> (-]x. P(x))
> intro ->

Goal : \-/x. P(x) |- -]x. P(x)
> intro -] x

Goal : \-/x. P(x) |- P(x)
> elim \-/ x x

Goal : \-/x. P(x) |- \-/x. P(x)
> axiom

No more goals to prove. Print/LaTeX or Qed.
> print
    ------------------------ax
     \-/x. P(x) |- \-/x. P(x)
  --------------------------\-/e
        \-/x. P(x) |- P(x)
 -------------------------------]i
      \-/x. P(x) |- -]x. P(x)
---------------------------------->i
   |- (\-/x. P(x)) -> (-]x. P(x))
No more goals to prove. Print/LaTeX or Qed
```

> prove (-]y.\-/x.R(x,y)) -> \-/x.-]y.R(x,y)

Goal :  |- (-]y. \-/x. R(x, y)) -> (\-/x. -]y. R(x, y))
> intro ->

Goal : -]y. \-/x. R(x, y) |- \-/x. -]y. R(x, y)
> intro \-/ x

Goal : -]y. \-/x. R(x, y) |- -]y. R(x, y)
> intro -] y

Goal : -]y. \-/x. R(x, y) |- R(x, y)
> elim \-/ x x

Goal : -]y. \-/x. R(x, y) |- \-/x. R(x, y)
> elim -] y \-/x.R(x,y)

Remaining Goal : \-/x. R(x, y), -]y. \-/x. R(x, y) |- \-/x. R(x, y)
Goal : -]y. \-/x. R(x, y) |- -]y. \-/x. R(x, y)
> axiom

Goal : \-/x. R(x, y), -]y. \-/x. R(x, y) |- \-/x. R(x, y)
> axiom

No more goals to prove. Print/LaTeX or Qed.
> print
       ----------------------------------------ax  --------------------------------------------------ax
        -]y. \-/x. R(x, y) |- -]y. \-/x. R(x, y)    \-/x. R(x, y), -]y. \-/x. R(x, y) |- \-/x. R(x, y)
      -------------------------------------------------------------------------------------------------]e
                                      -]y. \-/x. R(x, y) |- \-/x. R(x, y)
    ---------------------------------------------------------------------------------------------------\-/e
                                         -]y. \-/x. R(x, y) |- R(x, y)
   --------------------------------------------------------------------------------------------------------]i
                                       -]y. \-/x. R(x, y) |- -]y. R(x, y)
 ----------------------------------------------------------------------------------------------------------\-/i
                                    -]y. \-/x. R(x, y) |- \-/x. -]y. R(x, y)
--------------------------------------------------------------------------------------------------------------->i
                                 |- (-]y. \-/x. R(x, y)) -> (\-/x. -]y. R(x, y))

No more goals to prove. Print/LaTeX or Qed.
```

