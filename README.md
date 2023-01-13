# Dedunat : assistant de preuve minimaliste pour la déduction naturelle

Programme de MPI/MP-option info.

## Compilation

Cela utilise la même interface terminal que `utop`, donc si `utop` est
installé, vous avez les dépendances et `dune build` suffit.

Pour bien gérer l'unicode, il faut une version récente d'`OCaml` : >=4.14.

## Utilisation

Il s'agit d'une boucle interactive où on peut lancer des commandes (les
mots-clés ne sont pas sensibles à la casse) :

* `Help` pour l'aide
* `Help connecteur` pour l'aide sur le connecteur
* `Help intro` pour l'aide sur les introductions.
* `Help elim` pour l'aide sur les eliminations.
* `Prove formule` lance la preuve de la formule
* `Qed` termine la preuve en cours si elle est bien achevée
* `Print affiche la preuve, qu'elle soit achevée ou non, en ascii.
* `LaTeX` affiche la preuve, qu'elle soit achevée ou non, en LaTeX avec 
  des commandes compatibles avec le paquet `busproofs.sty`
* `French` affiche la preuve en français
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
* `Classical` pour appliquer le tiers exclu (avec contexte vide ou non)
* `Peirce` pour appliquer la loi de Peirce (avec contexte vide ou non)
* `Assume` pour admettre le but
* `Undo` pour annuler la dernière règle appliquée
* `Auto` pour appliquer une introduction sur le symbole du nœud racine quand il
  n'y a pas d'arguments

**Remarque** pour l'instant pas de tests de variables libres sur les règles de
pour tout et il existe.

## Unicode

Par défaut, les caractères sont affichés en unicode. On peut lancer
le programme avec `-ascii` comme option pour forcer l'affiche en ascii.

La saisie des symboles peut également se faire :

* soit avec les symboles unicodes : `∧, ∨...`
* soit avec les commandes `LaTeX` : `\land, \lor...`

## Exemple de déroulé

### Preuve de `(¬A ∧ ¬B) → ¬(A ∨ B)` en utilisant l'unicode

```
Use <Tab> to cycle between symbols → ∧ ∨ ¬ ⟂ ∀ ∃
Nothing to prove > Prove (¬A ∧ ¬B) → ¬(A ∨ B)

Goal :  ⊢ (¬A ∧ ¬B) → ¬(A ∨ B) > intro →

Goal : ¬A ∧ ¬B ⊢ ¬(A ∨ B) > intro ¬

Goal : A ∨ B, ¬A ∧ ¬B ⊢ ⟂ > elim ∨ A, B

Remaining Goal : A, A ∨ B, ¬A ∧ ¬B ⊢ ⟂
Remaining Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ ⟂
Goal : A ∨ B, ¬A ∧ ¬B ⊢ A ∨ B > axiom

Remaining Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ ⟂
Goal : A, A ∨ B, ¬A ∧ ¬B ⊢ ⟂ > elim ¬ A

Remaining Goal : A, A ∨ B, ¬A ∧ ¬B ⊢ ¬A
Remaining Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ ⟂
Goal : A, A ∨ B, ¬A ∧ ¬B ⊢ A > axiom

Remaining Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ ⟂
Goal : A, A ∨ B, ¬A ∧ ¬B ⊢ ¬A > elim ∧ left ¬B

Remaining Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ ⟂
Goal : A, A ∨ B, ¬A ∧ ¬B ⊢ ¬A ∧ ¬B > axiom

Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ ⟂ > elim ¬ B

Remaining Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ ¬B
Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ B > axiom

Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ ¬B > elim ∧ right ¬A

Goal : B, A ∨ B, ¬A ∧ ¬B ⊢ ¬A ∧ ¬B > axiom

No more goals to prove. Print/LaTeX or Qed > print
                                                        ───────────────────────────ax                                ───────────────────────────ax      
                                                         A, A ∨ B, ¬A ∧ ¬B ⊢ ¬A ∧ ¬B                                  B, A ∨ B, ¬A ∧ ¬B ⊢ ¬A ∧ ¬B       
                              ─────────────────────ax  ─────────────────────────────∧eg    ─────────────────────ax  ─────────────────────────────∧ed    
                               A, A ∨ B, ¬A ∧ ¬B ⊢ A        A, A ∨ B, ¬A ∧ ¬B ⊢ ¬A          B, A ∨ B, ¬A ∧ ¬B ⊢ B        B, A ∨ B, ¬A ∧ ¬B ⊢ ¬B         
   ──────────────────────ax  ─────────────────────────────────────────────────────────¬e  ─────────────────────────────────────────────────────────¬e   
    A ∨ B, ¬A ∧ ¬B ⊢ A ∨ B                      A, A ∨ B, ¬A ∧ ¬B ⊢ ⟂                                        B, A ∨ B, ¬A ∧ ¬B ⊢ ⟂                      
  ──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────∨e  
                                                                   A ∨ B, ¬A ∧ ¬B ⊢ ⟂                                                                   
 ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────¬i 
                                                                   ¬A ∧ ¬B ⊢ ¬(A ∨ B)                                                                   
──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────→i
                                                                 ⊢ (¬A ∧ ¬B) → ¬(A ∨ B)                                                                 
No more goals to prove. Print/LaTeX or Qed >
```

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

### Preuve de `(-]y.\-/x.R(x,y)) -> \-/x.-]y.R(x,y)`

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

