# Projet de compilateur dans le cadre du cours d'interpretation compilation

<br /><br /><br />

# Instructions de compilation et de lancement des test
<br />La commande ci dessous commande permet d'executer le projet de rajouter le contenu de l'execution puis de le lancer dans spim:<br />
``` dune exec projet --profile release ./tests/<nom_du_test>.test > prog.asm && spim load "prog.asm"  ```

<br />Pour la compilation simple: <br />```dune build```<br /><br /><br />

 <br />Pour l'execution du programme sur un test:<br /> ``` dune exec projet --profile release ./tests/<nom_du_test>.test```<br /><br /><br />

<br />Si la commande dune n'est pas trouvée: <br />```eval $(opam env)```<br /><br /><br />

# Description du langage et presentation de ses fonctionnalités.

Le langage que j'ai développé est un langage sur la base du langage C mais avec quelques différences :
Les conditions fonctionnent avec une syntaxe If Then Else sans avoir besoin d'accolades.
Les boucles fonctionnent avec une syntaxe While Do sans avoir besoin d'accolades.
Les fonctionnalités sont les suivantes : Gestion des entiers, des booléens, des variables, des appels de fonction , des déclarationsde variables, des assignations, des retours, des conditions et enfin des boucles.<br />
##### Projet Réalisé par Abdelrahman Fliou
<br /><br /><br />


# Compiler Project for the Compilation and Interpretation Course



<br /><br /><br />


# Compilation and Test Launch Instructions
<br />The following command executes the project, adds the execution content, and launches it in spim:<br />
``` dune exec projet --profile release ./tests/return.test > prog.asm && spim load "prog.asm"  ```
<br />For simple compilation: <br />```dune build```<br /><br /><br />

 <br />To execute the program on a test:<br /> ``` dune exec projet --profile release ./tests/<nom_du_test>.test```<br /><br /><br />

<br />If the dune command is not found: <br />```eval $(opam env)```<br /><br /><br />

# Language Description and Presentation of Its Features

The language I developed is based on the C language but with some differences:
Conditions work with an If Then Else syntax without needing braces.
Loops work with a While Do syntax without needing braces.
The features are as follows: integer, boolean, variable, function call, variable declaration, assignment, return, condition, and loop handling.
<br />


##### Project made by Abdelrahman Fliou