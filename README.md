# TP: Heidi

![Heidi Movie](https://www.ecranlarge.com/uploads/image/000/608/original-639065-961.jpg)

[Heidi](http://fr.wikipedia.org/wiki/Heidi_(roman)) est joyeuse :
Peter va lui faire découvrir comment diriger son troupeau de chèvres !
Pour cela, ils sont aidés par le chien de berger Tita.
Cependant, alors qu'Heidi ne parle que le romanche, Tita ne comprend qu'un langage sifflé.
Vous écrirez dans ce TP des traducteurs, leur permettant de communiquer.
Vous donnerez la syntaxe abstraite et la sémantique à la fois sous forme de règles d'inférences,
et sous forme de code Swift ou Prolog.
Le code devra bien entendu être commenté et testé.

Tita a été bien dressée,
et comprend les sifflets standards.
Leur description est [disponible ici](http://www.bordercollie-fr.net/autravail/sifflet.php),
accompagnée d'enregistrements sonores.
Les différents ordres et leur traduction en romanche (traduction très incertaine, corrections bienvenues),
et en sifflets sont donnés dans la table ci-dessous.
Un séance de travail avec le chien est une séquence d'ordres séparés par des pauses.


| Ordre                               | Traduction  | Sifflet                           |
|-------------------------------------|-------------|-----------------------------------|
| Amène le troupeau vers moi          | deponer     | Court -- Court                    |
| Contourne le troupeau par la droite | dretg       | Whee -- Who                       |
| Contourne le troupeau par la gauche | sanester    | Wheet -- Wheeo                    |
| Écarte-toi du troupeau              | davent      | Wheet -- Wheeo -- Wheet -- Wheet  |
| Ramène les animaux derrière toi     | davos       | Who -- Hee -- Who                 |
| Ralentis à l'approche du troupeau   | plaun       | Hee -- Hee -- Hee -- Hee          |
| Reviens                             | returnar    | Whee -- Whee -- Wheet             |
| Stop                                | sa fermar   | Long                              |

# Syntaxe Abstraite

## De Heidi

Définissez le langage que peut utiliser Heidi pour donner des ordres.
Ce langage reconnaît des successions d'ordres donnés en romanche.


# De Tita

Définissez le langage que peut comprendre Tita.
Un ordre est donc composé d'une séquence de coups de sifflet.
Entre chaque ordre, il est nécessaire de faire une pause, que vous devez représenter.
Une séance de travail est donc une succession de coups de sifflets et de pauses.

# Sémantique

L'informatique peut aider Heidi et Tita !
En effet, Heidi dispose d'un smartphone.
Nous souhaitons créer une application de traduction des ordres que veut donner Heidi
vers les coups de sifflets qu'elle doit exécuter.
Pour cela, nous écrivons une sémantique pour le langage de Heidi,
qui traduit les ordres dans le langage de Tita.

## Heidi vers Tita

Donnez la sémantique permettant de traduire les ordres de Heidi en ordres pour Tita.

## Tita vers Heidi

Donnez la sémantique permettant de traduire les ordres de Tita en ordres pour Heidi.

# Optimisation

En bonne informaticienne, Heidi se demande pourquoi autant de coups de sifflets différents
sont utilisés, alors que seuls huit ordres existent.
Connaissant bien le binaire, elle sait que des séquences utilisant deux coups de sifflets différents
suffiraient.

Cependant, elle préfère se limiter à trois coups de sifflets distincts.
Se fiant à l'expérience du chevrier Peter, elle dresse de nouveau Tita
à apprendre les ordres décrits ci-dessous.

| Ordre         | Sifflets                    |
|---------------|-----------------------------|
| deponer       | Wheeo -- Hee -- Wheet       |
| dretg         | Hee -- Wheet                |
| sanester      | Wheet -- Wheeo              |
| davent        | Wheet -- Hee -- Wheet       |
| davos         | Wheet -- Wheeo -- Wheet     |
| plaun         | Wheet -- Wheeo -- Wheeo     |
| returnar      | Wheeo -- Wheet              |
| sa fermar     | Wheeo -- Wheeo              |

## Heidi vers Tita

Donnez la sémantique de traduction des ordres en romanche vers les ordres en sifflets.

## Tita vers Heidi

Donnez la sémantique de traduction des ordres en sifflets vers les ordres en romanche.

## Preuve

Prouvez que les ordres donnés en romanche par Heidi sont bien executés par Tita,
c'est-à-dire que la traduction romanche vers sifflets vers romanche
retourne le programme d'origine.

## Accélération

Au bout de quelques jours à diriger Freyja,
Heidi prend confiance et réduit de plus en plus les pauses entre ses ordres.
Arrive le moment où elle supprime totalement ces pauses.

Évaluez (romanche vers sifflets vers romanche) le programme suivant :

* plaun
* dretg
* plaun
* deponer
* sa fermar

Que remarquez-vous ?

## Problèmes

Est-il possible d'obtenir la liste de tous les problèmes possibles ?
Si non, pourquoi ? Si oui, comment (et donnez alors le code le permettant) ?

![Heidi Movie](https://www.letemps.ch/sites/default/files/styles/lt_article_cover/public/media/2016/02/02/file6o9gy7gfina16ntcshsz.jpg?itok=GcUNmRYv)

# Grade

* Have you done something? yes
* Does your code compile or run? yes
* Do your tests succeed? yes
* Have you defined tests? yes
* Have you done the proof? yes
* Have you given all the problems? yes
* Have you written the semantics as inference rules? yes, but with errors
* Have you implemented the semantics? yes

| Grade |
| ----- |
|  5.5  |
