^\[\n _TEAction \|-> \[\n(.|\n)*?name \|-> "(?<event>(.)*)"(.|\n)*?Clock \|-> "(?<clock>.*)",\nHost \|-> (?<host>.*),\n disk \|-> (?<disk>.*),\n h \|-> (?<h>.*),\n head \|-> (?<head>.*),\n pc \|-> (?<pc>.*),\n result \|-> (?<result>.*),\n t \|-> (?<t>.*)\n tail \|-> (?<tail>.*)\n\]

----------------------------- MODULE ShiVizLog -----------------------------
\* Open in https://bestchai.bitbucket.io/shiviz/
\*
\* - Filter history from trace in Trace Explorer
\*   (regex not written to handle multiple lines)
\* - Manually delete initial state from trace below
\*   (ShiViz cannot visualize an initial state)


===========================================================================
