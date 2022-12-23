PageQueue
================
Markus A Kuppe
(2022-12-23)

- <a href="#q-learning" id="toc-q-learning">Q-Learning</a>

## Q-Learning

Left plot shows the average (mean) number of `A`-steps per trace with
`A` a sub-action of the next-state relation. The right plots show the
number of times (`trials`) over time (x-axis) the TLC’s simualtor
samples sub-actions to generate one of more successor states. The plot
indicates if reinforcement learning (RL) learned action enablement (it
didn’t). `w3` indicates that the spec was simulated for three processes.
When omitted, the spec was simulated for ten processes. The sub-label
`pc` indicates that the TLC view included the `pc` variable. No labels
indicates that the formula `Range(pc)` was used as the TLC view. The `r`
label shows the reward.

This is a PlusCal spec modeling a lock-free relaxed queue algorithm. We
don’t model failure, which is why action enablement largely depends on
the value of the `pc` variable alone. The spec has 55 action with three
processes and 167 with 10, respectively. TLC generated 3000 traces of
length 100 for each configuraion.

- random: TLC’s simulator samples sub-actions uniformly at random.
- rl: TLC’s simulator samples sub-actions according to the Q-Learning
  algorithm in [“Learning-based Controlled Concurrency
  Testing”](https://www.microsoft.com/en-us/research/publication/learning-based-controlled-concurrency-testing/).
  The Q-Learning hash `H` is calculated from the spec’s `pc` variable or
  from `Range(pc)` of the current state. The Q-Learning state-space is
  `A x H`, where `A` is the set of sub-actions of the next-state
  relation and `H` is the set of TLA+ fingerprints.
- rlaction: TLC’s simulator samples sub-actions according to the Q-table
  and the (Java) hashCode value of the current action. In other words,
  the TLA+ states are excluded from Q-Learning. The Q-Learning
  state-space is `A x A`, where `A` is the set of sub-actions of the
  next-state relation.

Note that wallclock time of random exploration is much lower than for
RL. Optimizations such as caching the TLA+ fingerprints are possible,
but not implemented yet.

![](README_files/figure-gfm/unnamed-chunk-1-1.png)<!-- -->

#### README.md is generated from README.Rmd on a host with all libraries installed via:

``` shell
Rscript -e "rmarkdown::render('README.Rmd')"
```

### Install required libraries and R packages (on macOS) with:

``` shell
brew install pandoc r
Rscript -e "install.packages(c('rmarkdown', 'ggplot2','dplyr', 'here'), repos='http://cran.us.r-project.org')"
```
