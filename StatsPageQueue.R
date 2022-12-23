require(ggplot2)
require(dplyr)
require(tidyr)

actions <- read.csv(header = TRUE, sep = "#", file = "./StatsPageQueue_actions.csv")
actions$Group <- paste(actions$Mode, actions$View, sep = "_")

acts <- actions %>%
  group_by(Group, Mode, View) %>%
  summarise_all(mean) %>%
  pivot_longer(cols=6:23, names_to = "Action", values_to = "Mean") %>%
  ggplot(aes(x=Group, fill=Action, y=Mean)) +
  geom_bar(stat="identity") +
  theme(axis.text.x = element_text(angle = 90, vjust = 0.5, hjust=1))

###### 

trials <- actions %>%
  ggplot(aes(x = Id, y = Trials, color=Group)) +
  geom_point()

require(gridExtra)
grid.arrange(acts, trials, ncol=1)
