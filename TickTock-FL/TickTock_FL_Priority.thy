theory
  TickTock_FL_Priority
imports
  "TickTock.TickTock_Prioritise"
  TickTock_Max_FL
  "FL.Finite_Linear_Pri"
  "FL.Finite_Linear_Pri_Laws"
begin

lemma pri_univ_dist:
  "Pri p (\<Union> X) = \<Union>{Pri p x|x. x \<in> X}"
  unfolding Pri_def by auto





end