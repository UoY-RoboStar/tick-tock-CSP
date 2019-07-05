theory Finite_Linear_Pri_Laws

imports
  Finite_Linear_Pri
begin

lemma pri_idem:
  "Pri p (Pri p P) = Pri p P"
  unfolding Pri_def apply auto
  using prirel_trans apply blast
  using prirel_decompose by blast

lemma pri_IntChoice_dist:
  "Pri p (P \<sqinter>\<^sub>\<F>\<^sub>\<L> Q) = (Pri p P) \<sqinter>\<^sub>\<F>\<^sub>\<L> (Pri p Q)"
  unfolding Pri_def IntChoice_def by auto

lemma pri_Prefix_eq_Prefix_pri:
  shows "Pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) = (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> (Pri p P))"
  unfolding Prefix_def Pri_def prefixH_def apply auto
         apply (simp add: prirel_rhs_singleton_iff)
        apply (metis fltrace.exhaust pri.simps(1) pri.simps(3) priacc.simps(1))
       apply (meson prirel_cons_imp_exists)
      apply (meson prirel_cons_bullet_iff_exists)
     apply force
    apply force
   apply (metis prirel_cons_iff_exists)
  by (metis prirel_cons_iff_exists)

lemma prirel_ExtChoice_extends:
  assumes "b <\<^sup>*p a"
  shows "(\<exists>A B X. pri p R X \<and> ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)) = (\<exists>A. pri p R A \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P))"
  using assms unfolding Prefix_def apply (safe, simp_all)
                     apply auto[4]
                  apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  apply (metis (no_types, lifting) partialorder.dual_order.strict_implies_order preirelacc_a_removed prirel_rhs_singleton_iff prirel_singleton_set_iff prirelacc.simps(2))
                 apply (metis prirel_cons_bullet_iff_exists some_higher_not_maximal)   
                apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
                 apply (metis (no_types, lifting) partialorder.dual_order.strict_implies_order preirelacc_a_removed prirel_rhs_singleton_iff prirel_singleton_set_iff prirelacc.simps(2))
               apply (simp_all add: prirel_cons_bullet_iff_exists some_higher_not_maximal)
 apply blast apply safe
                 apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
             apply (metis (no_types, lifting) partialorder.dual_order.strict_implies_order preirelacc_a_removed prirel_rhs_singleton_iff prirel_singleton_set_iff prirelacc.simps(2))
            apply (metis prirel_rel_less_eq_twoset)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI) apply auto[1]
            apply (simp add: prirel_rel_less_eq_twoset)
  using prirel_rel_less_eq_twoset apply fastforce
                   apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
                  apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  apply (simp_all add: prirel_cons_bullet_iff_exists some_higher_not_maximal)
             apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
            apply (metis prirel_cons_also_prirel)
  apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  
          apply (metis prirel_cons_also_prirel)+
     apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
     apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
    apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
  apply (cases R, auto)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI) apply auto[1]
    apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI) apply auto[1]
    apply (rule_tac x="([{b,a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI) apply auto[1]
   apply (simp_all add: prirel_cons_iff_exists_less_eq_twoset prirel_cons_imp_exists)
  by (metis ExtChoiceH.simps(3) ExtChoiceH_sym acceptance_event acceptance_set aunion.simps(2) prirel_cons_bullet_iff_exists)

lemma pri_ExtChoice_two_prefixes:
  assumes "b <\<^sup>*p a" "FL1 P"
  shows "Pri p ((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q))
        =
        Pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
proof -
  have "((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q))
      =
      {X| X A B. ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)}"
    unfolding ExtChoice_def by auto
  then have "Pri p ((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q))
      =
      {R|R A B X. pri p R X \<and> ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)}"
    unfolding Pri_def by auto
  also have "... = {R|R A. pri p R A \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)}"
    using assms(1)
    by (simp add: prirel_ExtChoice_extends)
  also have "... = Pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
    unfolding Pri_def by auto 
  then show ?thesis using calculation 
    by auto
qed

lemma
  assumes "\<not>a <\<^sup>*p b" "\<not>b <\<^sup>*p a"
  shows "Pri p ((a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> P))
        =
        Pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<box>\<^sub>\<F>\<^sub>\<L> Pri p (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
  using assms unfolding ExtChoice_def Pri_def apply auto
  oops

end