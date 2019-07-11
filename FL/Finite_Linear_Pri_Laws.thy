theory Finite_Linear_Pri_Laws

imports
  Finite_Linear_Pri
  Finite_Linear_Tick_Param
  Finite_Linear_Induction
begin

lemma Pri_idem:
  "Pri p (Pri p P) = Pri p P"
  unfolding Pri_def apply auto
  using prirel_trans apply blast
  using prirel_decompose by blast

lemma Pri_IntChoice_dist:
  "Pri p (P \<sqinter>\<^sub>\<F>\<^sub>\<L> Q) = (Pri p P) \<sqinter>\<^sub>\<F>\<^sub>\<L> (Pri p Q)"
  unfolding Pri_def IntChoice_def by auto

lemma Pri_Prefix_eq_Prefix_pri:
  shows "Pri p (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) = (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> (Pri p P))"
  unfolding Prefix_def Pri_def prefixH_def apply auto
         apply (simp add: prirel_rhs_singleton_iff)
       apply (meson prirel_cons_imp_exists)
      apply (meson prirel_cons_bullet_iff_exists)
     apply force
    apply force
   apply (metis prirel_cons_iff_exists)
  by (metis prirel_cons_iff_exists)

lemma pri_singleton_simp [intro]:
  assumes "b <\<^sup>*p a" "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" 
  shows "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{b, a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms by (cases R, auto)

lemma pri_singleton_simp' [intro]:
  assumes "b <\<^sup>*p a" "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{b, a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" 
  shows "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" 
  using assms by (cases R, auto)

lemma pri_acceptance_consFL_simp [intro]:
  assumes "b <\<^sup>*p a" "R pri\<^sub>[\<^sub>p\<^sub>] (([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>)" 
  shows "R pri\<^sub>[\<^sub>p\<^sub>] (([{b, a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>)"
  using assms 
  apply (cases R, auto, case_tac x21, auto)
  apply (case_tac aa, auto)
  by (metis partialorder.less_asym singleton_iff)+

lemma pri_acceptance_consFL_simp' [intro]:
  assumes "b <\<^sup>*p a" "R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>)" 
  shows "R pri\<^sub>[\<^sub>p\<^sub>] (([{b, a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>)"
  using assms 
  apply (cases R, auto, case_tac x21, auto)
  by (case_tac aa, auto)

lemma pri_imp_ExtChoice_extends:
  assumes "b <\<^sup>*p a" "pri p R A" "A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
  shows "\<exists>A B X. pri p R X \<and> ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)"
  using assms unfolding Prefix_def apply (auto)
     apply (rule_tac x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
     apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
    apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
   apply (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)
  apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> \<rho>" in exI, auto)
  by (rule_tac x="\<langle>[{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, auto)

lemma ExtChoiceH_find_refl:
  assumes "ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
  shows "\<exists>A B. ExtChoiceH A B A \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
  using assms ExtChoiceH_triple_refl by blast+

lemma pri_ExtChoice_extends:
  assumes "b <\<^sup>*p a" "pri p R X" "ExtChoiceH A B X" "A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)" "B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)"
  shows "\<exists>A. pri p R A \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P)"
using assms
  proof (induct A B X rule:ExtChoiceH.induct)
    case (1 A B X)
    then show ?case
      apply (cases X, auto)
      apply (cases A, auto, cases B, auto)
      apply (cases B, auto)
       apply (rule_tac x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, simp add:Prefix_def) 
      apply (rule_tac x="\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>" in exI, simp add:Prefix_def)
      using assms by auto
  next
    case (2 A aa B bb X)
    
    have X_split:"X = (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa \<or> X = (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb"
      using 2 by auto

    then show ?case using X_split 2
    proof (auto)
      assume prefixA:"X = (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa"
      then show ?thesis
      proof (cases "acceptance A = \<bullet>")
        case A_bullet:True
        then have "R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
          using 2 prefixA by auto
        then have "R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<and> ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
          using 2 prefixA unfolding Prefix_def by auto
        then show ?thesis by blast
      next
        case A_not_bullet:False
        then have accA:"acceptance A = [{a}]\<^sub>\<F>\<^sub>\<L>"
          using 2 unfolding Prefix_def by auto
        then show ?thesis
          proof (cases "acceptance B = \<bullet>")
            case B_bullet:True
            then have "R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
              using 2 prefixA by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<and> ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
              using 2 prefixA unfolding Prefix_def by auto
            then show ?thesis by blast
          next
            case B_not_bullet:False
            then have "acceptance B = [{b}]\<^sub>\<F>\<^sub>\<L>"
              using 2 unfolding Prefix_def by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] (([{a}]\<^sub>\<F>\<^sub>\<L> \<union>\<^sub>\<F>\<^sub>\<L> [{b}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
              using 2 prefixA accA by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] (([{b,a}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
              by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] (([{a}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
              using 2 prirel_rel_less_eq_twoset
              by (metis A_not_bullet accA amember.simps(2) event_in_acceptance insert_absorb insert_iff insert_not_empty)
            then have "R pri\<^sub>[\<^sub>p\<^sub>] (([{a}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<and> (([{a}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
              using 2 prefixA unfolding Prefix_def by auto
            then show ?thesis by blast
          qed
        qed
    next
      assume prefixB:"X = (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb"
      
      have eventB:"event B = b"
        using 2 unfolding Prefix_def by auto
      then have B_not_maximal:"\<not> maximal(p,event B)"
        using 2
        by (meson some_higher_not_maximal)
    
      then have R_notpri_X:"\<not> R pri\<^sub>[\<^sub>p\<^sub>] X"
      proof (cases "acceptance A = \<bullet>")
        case A_bullet:True
        then have "\<not>R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
          using 2 prefixB B_not_maximal by (cases R, auto)
        then show ?thesis using 2 A_bullet prefixB by auto
      next
        case A_not_bullet:False
        then have accA:"acceptance A = [{a}]\<^sub>\<F>\<^sub>\<L>"
          using 2 unfolding Prefix_def by auto
        then show ?thesis
          proof (cases "acceptance B = \<bullet>")
            case B_bullet:True
            then have "\<not>R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
              using 2 prefixB B_not_maximal by (cases R, auto)
            then show ?thesis using 2 B_bullet prefixB by auto
          next
            case B_not_bullet:False
            then have "acceptance B = [{b}]\<^sub>\<F>\<^sub>\<L>"
              using 2 unfolding Prefix_def by auto
            then have X_eq:"X = (([{b,a}]\<^sub>\<F>\<^sub>\<L>,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
              using 2 prefixB accA by auto
            then have "event B \<notin>\<^sub>\<F>\<^sub>\<L> priacc\<^sub>[\<^sub>p\<^sub>](acceptance ([{b,a}]\<^sub>\<F>\<^sub>\<L>,event B)\<^sub>\<F>\<^sub>\<L>)"
              using B_not_maximal eventB 2 by simp
            then have "\<not>R pri\<^sub>[\<^sub>p\<^sub>] (([{b,a}]\<^sub>\<F>\<^sub>\<L>,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
              using B_not_maximal eventB by auto
            then show ?thesis using X_eq by auto
          qed
        qed
        then show ?thesis using 2 by auto
      qed
  next
    case (3 A B bb X)
    then have X_split:"X = \<langle>A \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B)\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = ((A \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B),event(B))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
      by auto
    then show ?case using X_split 3
    proof (auto)
      assume prefixA:"X = \<langle>A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B\<rangle>\<^sub>\<F>\<^sub>\<L>"
      then show ?thesis
      proof (cases A)
        case acnil
        then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
          using 3 prefixA by auto
        then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
          using 3 prefixA unfolding Prefix_def by auto
        then show ?thesis by blast
      next
        case A_not_bullet:(acset x2)
        then have x2_is_A:"x2 = {a}"
          using 3 prefixA unfolding Prefix_def by auto
        then show ?thesis
        proof (cases "acceptance B = \<bullet>")
            case B_bullet:True
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
              using A_not_bullet 3 prefixA by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
              using 3 prefixA unfolding Prefix_def by auto
            then show ?thesis by blast
          next
            case B_not_bullet:False
            then have "acceptance B = [{b}]\<^sub>\<F>\<^sub>\<L>"
              using 3 unfolding Prefix_def by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{a}]\<^sub>\<F>\<^sub>\<L> \<union>\<^sub>\<F>\<^sub>\<L> [{b}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
              using 3 prefixA A_not_bullet x2_is_A by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{b,a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
              by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
              using 3 by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
              using 3 prefixA unfolding Prefix_def by auto
            then show ?thesis by blast
          qed
        qed
    next
      assume prefixB:"X = (A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb"

      have eventB:"event B = b"
        using 3 unfolding Prefix_def by auto
      then have B_not_maximal:"\<not> maximal(p,event B)"
        using 3
        by (meson some_higher_not_maximal)
    
      then have R_notpri_X:"\<not> R pri\<^sub>[\<^sub>p\<^sub>] X"
      proof (cases "A = \<bullet>")
        case A_bullet:True
        then have "\<not>R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
          using 3 prefixB B_not_maximal by (cases R, auto)
        then show ?thesis using 3 A_bullet prefixB by auto
      next
        case A_not_bullet:False
        then have accA:"A = [{a}]\<^sub>\<F>\<^sub>\<L>"
          using 3 unfolding Prefix_def by auto
        then show ?thesis
          proof (cases "acceptance B = \<bullet>")
            case B_bullet:True
            then have X_eq:"X = ((\<bullet>,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
              using 3 prefixB accA by auto
            then have "\<not>R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
              using 3 prefixB B_not_maximal by (cases R, auto)
            then show ?thesis using 3 X_eq by auto
          next
            case B_not_bullet:False
            then have "acceptance B = [{b}]\<^sub>\<F>\<^sub>\<L>"
              using 3 unfolding Prefix_def by auto
            then have X_eq:"X = (([{b,a}]\<^sub>\<F>\<^sub>\<L>,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
              using 3 prefixB accA by auto
            then have "event B \<notin>\<^sub>\<F>\<^sub>\<L> priacc\<^sub>[\<^sub>p\<^sub>](acceptance ([{b,a}]\<^sub>\<F>\<^sub>\<L>,event B)\<^sub>\<F>\<^sub>\<L>)"
              using B_not_maximal eventB 3 by simp
            then have "\<not>R pri\<^sub>[\<^sub>p\<^sub>] (([{b,a}]\<^sub>\<F>\<^sub>\<L>,event B)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb)"
              using B_not_maximal eventB by auto
            then show ?thesis using X_eq by auto
          qed
        qed
        then show ?thesis using 3 by auto
      qed
  next
    case (4 A aa B X)
    then have X_split:"X = \<langle>acceptance A \<union>\<^sub>\<F>\<^sub>\<L> B\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = ((acceptance(A) \<union>\<^sub>\<F>\<^sub>\<L> B,event(A))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
      by auto
    then show ?case using X_split 4
    proof (auto)
      assume prefixA:"X = \<langle>B \<union>\<^sub>\<F>\<^sub>\<L> acceptance A\<rangle>\<^sub>\<F>\<^sub>\<L>"
      then show ?thesis
      proof (cases B)
        case acnil
        then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
          using 4 prefixA by auto
        then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
          using 4 prefixA unfolding Prefix_def by auto
        then show ?thesis by blast
      next
        case B_not_bullet:(acset x2)
        then have x2_is_A:"x2 = {b}"
          using 4 prefixA unfolding Prefix_def by auto
        then show ?thesis
        proof (cases "acceptance A = \<bullet>")
            case A_bullet:True
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
              using B_not_bullet 4 prefixA by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
              using prefixA unfolding Prefix_def by auto
            then show ?thesis by blast
          next
            case A_not_bullet:False
            then have "acceptance A = [{a}]\<^sub>\<F>\<^sub>\<L>"
              using 4 unfolding Prefix_def by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{b}]\<^sub>\<F>\<^sub>\<L> \<union>\<^sub>\<F>\<^sub>\<L> [{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
              using 4 prefixA B_not_bullet x2_is_A by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{b,a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
              by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
              using 4 by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
              using prefixA unfolding Prefix_def by auto
            then show ?thesis by blast
          qed
        qed
    next
      assume prefixA:"X = (B \<union>\<^sub>\<F>\<^sub>\<L> acceptance A,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa"

      have eventA:"event A = a"
        using 4 unfolding Prefix_def by auto
      
      then show ?thesis
      proof (cases "acceptance A = \<bullet>")
        case A_bullet:True
        then have "R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
          using 4 prefixA
          by (metis aunion.simps(1) unionA_sym)
        then have "R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<and> ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
          using 4 prefixA unfolding Prefix_def by auto
        then show ?thesis by blast
      next
        case A_not_bullet:False
        then have accA:"acceptance A = [{a}]\<^sub>\<F>\<^sub>\<L>"
          using 4 unfolding Prefix_def by auto
        then show ?thesis
          proof (cases "B = \<bullet>")
            case B_bullet:True
            then have "R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
              using 4 prefixA by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<and> ((\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
              using 4 prefixA unfolding Prefix_def by auto
            then show ?thesis by blast
          next
            case B_not_bullet:False
            then have "B = [{b}]\<^sub>\<F>\<^sub>\<L>"
              using 4 unfolding Prefix_def by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] (([{a}]\<^sub>\<F>\<^sub>\<L> \<union>\<^sub>\<F>\<^sub>\<L> [{b}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
              using 4 prefixA accA by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] (([{b,a}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
              by auto
            then have "R pri\<^sub>[\<^sub>p\<^sub>] (([{a}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"
              using 4 prirel_rel_less_eq_twoset
              by (metis A_not_bullet accA amember.simps(2) event_in_acceptance insert_absorb insert_iff insert_not_empty)
            then have "R pri\<^sub>[\<^sub>p\<^sub>] (([{a}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<and> (([{a}]\<^sub>\<F>\<^sub>\<L>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa) \<in> a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P"
              using 4 prefixA unfolding Prefix_def by auto
            then show ?thesis by blast
          qed
        qed
      qed
qed 


lemma prirel_ExtChoice_extends:
  assumes "b <\<^sup>*p a"
  shows "(\<exists>A B X. pri p R X \<and> ExtChoiceH A B X \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P) \<and> B \<in> (b \<rightarrow>\<^sub>\<F>\<^sub>\<L> Q)) = (\<exists>A. pri p R A \<and> A \<in> (a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P))"
  using assms apply auto
   apply (simp add: pri_ExtChoice_extends)
  by (simp add:pri_imp_ExtChoice_extends)

lemma Pri_ExtChoice_two_prefixes:
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

lemma prirelacc_not_in_imp [simp]:
  assumes "priacc\<^sub>[\<^sub>p\<^sub>](A) = Z" "e \<notin>\<^sub>\<F>\<^sub>\<L> A"
  shows "e \<notin>\<^sub>\<F>\<^sub>\<L> Z"
  using assms
  by (cases A, auto)

lemma pri_tickWF:
  assumes "pri p x Z" "tickWF tick Z"
  shows "tickWF tick x"
  using assms by (induct p x Z arbitrary:tick rule:pri.induct, auto)

lemma FLTick0_Pri:
  assumes "FLTick0 tick P"
  shows "FLTick0 tick (Pri p P)"
  using assms unfolding FLTick0_def Pri_def apply auto
  by (simp add: pri_tickWF)

lemma prirel_extend_both_last_null_imp:
  assumes "pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length \<beta> = length \<Gamma>" "a \<in>\<^sub>\<F>\<^sub>\<L> A" "last \<beta> = \<bullet>" "last \<Gamma> = \<bullet>"
  shows "pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct \<beta> \<Gamma> rule:pri.induct, auto)

lemma prirel_extend_both_last_null_imp2:
  assumes "pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length \<beta> = length \<Gamma>" "a \<in>\<^sub>\<F>\<^sub>\<L> A" "last \<beta> = \<bullet>" "last \<Gamma> = \<bullet>" "\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> A  \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> B"
  shows "pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(B,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct \<beta> \<Gamma> rule:pri.induct, auto)

lemma prirel_eq_length_imp_last_member:
  assumes "length xs = length ys" "last xs = \<bullet>" "last ys \<noteq> \<bullet>" "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) ys"
  shows  "\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> x  \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> last ys"
  using assms
proof(induct p xs ys rule:pri.induct)
  case (1 p A Z)
  then show ?case by auto
next
  case (2 p A Z zz)
  then show ?case by auto
next
  case (3 p A aa Z)
  then show ?case by auto
next
  case (4 p A aa Z zz)
  then show ?case by auto
qed
 
lemma pri_FL2:
  assumes "FL2 P" "a \<in>\<^sub>\<F>\<^sub>\<L> A" "pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) Z" "Z \<in> P"
  shows "\<exists>Z. pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z \<and> Z \<in> P"
  using assms
proof (cases "last \<beta> = \<bullet>")
  case True
  then obtain \<Gamma> where pGama:"pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (\<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = Z \<and> length \<beta> = length \<Gamma>"
    using assms
    by (metis Finite_Linear_Model.last.simps(1) acceptance.distinct(1) add_cancel_right_right amember.elims(2) concat_FL_last_not_bullet_absorb last_bullet_then_last_cons length.simps(1) length_cons prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq prirel_cons_eq_length_imp_prirel_acceptances_last_not_bullet prirel_same_length)
  then show ?thesis
  proof (cases "last \<Gamma> = \<bullet>")
    case True
    then show ?thesis 
      by (metis FL2_def pGama assms(1) assms(2) assms(4) concat_FL_last_not_bullet_absorb prirel_extend_both_last_null_imp)
  next
    case False
    then have "\<Gamma> = Z"
      using concat_FL_last_not_bullet_absorb pGama by fastforce
    then have "\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> last \<Gamma>"
      using True pGama False assms(3) prirel_eq_length_imp_last_member by blast
    then have "\<Gamma> = butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>last \<Gamma>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      by (simp add: butlast_last_cons2_FL)
    then have "butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(last \<Gamma>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
      by (metis FL2_def \<open>\<Gamma> = Z\<close> \<open>\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> Finite_Linear_Model.last \<Gamma>\<close> assms(1) assms(2) assms(4))

    have "pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Gamma>"
      using pGama \<open>\<Gamma> = Z\<close> by auto
    then have "pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>last \<Gamma>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      by (simp add: butlast_last_cons2_FL)
    have "length \<beta> = length (butlast \<Gamma>)"
      by (metis butlast_last_cons2_FL pGama rev_rev_butlast strong_less_eq_fltrace_cons_imp_lhs strong_less_eq_fltrace_eq_length strong_less_eq_fltrace_refl)

    then have "pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(last \<Gamma>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using True \<open>\<forall>e. e \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> e \<in>\<^sub>\<F>\<^sub>\<L> Finite_Linear_Model.last \<Gamma>\<close> \<open>pri p (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) (Finite_Linear_Model.butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>Finite_Linear_Model.last \<Gamma>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> assms(2) last_butlast_cons_bullet prirel_extend_both_last_null_imp2
      by (metis bullet_right_zero2)
    then show ?thesis
      using \<open>Finite_Linear_Model.butlast \<Gamma> &\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last \<Gamma>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P\<close> by blast
  qed
next
case False
  then show ?thesis 
    using assms
    by (metis concat_FL_last_not_bullet_absorb)
qed

lemma FL2_Pri:
  assumes "FL2 P"
  shows "FL2 (Pri p P)"
  using assms unfolding FL2_def Pri_def apply auto
  by (simp add: assms pri_FL2)

text \<open>Does Pri distribute through sequential composition in this model?\<close>

lemma prirel_consFL_both_imp:
  assumes "pri p (x &\<^sub>\<F>\<^sub>\<L>y) (s &\<^sub>\<F>\<^sub>\<L> t)" "length x = length s" "last x = \<bullet>" "last s = \<bullet>"
  shows "pri p x s"
  using assms by(induct x s rule:pri.induct, auto)

lemma prirel_consFL_both_imp':
  assumes "pri p x s" "pri p y t" 
  shows "pri p (x &\<^sub>\<F>\<^sub>\<L>y) (s &\<^sub>\<F>\<^sub>\<L> t)" 
  using assms 
proof(induct x s rule:pri.induct)
  case (1 p A Z)
  then show ?case 
  proof (cases "Z = \<bullet>")
    case True
    then show ?thesis using 1 by auto
  next
    case False
    then obtain ZSet where ZSet:"Z = [ZSet]\<^sub>\<F>\<^sub>\<L>"
      by (cases Z, auto)
    have "Finite_Linear_Model.last \<langle>[ZSet \<inter> {a. \<forall>aa. aa \<in> ZSet \<longrightarrow> \<not> a <\<^sup>*p aa}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<noteq> \<bullet>"
      by auto
    then have f1: "\<langle>[ZSet \<inter> {a. \<forall>aa. aa \<in> ZSet \<longrightarrow> \<not> a <\<^sup>*p aa}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> y = \<langle>[ZSet \<inter> {a. \<forall>aa. aa \<in> ZSet \<longrightarrow> \<not> a <\<^sup>*p aa}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using concat_FL_last_not_bullet_absorb by blast
    have "\<langle>[ZSet]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> t = \<langle>[ZSet]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      by (simp add: concat_FL_last_not_bullet_absorb)
    then have "(\<langle>[ZSet \<inter> {a. \<forall>aa. aa \<in> ZSet \<longrightarrow> \<not> a <\<^sup>*p aa}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> y) pri\<^sub>[\<^sub>p\<^sub>] (\<langle>[ZSet]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> t)"
      using f1 by auto
    then show ?thesis using 1 False ZSet by auto
  qed
next
  case (2 p A Z \<sigma>)
  then show ?case by auto
next
  case (3 p A \<rho> Z)
  then show ?case by auto
next
  case (4 p A \<rho> Z \<sigma>)
  then show ?case by auto
qed

lemma prirel_consFL_exists:
  assumes "pri p x (s &\<^sub>\<F>\<^sub>\<L> t)"
  shows "\<exists>y. pri p y s"
  using assms apply(induct x s rule:pri.induct, auto)  
  using pri.simps(1) apply blast+
  by (metis pri.simps(4))+

lemma prirel_consFL_last_bullet_exists:
  assumes "pri p x (s &\<^sub>\<F>\<^sub>\<L> t)" "last s = \<bullet>"
  shows "\<exists>s0 t0. x = s0 &\<^sub>\<F>\<^sub>\<L> t0 \<and> pri p s0 s \<and> pri p t0 t"
  using assms apply(induct x s rule:pri.induct, auto)
  apply (metis bullet_left_zero2 pri.simps(1) priacc.simps(1))
    apply (metis bullet_left_zero2 pri.simps(1) priacc.simps(1))
  by (metis fltrace_concat2.simps(2) pri.simps(4))+

lemma prirel_consFL_last_bullet_exists':
  assumes "pri p (s &\<^sub>\<F>\<^sub>\<L> t) x" "last s = \<bullet>"
  shows "\<exists>s0 t0. x = s0 &\<^sub>\<F>\<^sub>\<L> t0 \<and> pri p s s0 \<and> pri p t t0"
  using assms apply(induct x s rule:pri.induct, auto)
     apply (metis bullet_left_zero2 pri.simps(1) priacc.simps(1))
    apply (metis bullet_left_zero2 pri.simps(1) priacc.simps(1))
  by (metis fltrace_concat2.simps(2) pri.simps(4))+

lemma prirel_not_events:
  assumes "pri p x s" "tick \<notin> events s"
  shows "tick \<notin> events x"
  using assms by (induct p x s rule:pri.induct, auto)

lemma prirel_not_events':
  assumes "pri p x s" "tick \<notin> events x"
  shows "tick \<notin> events s"
  using assms by (induct p x s rule:pri.induct, auto)

lemma prirel_consFL_both_imp_prirel:
  assumes "pri p (s &\<^sub>\<F>\<^sub>\<L> t) (u &\<^sub>\<F>\<^sub>\<L> v)" "last s = \<bullet>" "last u = \<bullet>" "length s = length u"
  shows "pri p t v"
  using assms by(induct p s u rule:pri.induct, auto)

lemma prirel_consFL_last_bullet_both:
  assumes "pri p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,b)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>(a,c)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last s = \<bullet>" "last ys = \<bullet>" "maximal(p,b)" "c \<in>\<^sub>\<F>\<^sub>\<L> a \<or> a = \<bullet>"
  shows "b = c"
  using assms apply(induct p s ys rule:pri.induct, auto)
      apply (metis Finite_Linear_Model.butlast.simps(1) bullet_left_zero2 butlast_last_cons2_FL fltrace.exhaust fltrace_concat2.simps(2) pri.simps(2))
     apply (metis fltrace.distinct(1) fltrace.exhaust pri.simps(2) rev3.simps(1) rev3_little_more_extra)      
  by (metis bullet_left_zero2 dual_order.antisym pri.simps(3) prirel_consFL_last_bullet_exists' x_le_x_concat2)+
  
lemma tickWF_consFL_tick_imp_bullet:
  assumes "tickWF tick (ys &\<^sub>\<F>\<^sub>\<L> \<langle>(y,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last ys = \<bullet>" "tick \<in>\<^sub>\<F>\<^sub>\<L> y \<or> y = \<bullet>"
  shows "y = \<bullet>"
  using assms apply (induct ys rule:tickWF.induct, auto)
  by (metis fltrace.distinct(1) rev3.simps(1) rev3_little_more)

lemma pri_eq_length_two_last_bullet:
  assumes "xs pri\<^sub>[\<^sub>p\<^sub>] (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)" "length xs = length ys" "last ys = \<bullet>" "last xs = \<bullet>"
  shows "y = \<bullet>"
  using assms apply (induct p xs ys rule:pri.induct, auto)
  by (cases y, auto)

lemma prirel_exists_tick_max:
  assumes "pri p S Z" "last s = \<bullet>" "maximal(p,tick)" "S = (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "tickWF tick Z"
  shows "\<exists>z. last z = \<bullet> \<and> Z = (z &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> length s = length z"
  using assms 
proof (induct S Z rule:ftrace_cons_induct_both_eq_length)
  case 1
  then show ?case 
    using assms(1) prirel_same_length by blast
next
  case (2 x y)
  then show ?case 
    by (metis fltrace.distinct(1) rev3.simps(1) rev3_little_more)
next
  case (3 x y xs ys)
  then show ?case
  proof (cases y)
    case acnil
    then show ?thesis
      using 3 apply auto
      by (metis Finite_Linear_Model.last.simps(1) bullet_right_zero2 last_bullet_then_last_cons last_cons_bullet_iff)
  next
    case (acset y2)
    then show ?thesis
    proof (cases x)
      case acnil
      then show ?thesis
      proof -
        have f1: "\<forall>f. Finite_Linear_Model.last (f &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) \<noteq> \<bullet>"
          using acset last_cons_acceptance_not_bullet by blast
        have f2: "\<forall>f fa fb fc fd p. (f &\<^sub>\<F>\<^sub>\<L> fb pri\<^sub>[\<^sub>(p::'a partialorder)\<^sub>] fa &\<^sub>\<F>\<^sub>\<L> (fd &\<^sub>\<F>\<^sub>\<L> fc) \<or> \<not> f pri\<^sub>[\<^sub>p\<^sub>] fa &\<^sub>\<F>\<^sub>\<L> fd) \<or> \<not> fb pri\<^sub>[\<^sub>p\<^sub>] fc"
          by (metis fltrace_concat2_assoc prirel_consFL_both_imp')
        have f3: "xs pri\<^sub>[\<^sub>p\<^sub>] ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
          by (metis "3.prems"(1) acnil bullet_right_zero2)
        then have "\<forall>f fa a. \<not> a #\<^sub>\<F>\<^sub>\<L> fa pri\<^sub>[\<^sub>p\<^sub>] f"
          using f2 f1 by (metis (no_types) "3.hyps"(2) "3.hyps"(3) "3.hyps"(4) FL_concat_equiv Finite_Linear_Model.last.simps(2) concat_FL_last_not_bullet_absorb pri.simps(3) prirel_consFL_both_imp_prirel)
        then show ?thesis
          using f3 by (metis "3.prems"(4) acnil assms(2) bullet_right_zero2 prirel_consFL_last_bullet_exists')
      qed
  next
    case (acset x2)
    then show ?thesis 
      using 3 acset by (metis last_cons_acceptance_not_bullet last_cons_bullet_iff)
    qed
  qed
next
  case (4 x y xs ys)
  then have "pri p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    by auto
  then obtain yA yEvent where yA:"y = (yA,yEvent)\<^sub>\<F>\<^sub>\<L> \<and> (yEvent \<in>\<^sub>\<F>\<^sub>\<L> yA \<or> yA = \<bullet>)"
    proof -
      assume a1: "\<And>yA yEvent. y = (yA,yEvent)\<^sub>\<F>\<^sub>\<L> \<and> (yEvent \<in>\<^sub>\<F>\<^sub>\<L> yA \<or> yA = \<bullet>) \<Longrightarrow> thesis"
      have "y \<le> (acceptance y,event y)\<^sub>\<F>\<^sub>\<L>"
        by (simp add: less_eq_aevent_def)
      then show ?thesis
        using a1 by (metis aevent_less_eq_iff_components event_in_acceptance)
    qed
  then have "pri p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>(yA,yEvent)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "4.prems"(1) "4.prems"(4) by auto
  then have "yEvent = tick"
            "yA = \<bullet>"
    using prirel_consFL_last_bullet_both "4.hyps"(4) yA assms(2) assms(3) apply fastforce
    using 4 tickWF_consFL_tick_imp_bullet 
    by (metis prirel_consFL_last_bullet_both yA)
  then have "ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = ys &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> Finite_Linear_Model.length s = Finite_Linear_Model.length ys"
    by (metis "4.hyps"(2) "4.hyps"(3) "4.prems"(4) assms(2) fltrace.inject(2) rev3_little_more rev3_rev3_const2_last yA)
  then show ?case
    using "4.hyps"(4) by blast
qed

lemma Pri_dist_SeqComp:
  assumes "FLTick0 tick P" "maximal(p,tick)"
  shows "Pri p (P (tick);\<^sub>\<F>\<^sub>\<L> Q) = ((Pri p P) (tick);\<^sub>\<F>\<^sub>\<L> (Pri p Q))"
  using assms unfolding Pri_def SeqComp_def
proof (auto)
  fix "x" "s" "t"
  assume  assm0:"FLTick0 tick P"
      and assm1:"pri p x (s &\<^sub>\<F>\<^sub>\<L> t)"
      and assm2:"s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
      and assm3:"t \<in> Q"
  show "\<exists>s. (\<exists>Z. pri p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z \<and> Z \<in> P) \<and> (\<exists>t. (\<exists>Z. pri p t Z \<and> Z \<in> Q) \<and> x = s &\<^sub>\<F>\<^sub>\<L> t) \<or>
           (\<exists>Z. pri p s Z \<and> Z \<in> P) \<and> tick \<notin> events s \<and> x = s"
  proof (cases "last s = \<bullet>")
    case True
    then obtain s0 t0 where s0t0:"x = s0 &\<^sub>\<F>\<^sub>\<L> t0 \<and> pri p s0 s \<and> pri p t0 t"
      using assm1 prirel_consFL_last_bullet_exists by blast
    then have "pri p \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using assms(2) by auto
    then have "pri p (s0 &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using s0t0 prirel_consFL_both_imp' by blast    
    then show ?thesis
      using assm2 assm3 s0t0 by blast
  next
    case False
    then show ?thesis
      by (metis FLTick0_def assm0 assm1 assm2 concat_FL_last_not_bullet_absorb prirel_not_events tickWF_last_x_is_emptyset)
  qed
next
  fix "x" "s"
  assume  assm0:"FLTick0 tick P"
    and   assm1:"maximal(p,tick)"
    and   assm2:"pri p x s"
    and   assm3:"s \<in> P"
    and   assm4:"tick \<notin> events s"
  show "\<exists>s. (\<exists>Z. pri p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z \<and> Z \<in> P) \<and> (\<exists>t. (\<exists>Z. pri p t Z \<and> Z \<in> Q) \<and> x = s &\<^sub>\<F>\<^sub>\<L> t) \<or>
            (\<exists>Z. pri p s Z \<and> Z \<in> P) \<and> tick \<notin> events s \<and> x = s"
  proof -
    have "tick \<notin> events x"
      using assm2 assm4 prirel_not_events
      by fastforce
    then show ?thesis
      using assm2 assm3 by blast
  qed
next
  fix "s" "t" "Z" "Za"
  assume 
      assm0: "FLTick0 tick P"
  and assm1: "maximal(p,tick)"
  and assm2: "pri p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z"
  and assm3: "Z \<in> P"
  and assm4: "pri p t Za"
  and assm5: "Za \<in> Q"
  show "\<exists>Z. pri p (s &\<^sub>\<F>\<^sub>\<L> t) Z \<and> (\<exists>s. s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> (\<exists>t. t \<in> Q \<and> Z = s &\<^sub>\<F>\<^sub>\<L> t) \<or> s \<in> P \<and> tick \<notin> events s \<and> Z = s)"
  proof (cases "last s = \<bullet>")
    case True
    then obtain s0 where s0:"pri p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (s0 &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> last s0 = \<bullet> \<and> length s = length s0 \<and> Z = (s0 &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      by (metis FLTick0_def assm0 assm1 assm2 assm3 prirel_exists_tick_max)
    then have "pri p s s0"
      using True prirel_consFL_both_imp by blast
    then have "pri p (s &\<^sub>\<F>\<^sub>\<L> t) (s0 &\<^sub>\<F>\<^sub>\<L> Za)"
      by (simp add: assm4 prirel_consFL_both_imp')
    then have "\<exists>Z. pri p (s &\<^sub>\<F>\<^sub>\<L> t) (s0 &\<^sub>\<F>\<^sub>\<L> Za) \<and> s0 &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> Za \<in> Q \<and> Z = s0 &\<^sub>\<F>\<^sub>\<L> Za"
      using s0 assm5 assm3 by blast
    then show ?thesis
      by blast
  next
    case False
    then show ?thesis 
      by (metis FLTick0_def \<open>Z \<in> P\<close> \<open>pri p (s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) Z\<close> assms(1) concat_FL_last_not_bullet_absorb prirel_cons_eq_length_imp_prirel_acceptances_last_bullet_eq prirel_cons_eq_length_imp_prirel_acceptances_last_not_bullet prirel_same_length tickWF_last_x_is_emptyset)
  qed
next
  fix "s" "Z"
  assume 
       assm0: "FLTick0 tick P"
  and  assm1: "maximal(p,tick)"
  and  assm2: "tick \<notin> events s"
  and  assm3: "pri p s Z"
  and  assm4: "Z \<in> P"
  show "\<exists>Z. pri p s Z \<and> (\<exists>s. s &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> (\<exists>t. t \<in> Q \<and> Z = s &\<^sub>\<F>\<^sub>\<L> t) \<or> s \<in> P \<and> tick \<notin> events s \<and> Z = s)"
    using assm3 assm4 assm2 apply (rule_tac x="Z" in exI, auto)
    apply (rule_tac x="Z" in exI, auto)
    by (simp add: prirel_not_events')+
qed

end