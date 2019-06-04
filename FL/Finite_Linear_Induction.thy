theory Finite_Linear_Induction
  imports
    Finite_Linear_Model
begin

lemma prefixFL_induct:
  "(\<And>xs. P \<langle>xs\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Longrightarrow> (\<And>xs ys. P xs \<and> xs \<le> ys \<Longrightarrow> P ys) \<Longrightarrow> P xs"
  by (metis fltrace.exhaust less_eq_acceptance.simps(1) less_eq_fltrace.simps(2))

lemma prefixFL_induct2:
  "\<lbrakk>(P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>); (\<And>xs ys. P xs \<and> xs \<le> ys \<Longrightarrow> P ys)\<rbrakk> \<Longrightarrow> P xs"
  using fltrace.inject(1) less_eq_acceptance.simps(1) less_eq_fltrace.elims(3) by fastforce

lemma prefixFL_induct21:
  "\<lbrakk>(P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>); (\<And>xs ys. P xs \<Longrightarrow> xs \<le> ys \<Longrightarrow> P ys)\<rbrakk> \<Longrightarrow> P xs"
  using fltrace.inject(1) less_eq_acceptance.simps(1) less_eq_fltrace.elims(3) by fastforce

lemma cons_is_concatC: "x #\<^sub>\<F>\<^sub>\<L> xs = (\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> @\<^sub>\<F>\<^sub>\<L> xs)"
  by (induct xs, auto simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)

(*
lemma fltrace_induct1:
  "(\<And>x. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (x + xs)) \<Longrightarrow> P xs"
  apply(subst rev_rev_last[symmetric])
  apply (induct xs, auto)
*)

lemma fltrace_induct0:
  "P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> x)) \<Longrightarrow> P xs"
  apply(subst rev4_rev4[symmetric])
  apply(rule_tac fltrace ="rev4 xs" in fltrace.induct)
  by force+

lemma fltrace_induct00:
  "P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<Longrightarrow> (\<And>x xs y ys. P xs ys \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> x) (ys &\<^sub>\<F>\<^sub>\<L> y)) \<Longrightarrow> P xs ys"
  apply(subst rev4_rev4[symmetric])
  apply(rule_tac fltrace ="rev4 xs" in fltrace.induct)
  by force+

text \<open>The following induction rule is unsatisfactory because it relies on swapping
      'x' to the front of 'y'.\<close>

lemma fltrace_induct01:
  "\<lbrakk>P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>;
   (\<And>x xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>));
   (\<And>x y xs. P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>y,x\<rangle>\<^sub>\<F>\<^sub>\<L>))\<rbrakk> \<Longrightarrow> P xs"
  apply(subst rev4_rev4[symmetric])
  apply(rule_tac fltrace ="rev4 xs" in fltrace.induct)
  unfolding rev4_def apply (case_tac x, auto)
   apply force
  by (simp add: fltrace_concat2_assoc)

text \<open>Instead we would like to prove the following lemma.\<close>

lemma
  "\<lbrakk>P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>;
   (\<And>x xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>));
   (\<And>x y xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) \<rbrakk> \<Longrightarrow> P xs"
  oops

text \<open>The key observation to enable the proof of this lemma is that it
      can be proved when last xs = \<bullet>. This is precisely the case when considering
      the application of 'butlast' to xs. Therefore we need, first of all, a rule
      that uses consFL and assumes last xs = \<bullet>, and then prove the induction rule
      when we have that butlast xs holds. \<close>

lemma fltrace_induct_last_bullet:
  "\<lbrakk>(\<And>x. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>);
    (\<And>x1a x2. P x2 \<Longrightarrow> last x2 = \<bullet> \<Longrightarrow> P (x1a #\<^sub>\<F>\<^sub>\<L> x2))\<rbrakk> \<Longrightarrow> last x = \<bullet> \<Longrightarrow> P x"
  by (induct x, auto)

lemma fltrace_induct_butlast_every:
  "\<lbrakk>P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>;
   (\<And>x xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>));
   (\<And>x xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) \<rbrakk> \<Longrightarrow> P (butlast xs) \<Longrightarrow> P xs"
  by (metis butlast_last_cons2_FL)

lemma fltrace_induct_butlast:
  "\<lbrakk>P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>;
   (\<And>x xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>));
   (\<And>x xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) \<rbrakk> \<Longrightarrow> P (butlast xs)"
  apply(subst rev4_rev4[symmetric])
  apply(rule_tac x ="rev4(butlast xs)" in fltrace_induct_last_bullet)
  unfolding rev4_def apply (case_tac x, auto)
   apply force
  by (metis bullet_right_zero2 last_butlast_cons_bullet last_rev3_acceptance)

text \<open>We are now in a position to prove the main induction rule.\<close>

lemma fltrace_induct:
  "\<lbrakk>P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>;
   (\<And>x xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>));
   (\<And>x xs. P xs \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) \<rbrakk> \<Longrightarrow> P xs"
  using fltrace_induct_butlast_every fltrace_induct_butlast by blast

lemma ftrace_cons_induct_both:
  assumes "length x = length y"
  shows "\<lbrakk>(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>);
          (\<And>x x1a y y1a. P x y \<Longrightarrow> length x = length y \<Longrightarrow> P (x1a #\<^sub>\<F>\<^sub>\<L> x) (y1a #\<^sub>\<F>\<^sub>\<L> y))\<rbrakk> \<Longrightarrow> P x y"
using assms proof (induct x arbitrary: y)
  case (Acceptance x)
  then show ?case
    apply auto
    by (case_tac y, auto)
next
  case (AEvent x1a x)
  then show ?case apply auto
    by (case_tac y, auto)
qed

lemma length_rev3_eq:
  assumes "length x = length y"
  shows "length (rev3 x) = length (rev3 y)"
  using assms apply(induct x y rule:ftrace_cons_induct_both, auto)
  by (simp add: last_rev3_is_bullet length_cons)

lemma ftrace_cons_induct_both_butlast_rev4:
  assumes "length x = length y"
          "(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs = \<bullet> \<Longrightarrow> last ys = \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
  shows "P (butlast(rev4(x))) (butlast(rev4(y)))"
  using assms proof (induct x y rule:ftrace_cons_induct_both)
    case 1
    then show ?case using assms by auto
  next
    case (2 x y)
    then show ?case unfolding rev4_def by auto
  next
    case (3 x x1a y y1a)
    from 3 have rev4:"P (butlast (rev4 x)) (butlast (rev4 y))"
      by auto
     
    have rev4_rev3:"P (butlast (rev4 x)) (butlast (rev4 y)) = P (rev3 x) (rev3 y)"
      unfolding rev4_def using last_bullet_butlast_last
      by (simp add: last_bullet_butlast_last last_rev3_is_bullet)

    then have rev3:"P (rev3 x) (rev3 y)"
      using rev4 by auto

    have eq_length:"length (rev3 x) = length (rev3 y)"
      using 3 length_rev3_eq by auto  
    
    have "P (butlast(rev4(x1a #\<^sub>\<F>\<^sub>\<L> x))) (butlast(rev4(y1a #\<^sub>\<F>\<^sub>\<L> y)))
               = 
               P (butlast(rev3(x1a #\<^sub>\<F>\<^sub>\<L> x) &\<^sub>\<F>\<^sub>\<L> \<langle>last x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (butlast(rev3(y1a #\<^sub>\<F>\<^sub>\<L> y) &\<^sub>\<F>\<^sub>\<L> \<langle>last y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
      unfolding rev4_def by auto
    also have "... =
               P (butlast((rev3(x) &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) &\<^sub>\<F>\<^sub>\<L> \<langle>last x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (butlast((rev3(y) &\<^sub>\<F>\<^sub>\<L> \<langle>y1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) &\<^sub>\<F>\<^sub>\<L> \<langle>last y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
      by auto
    also have "... =
               P (butlast(rev3(x) &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,last x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (butlast(rev3(y) &\<^sub>\<F>\<^sub>\<L> \<langle>y1a,last y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
      by (simp add: fltrace_concat2_assoc)
    also have "... = P (rev3(x) &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (rev3(y) &\<^sub>\<F>\<^sub>\<L> \<langle>y1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      by (simp add: last_bullet_butlast last_rev3_is_bullet)
    also have "... = True"
      using assms rev3 3 
      using eq_length
      by (simp add: last_rev3_is_bullet)
    then show ?case
      using calculation by blast
  qed



lemma ftrace_cons_induct_both_butlast:
  assumes "length x = length y"
          "(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs = \<bullet> \<Longrightarrow> last ys = \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
    shows "P (butlast(x)) (butlast(y))"
proof -
  have "P (butlast(x)) (butlast(y))
        =
        P (butlast(rev4(rev4(x)))) (butlast(rev4(rev4(y))))"
    by (auto simp add:rev4_rev4)
  then show ?thesis
    by (metis assms(1) assms(2) assms(3) ftrace_cons_induct_both_butlast_rev4 last_bullet_butlast_last last_rev3_is_bullet length_rev3_eq rev3_rev3_const2_last rev4_def)
qed

lemma ftrace_cons_induct_both_butlast_eq_length:
  assumes "length x = length y"
          "(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs = \<bullet> \<Longrightarrow> last ys = \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs = \<bullet> \<Longrightarrow> last ys = \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          "P (butlast(x)) (butlast(y))"
        shows "P x y"
  by (metis assms(1) assms(3) assms(5) bullet_right_zero2 butlast_last_cons2_FL last_butlast_cons_bullet length.simps(1) length_cons)
  
lemma ftrace_cons_induct_both_eq_length:
  assumes "length x = length y"
          "(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs = \<bullet> \<Longrightarrow> last ys = \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs = \<bullet> \<Longrightarrow> last ys = \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        shows "P x y"
  by (simp add: assms(1) assms(2) assms(3) assms(4) ftrace_cons_induct_both_butlast ftrace_cons_induct_both_butlast_eq_length)

lemma fltrace_induct1:
  "(\<And>x. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (x @\<^sub>\<F>\<^sub>\<L> xs)) \<Longrightarrow> P xs"
  apply(subst rev_rev_last[symmetric])
  by(induct xs, auto)

lemma fltrace_induct2:
  "(\<And>x. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (xs @\<^sub>\<F>\<^sub>\<L> x)) \<Longrightarrow> P xs"
  apply(subst rev_rev_last[symmetric])
  apply(induct xs, auto)
  by (metis bullet_left_zero)  

lemma fltrace_induct3:
  "P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (xs @\<^sub>\<F>\<^sub>\<L> x)) \<Longrightarrow> P xs"
  apply(subst rev_rev_last[symmetric])
  apply(induct xs, auto)
  apply fastforce
  by fastforce

lemma fltrace_induct4:
  "\<lbrakk>(P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>);
    (\<And>y xs. P (xs) \<Longrightarrow> P (xs @\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>));
    (\<And>y b xs. P (xs @\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Longrightarrow> P (xs @\<^sub>\<F>\<^sub>\<L> \<langle>b\<rangle>\<^sub>\<F>\<^sub>\<L>));
    (\<And>y b xs. P (xs @\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Longrightarrow> y \<le> acceptance(b)  \<Longrightarrow> P (xs @\<^sub>\<F>\<^sub>\<L> \<langle>b,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))\<rbrakk> \<Longrightarrow> P xs"
  apply (subst rev_rev_last[symmetric])
  apply(rule_tac fltrace ="rev xs" in fltrace.induct)                
   apply (auto)
   apply fastforce
  by blast

lemma fltrace_induct5:
  "\<lbrakk>(P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>);
    (\<And>y xs. P (xs) \<Longrightarrow> P (xs @\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>));
    (\<And>y b xs. P (xs @\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)  \<Longrightarrow> P (xs @\<^sub>\<F>\<^sub>\<L> \<langle>b,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))\<rbrakk> \<Longrightarrow> P xs"
  apply (subst rev_rev_last[symmetric])
  apply(rule_tac fltrace ="rev xs" in fltrace.induct)                
   apply (auto)
  by fastforce

lemma fltrace_induct6:
  "\<lbrakk>(P \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>);
    (\<And>y. P \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>);
    (\<And>y. P \<langle>acceptance(y)\<rangle>\<^sub>\<F>\<^sub>\<L> \<Longrightarrow> P \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>);
    (\<And>y xs. P (\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<Longrightarrow> P (y #\<^sub>\<F>\<^sub>\<L> xs))\<rbrakk> \<Longrightarrow> P xs"
  by (induct xs, auto)

lemma fltrace_eq_length_imp_eq_length_cons_acceptance:
  assumes "length xs = length ys" "last xs = \<bullet>" "last ys = \<bullet>"
  shows "length (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = length (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (simp add: length_cons)

lemma fltrace_eq_length_imp_eq_length_cons_acceptance2:
  assumes "length xs = length ys" "last xs \<noteq> \<bullet>" "last ys \<noteq> \<bullet>"
  shows "length (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = length (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (simp add: concat_FL_last_not_bullet_absorb)

lemma fltrace_eq_length_imp_neq_length:
  assumes "length xs = length ys" "last xs \<noteq> \<bullet>" "last ys = \<bullet>"
  shows "length (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<noteq> length (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (simp add: concat_FL_last_not_bullet_absorb length_cons)

lemma fltrace_eq_length_imp_eq_length:
  assumes "length xs = length ys" "last xs = \<bullet>" "last ys = \<bullet>"
  shows "length (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = length (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (simp add: length_cons)

lemma fltrace_cons_eq_length_imp_eq_length:
  assumes "length (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = length (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last xs = \<bullet>" "last ys = \<bullet>"
  shows "length xs = length ys"
  using assms
  by (metis add_right_cancel length.simps(1) length.simps(2) length_cons)

lemma fltrace_eq_length_imp_eq_length2:
  assumes "length xs = length ys" "last xs \<noteq> \<bullet>" "last ys \<noteq> \<bullet>"
  shows "length (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = length (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (simp add: concat_FL_last_not_bullet_absorb)
 
lemma fltrace_cons_eq_length_imp_eq_length2:
  assumes "length (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = length (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)" "last xs \<noteq> \<bullet>" "last ys \<noteq> \<bullet>"
  shows "length xs = length ys"
  using assms by (simp add: concat_FL_last_not_bullet_absorb)

lemma ftrace_cons_induct_both_eq_length2:
  assumes "length x = length y"
          "(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs \<noteq> \<bullet> \<Longrightarrow> last ys \<noteq> \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs = \<bullet> \<Longrightarrow> last ys = \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs \<noteq> \<bullet> \<Longrightarrow> last ys \<noteq> \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> last xs = \<bullet> \<Longrightarrow> last ys = \<bullet> \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
    shows "P x y"
  by (simp add: assms(1) assms(2) assms(4) assms(6) ftrace_cons_induct_both_eq_length)
  
end