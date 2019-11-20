theory TickTock_Max_FL_Priority

imports
  "TickTock_Max_Pri"
  "TickTock_Max_FL"
  "FL.Finite_Linear_Pri"
  "FL.Finite_Linear_Pri_Laws"
begin

text \<open> This theory contains results on the calculation of
       a definition for Pri in TickTock_Max based on that
       of the Finite-Linear model. \<close>

section \<open> Preliminaries \<close>

text \<open> The following describes early results, and attempts, at calculating
       the definition of Pri from FL. \<close>

lemma fl2ttobs_extn:
  "(fl2ttm fl\<^sub>0 \<subseteq> P \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))
   =
   ({fl2ttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs(Z) \<in> P))"
proof -

    have "((fl2ttm fl\<^sub>0) \<subseteq> P \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))
          =
          ((\<forall>x. x \<in> (fl2ttm fl\<^sub>0) \<longrightarrow> x \<in> P) \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>x. x \<in> {fl2ttobs fl|fl. fl \<in> fl\<^sub>0} \<longrightarrow> x \<in> P) \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))"
      unfolding fl2ttm_def by auto
    also have "... =
          ((\<forall>x. (\<exists>fl. x = fl2ttobs(fl) \<and> fl \<in> fl\<^sub>0) \<longrightarrow> x \<in> P) \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>x fl. (x = fl2ttobs(fl) \<and> fl \<in> fl\<^sub>0) \<longrightarrow> x \<in> P) \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>fl. fl \<in> fl\<^sub>0 \<longrightarrow> fl2ttobs(fl) \<in> P) \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>fl. (fl \<in> fl\<^sub>0 \<longrightarrow> fl2ttobs(fl) \<in> P)) \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          (\<forall>fl\<^sub>x. (fl\<^sub>x \<in> fl\<^sub>0 \<longrightarrow> fl2ttobs(fl\<^sub>x) \<in> P) \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
  then have "...
        =
        (\<forall>fl\<^sub>x. (fl\<^sub>x \<in> fl\<^sub>0 \<longrightarrow> fl2ttobs(fl\<^sub>x) \<in> P) \<and> 
              (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs(Z) \<in> P))"
    by auto
  then have "... =
        ((\<forall>x fl. (x = fl2ttobs(fl) \<and> fl \<in> fl\<^sub>0) \<longrightarrow> x \<in> P) \<and>
              (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs(Z) \<in> P))"
    by auto
  then have "... =
        (({fl2ttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P) \<and>
              (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs(Z) \<in> P))"
    by auto
  ultimately show ?thesis
    by (smt \<open>((\<forall>x. x \<in> fl2ttm fl\<^sub>0 \<longrightarrow> x \<in> P) \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0)) = ((\<forall>x. x \<in> {fl2ttobs fl |fl. fl \<in> fl\<^sub>0} \<longrightarrow> x \<in> P) \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0))\<close> mem_Collect_eq subset_eq)
qed

lemma fl2ttobs_base_priacc:
  assumes "priacc p Z = A"
  shows "fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if A = \<bullet> then [] else [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R])"
  using assms
proof (cases Z)
  case acnil
  then show ?thesis using assms 
    by auto
next
  case ZS:(acset ZS)
  then show ?thesis
    proof (cases A)
      case acnil
      then show ?thesis using assms by auto
    next
      case (acset AS)
      then have AS:"AS = {a. a \<in> ZS \<and> \<not>(\<exists>b. b\<in>ZS \<and> a <\<^sup>*p b)}"
        using assms ZS by auto
      then have a:"fl2ttobs(\<langle>[AS]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> [AS]\<^sub>\<F>\<^sub>\<L>}]\<^sub>R]"
        by auto
      also have "... = [[{z. z \<notin> AS}]\<^sub>R]"
        by auto
      also have "... = [[{z. z \<notin> {a. a \<in> ZS \<and> \<not>(\<exists>b. b\<in>ZS \<and> a <\<^sup>*p b)}}]\<^sub>R]"
        using AS by auto
      also have "... = [[{z. \<not>(\<exists>a. a = z \<and> a \<in> ZS \<and> \<not>(\<exists>b. b\<in>ZS \<and> a <\<^sup>*p b))}]\<^sub>R]"
        by auto
      also have "... = [[{z. \<not>(z \<in> ZS \<and> \<not>(\<exists>b. b\<in>ZS \<and> z <\<^sup>*p b))}]\<^sub>R]"
        by auto
      also have "... = [[{z. z \<in> ZS \<longrightarrow> (\<exists>b. b\<in>ZS \<and> z <\<^sup>*p b)}]\<^sub>R]"
        by blast
      also have "... = [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R]"
        using ZS by auto
      then show ?thesis using calculation acset by auto
    qed
qed

lemma fl2ttobs_base_Z_priacc:
  assumes "priacc p Z = A"
  shows "fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) 
         =
         (if Z = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R])"
  using assms
proof (cases Z)
  case acnil
  then show ?thesis by auto
next
  case ZS:(acset ZS)
  then show ?thesis
    proof (cases A)
      case acnil
      then show ?thesis using assms by auto
    next
      case (acset AS)
      then have AS:"AS = {a. a \<in> ZS \<and> \<not>(\<exists>b. b\<in>ZS \<and> a <\<^sup>*p b)}"
        using assms ZS by auto
      then have a:"fl2ttobs(\<langle>[ZS]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> [ZS]\<^sub>\<F>\<^sub>\<L>}]\<^sub>R]"
        by auto
      then show ?thesis using assms by auto
    qed
  qed

(*
lemma fl2ttobs_base_Z_priacc_iff:
   "priacc p Z = A \<longleftrightarrow>
         ((fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if Z = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R]))
          \<and> 
         (fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if A = \<bullet> then [] else (if Z \<noteq> \<bullet> then [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R] else []))))"
  apply (cases Z, auto)
by (induct Z rule:priacc.induct, auto)*)

lemma
  "{z. z \<in> {z. z \<notin> Z} \<longrightarrow> (\<exists>b. b\<in> {z. z \<notin> Z} \<and> z <\<^sup>*p b)} 
   = 
   {z. z \<notin> Z \<longrightarrow> (\<exists>b. b \<notin> Z \<and> z <\<^sup>*p b)}"
proof -
  have "{z. z \<in> {z. z \<notin> Z} \<longrightarrow> (\<exists>b. b\<in> {z. z \<notin> Z} \<and> z <\<^sup>*p b)}
        =
        {z. z \<notin> Z \<longrightarrow> (\<exists>b. b \<notin> Z \<and> z <\<^sup>*p b)}"
    by auto
  then show ?thesis .
qed

lemma priacc_eq_priref_via_fl2ttobs1:
  assumes "fl2ttobs(\<langle>priacc p Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R]" "fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R]"
  shows "prirefMaxTT p S = R"
  using assms unfolding prirefMaxTT_def by (cases Z, auto)

lemma priacc_eq_priref_via_fl2ttobs2:
  assumes "fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R]" "fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R]" "prirefMaxTT p S = R"
  shows "priacc p Z = A"
  using assms unfolding prirefMaxTT_def 
  apply (cases Z, auto)
  by (cases A, auto)

lemma priacc_eq_priref_via_fl2ttobs:
  assumes "fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R]" "fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R]"
  shows "(priacc p Z = A) \<longleftrightarrow> (prirefMaxTT p S = R)"
  using assms priacc_eq_priref_via_fl2ttobs1 priacc_eq_priref_via_fl2ttobs2
  by metis

(*
lemma priacc_eq_priref_via_fl2ttobs:
  assumes "fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R]" "fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R]"
  shows "(priacc p Z = A) \<longleftrightarrow> (prirelref p S = R)"
proof -
  have "(priacc p Z = A) 
        =
        ((fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if Z = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R]))
          \<and> 
         (fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if A = \<bullet> then [] else (if Z \<noteq> \<bullet> then [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R] else []))))" 
    apply (cases Z, auto)
    by (induct Z rule:priacc.induct, auto)
  also have "... = 
        (([[S]\<^sub>R] = (if Z = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R]))
          \<and> 
         ([[R]\<^sub>R] = (if A = \<bullet> then [] else (if Z \<noteq> \<bullet> then [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R] else []))))"
    using assms by simp
  also have "... = 
        (([[S]\<^sub>R] = [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R] \<and> Z \<noteq> \<bullet>)
          \<and> 
         ([[R]\<^sub>R] = [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R] \<and> A \<noteq> \<bullet> \<and> Z \<noteq> \<bullet>))"
    by auto
  also have "... = 
        (([[S]\<^sub>R] = [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R])
          \<and> 
         ([[R]\<^sub>R] = [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R] \<and> A \<noteq> \<bullet>))"
    using assms by auto
  also have "... = 
        ([[S]\<^sub>R] = [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> [{z. z \<notin> S}]\<^sub>\<F>\<^sub>\<L>}]\<^sub>R] \<and> [[R]\<^sub>R] = [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> [{z. z \<notin> S}]\<^sub>\<F>\<^sub>\<L> \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>[{z. z \<notin> S}]\<^sub>\<F>\<^sub>\<L> \<and> z <\<^sup>*p b)}]\<^sub>R])"
  proof -
    have "Z = [{z. z \<notin> S}]\<^sub>\<F>\<^sub>\<L>"
      using assms apply auto
      by (cases Z, auto)
    then show ?thesis
      using assms(1) by auto
  qed
  also have "... = 
        ([[S]\<^sub>R] = [[{z. z \<in> S}]\<^sub>R] \<and> [[R]\<^sub>R] = [[{z. z \<notin> S \<longrightarrow> (\<exists>b. b \<notin> S \<and> z <\<^sup>*p b)}]\<^sub>R])"
    by auto
  also have "... = ([[R]\<^sub>R] = [[{z. z \<notin> S \<longrightarrow> (\<exists>b. b \<notin> S \<and> z <\<^sup>*p b)}]\<^sub>R])"
    by auto
  also have "... = (R = {z. z \<notin> S \<longrightarrow> (\<exists>b. b \<notin> S \<and> z <\<^sup>*p b)})"
    by auto
  finally show ?thesis unfolding priref_def by auto
qed
*)
lemma
  "acceptance(A) = \<bullet> \<longleftrightarrow> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = []"
  by auto

lemma acceptances_same_set:
  assumes "acceptance Z \<noteq> \<bullet>"
  shows "acceptance Z = [{z. z \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z}]\<^sub>\<F>\<^sub>\<L>"
  using assms apply (cases Z, auto)
  by (case_tac a, auto)

(* TODO: to be fixed using new definition. *)

(*
lemma
  assumes "fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = ctA" "fl2ttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = ctZ"
          "event(Z) = Tock \<and> acceptance(Z) \<noteq> \<bullet>"
  shows "pri p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
      =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (pri p aa zz) \<and>
      ((ctA = [] \<and> (\<forall>b. (Tock <\<^sup>*p b) \<longrightarrow> b \<in> ref))
      \<or>
      ctA = [priref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
proof -
  from assms(3) have event_Tock:"event(Z) = Tock \<and> acceptance(Z) \<noteq> \<bullet>"
      by auto
  then have ctZA:"ctZ = [{z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(Z)}]\<^sub>R # [Tock]\<^sub>E # (fl2ttobs zz)"
    using assms(2) by auto
  then have "\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> acceptance(Z) = [{z. z \<notin> ref}]\<^sub>\<F>\<^sub>\<L> \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R]"
    using event_Tock acceptances_same_set by auto
  then have "pri p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> 
      ((acceptance A) \<le> priacc p (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> [{z. z \<notin> ref}]\<^sub>\<F>\<^sub>\<L> \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    using event_Tock by (metis ttobs.inject(2) pri.simps(4))
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> 
      (priacc p (acceptance A) (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = Tock
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (\<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    by simp
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> 
      (priacc p (acceptance A) (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = Tock
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (acceptance(A) = \<bullet> \<or> acceptance(A) \<noteq> \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (\<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (pri p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      (acceptance(A) \<noteq> \<bullet> \<and> priacc p (acceptance A) (acceptance Z))))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (pri p aa zz) \<and> event(A) = Tock 
     \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> 
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      (\<exists>ref\<^sub>1. fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref\<^sub>1]\<^sub>R] \<and> priacc p (acceptance A) (acceptance Z))))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (pri p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> 
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      (\<exists>ref\<^sub>1. fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref\<^sub>1]\<^sub>R] \<and> priref p ref = ref\<^sub>1)))"
    using priacc_eq_priref_via_fl2ttobs
    by blast
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (pri p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[priref p ref]\<^sub>R]))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (pri p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[priref p ref]\<^sub>R]))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (pri p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[priref p ref]\<^sub>R]))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (pri p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[priref p ref]\<^sub>R]))"
    using assms(1) by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (pri p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = [priref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (pri p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [priref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    using assms(1) by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (pri p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [priref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    using event_Tock by auto
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (pri p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [priref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    using assms(2) by auto
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (pri p aa zz) \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [priref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    using assms(1) by force
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (pri p aa zz) \<and>
      ((ctA = [] \<and> \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b))
      \<or>
      ctA = [priref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
  proof -
    have "\<forall>ref. (maximal(p,Tock) \<or> \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b))
                = 
                (\<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b))"
      apply auto
      by (simp add: some_higher_not_maximal)
    then show ?thesis by auto
  qed
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (pri p aa zz) \<and>
      ((ctA = [] \<and> (\<forall>b. (Tock <\<^sup>*p b) \<longrightarrow> b \<in> ref))
      \<or>
      ctA = [priref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"  
    by auto
  finally show ?thesis .
qed

lemma
  assumes "fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = ctA" "fl2ttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = ctZ"
          "event(Z) = Tock \<and> acceptance(Z) = \<bullet>"
  shows "pri p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) = (ctZ = [] \<and> ctA = [] \<and> (pri p aa zz) \<and> maximal(p,Tock))"
proof -
  from assms(3) have event_Tock_bullet:"event(Z) = Tock \<and> acceptance(Z) = \<bullet>"
      by auto
  then have "ctZ = []"
    using assms(2) by auto
  then have "pri p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
    =
    (fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> 
      (priacc p (acceptance A) (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    using event_Tock_bullet by auto
  also have "... =
    (fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> acceptance(A) = \<bullet> \<and>
      (priacc p (acceptance A) (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = Tock \<and>
      (maximal(p,event(A)) 
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    using acceptance_not_bullet_imp_priacc event_Tock_bullet by blast
  also have "... =
    (fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> acceptance(A) = \<bullet> \<and>
      (pri p aa zz) \<and> event(A) = Tock \<and> maximal(p,event(A)))"  
    using event_Tock_bullet by auto
  also have "... =
    (ctZ = [] \<and> acceptance(A) = \<bullet> \<and>
      (pri p aa zz) \<and> event(A) = Tock \<and> maximal(p,event(A)))"  
    using assms event_Tock_bullet by auto
  also have "... =
    (ctZ = [] \<and> ctA = [] \<and>
      (pri p aa zz) \<and> event(A) = Tock \<and> maximal(p,event(A)))" 
    using assms(1) by force
  also have "... =
    (ctZ = [] \<and> ctA = [] \<and> (pri p aa zz) \<and> maximal(p,Tock))" 
    using assms(1) by force
  finally show ?thesis .
qed


lemma
  assumes "fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = ctA" "fl2ttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = ctZ"
          "event(Z) \<noteq> Tock"
    shows "pri p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
        =
        (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
         ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> (\<exists>S. fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> event(Z) \<notin> S \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. priref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
proof -
    from assms have event_Tock_bullet:"event(Z) \<noteq> Tock"
      by auto
    then have "ctZ = [event Z]\<^sub>E # fl2ttobs(zz)"
      using assms(2) by auto
    then have "pri p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
      =
      ((priacc p (acceptance A) (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      by auto
    also have "... =
      ((priacc p (acceptance A) (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event A]\<^sub>E # fl2ttobs(aa) \<and>
      (maximal(p,event(A))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      using assms by auto
    also have "... =
      ((priacc p (acceptance A) (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event A]\<^sub>E # fl2ttobs(aa) \<and>
       (maximal(p,event(A))
       \<or> 
       (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
       acceptance(A) \<noteq> \<bullet>))"
      using assms by auto
    also have "... =
      ((priacc p (acceptance A) (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
      (maximal(p,event(Z))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      by auto
    then have p1:"pri p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) = 
      ((priacc p (acceptance A) (acceptance Z)) \<and> (pri p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
      (maximal(p,event(Z))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      using calculation assms by auto

    then have "(pri p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)) =
      (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> event(A) = event(Z))
         \<or> 
        (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b) \<and> event(A) = event(Z))
         \<or>
        (priacc p (acceptance A) (acceptance Z) \<and> acceptance(A) \<noteq> \<bullet> \<and> event(A) = event(Z))))"
      by auto
    also have "... =
      (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> event(A) = event(Z))
         \<or> 
        (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(Z) <\<^sup>*p b))
         \<or>
        (priacc p (acceptance A) (acceptance Z) \<and> acceptance(A) \<noteq> \<bullet> \<and> event(A) = event(Z))))"
      using assms(1) ttobs.inject(1) fl2ttobs.simps(2) by force
    also have "... =
      (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(Z) <\<^sup>*p b))
         \<or>
         (priacc p (acceptance A) (acceptance Z) \<and> acceptance(A) \<noteq> \<bullet>)))"
      using assms(1) ttobs.inject(1) fl2ttobs.simps(2) by force
    also have "... =
      (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(Z) <\<^sup>*p b))
         \<or>
         (\<exists>R S. priref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by (smt acceptance_not_bullet_imp_priacc fl2ttobs.simps(1) list.discI priacc_eq_priref_via_fl2ttobs)
    also have "... =
      (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> (\<exists>S. fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. priref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by auto
    also have "... =
      (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> event(Z) \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> (\<exists>S. fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. priref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by auto
    also have "... =
      (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> event(Z) \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> (\<exists>S. fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> event(Z) \<notin> S \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. priref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by auto
    finally show ?thesis
      using \<open>(pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event A <\<^sup>*p b) \<and> event A = event Z \<or> priacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z)) = (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> priacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z))\<close> \<open>(pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> priacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z)) = (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (maximal(p,event Z) \<and> acceptance A = \<bullet> \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> priacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet>))\<close> \<open>(pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (maximal(p,event Z) \<and> acceptance A = \<bullet> \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> priacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet>)) = (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (maximal(p,event Z) \<and> acceptance A = \<bullet> \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> (\<exists>R S. priref p S = R \<and> fl2ttobs \<langle>acceptance A\<rangle>\<^sub>\<F>\<^sub>\<L> = [[R]\<^sub>R] \<and> fl2ttobs \<langle>acceptance Z\<rangle>\<^sub>\<F>\<^sub>\<L> = [[S]\<^sub>R])))\<close> \<open>pri p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) = (pri p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event A <\<^sup>*p b) \<and> event A = event Z \<or> priacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z))\<close> by auto
        
  qed
*)
lemma fl2ttobs_consFL_eq_Nil: "fl2ttobs (A #\<^sub>\<F>\<^sub>\<L> fl) = [] \<longleftrightarrow> event(A) = Tock \<and> acceptance(A) = \<bullet>"
  by auto

lemma fl2ttobs_consFL_eq_Nil_imp_not_flt2goodTock: 
  assumes "\<forall>Z. A \<noteq> \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>" "fl2ttobs (A) = []"
  shows "\<not> flt2goodTock A"
proof (cases A)
  case (Acceptance x1)
  then show ?thesis using assms by auto
next
  case (AEvent x21 x22)
  have "event(x21) = Tock \<and> acceptance(x21) = \<bullet>"
    using assms AEvent fl2ttobs_consFL_eq_Nil by blast
  then have "\<not> flt2goodTock (x21 #\<^sub>\<F>\<^sub>\<L> x22)"
    by auto
  then have "\<not> flt2goodTock (A)"
    using AEvent by auto
  then show ?thesis by auto
qed

section \<open> Proving that PriMaxTT is obtained from FL \<close>

text \<open> The following auxiliary function is useful to characterise exactly the traces
      @{term fl} that are related by @{term pri} p A fl. It is useful in a number of
      proofs, and furthermore it also ensures that @{term fl} satisfies flt2goodTock.\<close>

fun flt2goodAcceptance :: "('e ttevent) fltrace \<Rightarrow> ('e ttevent) partialorder \<Rightarrow> bool" where
"flt2goodAcceptance \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> p = True" |
"flt2goodAcceptance (A #\<^sub>\<F>\<^sub>\<L> fl) p = 
  (if acceptance(A) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A) \<and> event(A) <\<^sup>*p b) 
      then (flt2goodAcceptance fl p) 
      else (if event(A) = Tock \<or> (event(A) \<noteq> Tick \<and> \<not>maximal(p,event(A))) 
            then False else (flt2goodAcceptance fl p)))"

lemma flt2goodAcceptance_imp_flt2goodTock:
  assumes "flt2goodAcceptance xs p"
  shows "flt2goodTock xs"
  using assms apply(induct xs, auto)
    apply (case_tac x1a, auto, case_tac a, auto)
  apply meson
   apply (case_tac x1a, auto, case_tac b, auto, case_tac a, auto, meson)
  apply (case_tac a, auto, meson)
  by presburger

lemma FLTick0_Tick_Event:
  assumes "S = \<bullet> \<or> ((Event ev) \<in>\<^sub>\<F>\<^sub>\<L> S \<and> Tick \<notin>\<^sub>\<F>\<^sub>\<L> S)"
  shows "FLTick0 Tick {z. z \<le> \<langle>(S,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"
  using assms unfolding FLTick0_def apply auto
   apply (case_tac x, auto)
       apply (case_tac x1, auto)
  apply (simp_all add: less_eq_aevent_def)
    apply (case_tac x21, auto, case_tac x22, auto, case_tac x1, auto, case_tac a, auto)
   apply (case_tac x22, auto, case_tac x1, auto)
  apply (case_tac x, auto)
       apply (case_tac x1, auto)
      apply (simp_all add: less_eq_aevent_def)
  apply (metis (full_types) amember.elims(2) amember.simps(2) less_eq_acceptance.simps(3))
   apply (metis amember.elims(2) ttevent.distinct(3) less_eq_acceptance.simps(3) singleton_iff)
  apply (case_tac x21, auto, case_tac x22, auto, case_tac x1, auto)
  by (case_tac x22, auto, case_tac x1, auto)

lemma fl_le_TT1w_ES_Event:
  assumes "fl \<le> \<langle>([{x. x \<notin> ES}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "[[Event ev]\<^sub>E] \<in> P" "[[ES]\<^sub>R] \<in> P" "Event ev \<notin> ES" "TT1w P"
  shows "fl2ttobs fl \<in> P"
  using assms apply (cases fl, auto)
  apply (simp_all add: less_eq_aevent_def)
    apply (case_tac x1, auto)
  apply (metis (no_types, lifting) Collect_cong Collect_mem_eq mem_Collect_eq)
   apply (case_tac x21, auto, case_tac x22, auto, case_tac x1, auto)
  by (case_tac x22, auto, case_tac x1, auto)

lemma rev_induct_both:
  assumes "List.length xs = List.length ys"
          "P [] []"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> List.length xs = List.length ys \<Longrightarrow> P (xs @ [x]) (ys @ [y]))"
        shows "P xs ys"
proof -
  have revs:"P xs ys = P (List.rev (List.rev xs)) (List.rev (List.rev ys))"
    by auto
  
  have "P (List.rev (List.rev xs)) (List.rev (List.rev ys))"
    apply(rule_tac xs = "List.rev xs" and ys = "List.rev ys" in list_induct2, simp_all)
    using assms by auto
  then show ?thesis using revs by blast
qed

lemma priMaxTT_extend_cons_fl2ttobs_both:
  assumes "priMaxTT p (fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" "last xs = \<bullet>" "last ys = \<bullet>"
  shows "priMaxTT p (fl2ttobs xs) (fl2ttobs ys) s P"
  (* FIXME: There must be a nicer proof. *)
  using assms apply (induct p xs ys arbitrary:x y s rule:pri.induct, auto)
         apply (smt priMaxTT.simps(29) priMaxTT.simps(46) priMaxTT.simps(68))
        apply (smt priMaxTT.simps(29) priMaxTT.simps(46))
       apply (smt priMaxTT.simps(28) priMaxTT.simps(57) priMaxTT.simps(6))
      apply (smt priMaxTT.simps(28) priMaxTT.simps(47))
    apply (smt priMaxTT.simps(28) priMaxTT.simps(29))
   apply (smt priMaxTT.simps(46))
  by (smt priMaxTT.simps(46))

lemma priMaxTT_extend_cons_acceptance_fl2ttobs_both:
  assumes "priMaxTT p (fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" "last xs = \<bullet>" "last ys = \<bullet>"
          "length xs = length ys"
  shows "priMaxTT p (fl2ttobs xs) (fl2ttobs ys) s P"
  (* FIXME: There must be a nicer proof. *)
  using assms apply (induct p xs ys arbitrary:x y s rule:pri.induct, auto)
    apply (smt priMaxTT.simps(18) priMaxTT.simps(19))
   apply (smt priMaxTT.simps(46))
  by (smt priMaxTT.simps(46))

lemma flt2goodAcceptance_extend_consFL_last_fl_e:
  assumes "flt2goodAcceptance fl p" "e \<in>\<^sub>\<F>\<^sub>\<L> last fl" "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> last fl \<and> e <\<^sup>*p b)"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
  using assms apply(induct fl p rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto, case_tac a, auto)
   apply (meson acceptance_event amember.simps(2))
  apply (case_tac A, auto, case_tac a, auto)
  by (metis acceptance_event amember.simps(2))

lemma flt2goodAcceptance_extend_consFL:
  assumes "flt2goodAcceptance fl p" "e \<in>\<^sub>\<F>\<^sub>\<L> X" "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> X \<and> e <\<^sup>*p b)"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(X,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
  using assms apply(induct fl p rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto, case_tac a, auto)
   apply (meson acceptance_event amember.simps(2))
  apply (case_tac A, auto, case_tac a, auto)
  by (metis acceptance_event amember.simps(2))

lemma flt2goodAcceptance_extend_consFL_last_fl_bullet_maximal_pri:
  assumes "flt2goodAcceptance fl p" "last fl = \<bullet>" "maximal(p,e)" "e \<noteq> Tock"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
  using assms apply(induct fl p rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto, case_tac a, auto)
   apply (meson acceptance_event amember.simps(2))
  apply (case_tac A, auto, case_tac a, auto)
  by (metis acceptance_event amember.simps(2))

lemma flt2goodAcceptance_extend_consFL_last_fl_bullet_Tick:
  assumes "flt2goodAcceptance fl p" "last fl = \<bullet>"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
  using assms apply(induct fl p rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto, case_tac a, auto)
   apply (meson acceptance_event amember.simps(2))
  apply (case_tac A, auto, case_tac a, auto)
  by (metis acceptance_event amember.simps(2))

lemma flt2goodAcceptance_extend_consFL_acceptance:
  assumes "flt2goodAcceptance fl p"
  shows "flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>X\<rangle>\<^sub>\<F>\<^sub>\<L>) p"
  using assms apply(induct fl p rule:flt2goodAcceptance.induct, auto)
   apply (case_tac A, auto, case_tac a, auto)
   apply (meson acceptance_event amember.simps(2))
  apply (case_tac A, auto, case_tac a, auto)
  by (metis acceptance_event amember.simps(2))

lemma TTwf_1c_3_imp_fl2ttobs_FL1_mod:
  assumes "x \<in> P" 
      and TTwf_healthy: "TTwf P" 
      and TT1w_healthy: "TT1w P"
      and ttWFx_healthy:  "ttWFx P"
      and TTick_healthy: "TTick P"
      and TT3w_healthy: "TT3w P"
      and pri:"priMaxTT p ar x [] P \<and> x \<in> P"
     (* and tick_Max:"maximal(p,Tick)"*)
  shows "\<exists>fl. x = fl2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
  using assms
proof(induct x arbitrary:ar rule:rev_induct)
  case Nil
  then show ?case 
    apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (rule exI[where x="{\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
    unfolding FL1_def apply auto
    unfolding FLTick0_def apply auto
    by (case_tac s, auto, case_tac x1, auto)
next
  case (snoc x xs)
  then have xs_x_in_P:"xs @ [x] \<in> P"
    by blast
  from snoc have "priMaxTT p (List.butlast ar) xs [] P"
    using priMaxTT_imp_one_butlast_of_priMaxTT
    by metis
  then have "\<exists>ar. priMaxTT p ar xs [] P \<and> xs \<in> P"
    using xs_x_in_P apply auto
    using TT1w_def tt_prefix_concat
    using TT1w_healthy by blast
   
  then have xs_in_P:"xs \<in> P" "ttWF (xs @ [x])"
     apply auto
    using TTwf_def TTwf_healthy xs_x_in_P by blast

  from snoc show ?case
  proof (induct xs rule:rev_induct)
    case Nil
    then show ?case
    proof (cases x)
      case (Ref x1)
      then have "Tick \<in> x1"
        using TTick_def TTick_healthy Nil.prems(8) by blast
      then show ?thesis
          apply (intro exI[where x="\<langle>[{x. x \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
          using Ref apply auto
           apply (rule exI[where x="{z. z \<le> \<langle>[{z. z \<notin> x1} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
        unfolding FLTick0_def apply auto
          apply (case_tac x, auto)
        apply (metis (full_types) amember.elims(2) less_eq_acceptance.simps(3) mem_Collect_eq)
        using FL1_def dual_order.trans apply blast
        using fl_le_TT1w using Nil by auto
    next
      case (ObsEvent x2)
      then have pri_x:"priMaxTT p ar [x] [] P"
        using Nil.prems(8) by auto
      then show ?thesis
      proof (cases x2)
        case (Event ev)
        then show ?thesis
        proof (cases "maximal(p,Event ev)")
          case True
          then show ?thesis using Event
            apply (intro exI[where x="\<langle>(\<bullet>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
            apply (simp add:ObsEvent)
            apply (intro exI[where x="{z. z \<le> \<langle>(\<bullet>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
            unfolding FLTick0_def apply auto
            apply (metis acceptance_set amember.simps(1) bullet_left_zero2 tickWF.simps(1) tickWF.simps(2) x_le_x_concat2 xs_less_eq_z_two_only)
            using FL1_def dual_order.trans apply blast
            using ObsEvent Nil by (simp add: fl_le_TT1w_Event)
        next
          case False
          then obtain ES where ES:"Event ev \<notin> ES \<and> (\<forall>b. ((Event ev) <\<^sup>*p b) \<longrightarrow> b \<in> ES) \<and> [[ES]\<^sub>R] \<in> P"
            using pri_x ObsEvent Event False 
            apply (case_tac ar, simp)
            apply (case_tac ar, simp, case_tac list, simp, case_tac a, simp)          
            apply blast
             apply simp
            using priMaxTT_imp_butlast_of_priMaxTTs by fastforce
          then have "Tick \<in> ES"
            using TTick_healthy by (metis TTick_def append.left_neutral)
          then show ?thesis using ObsEvent Event False ES
            apply (intro exI[where x="\<langle>([{x. x \<notin> ES}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
            apply (simp add:ObsEvent, auto)
            apply (intro exI[where x="{z. z \<le> \<langle>([{x. x \<notin> ES}]\<^sub>\<F>\<^sub>\<L>,Event ev)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"], auto)
              apply (simp add: FLTick0_Tick_Event)
              using FL1_def dual_order.trans apply blast
          using ObsEvent Nil by (simp add: fl_le_TT1w_ES_Event)
      qed
      next
        case Tock
        text \<open> There cannot be a Tock without a refusal before it following ttWF,
               so this case is automatically solved. \<close>
        then show ?thesis
          using Nil.prems(3) ObsEvent
          by (metis TTwf_def Nil.prems(2) append_Nil ttWF.simps(6))
      next
        case Tick
        then show ?thesis
          apply (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
          apply (auto simp add: ObsEvent)
          apply (intro exI[where x="{z. z \<le> \<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"])
          apply auto
          unfolding FLTick0_def apply auto
          apply (metis acceptance_set amember.simps(1) bullet_left_zero2 tickWF.simps(1) tickWF.simps(2) x_le_x_concat2 xs_less_eq_z_two_only)
          using FL1_def dual_order.trans apply blast
          using ObsEvent Nil by (simp add:fl_le_TT1w_Tick)
      qed
    qed
  next
    case yys:(snoc y ys)
    then have priMaxTTyys:"priMaxTT p ar ((ys @ [y]) @ [x]) [] P \<and> (ys @ [y]) @ [x] \<in> P"
      by auto

    from yys have ys_y_inP:"ys @ [y] \<in> P" using TT1w_def
      by (metis tt_prefix_concat)
    from yys have "priMaxTT p (List.butlast ar) (ys @ [y]) [] P"
      using priMaxTT_imp_one_butlast_of_priMaxTT by blast
    then have ys_y_fl:"\<exists>fl. ys @ [y] = fl2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      using ys_y_inP yys by auto
    then have ys_y_x: "\<exists>fl. ys @ [y] @ [x] = fl2ttobs fl @ [x] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
      by auto

    then show ?case
    proof (cases y)
      case r1:(Ref r1)
      then have exp:"\<exists>fl. ys @ [[r1]\<^sub>R] @ [x] = fl2ttobs fl @ [x] \<and> flt2goodAcceptance fl p \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by auto

      then show ?thesis
      proof (cases x)
        case (Ref r2) text \<open>Not allowed\<close>
        then have "\<not>ttWF (ys @ [Ref r1, Ref r2])"
          by (induct ys rule:ttWF.induct, auto)
        then have "ys @ [Ref r1, Ref r2] \<notin> P"
          using assms unfolding TTwf_def by auto
        then show ?thesis using Ref r1 yys by auto
      next
        case (ObsEvent e1)
        then show ?thesis
        proof (cases e1)
          case (Event e2)
          then have "\<not>ttWF (ys @ [Ref r1, [Event e2]\<^sub>E])"
            by (induct ys rule:ttWF.induct, auto)
          then show ?thesis
            using assms unfolding TTwf_def
            by (metis Cons_eq_append_conv Event ObsEvent append_eq_appendI r1 ys_y_x yys.prems(2))
        next
          case Tock
          then have tock_not_in_r1: "Tock \<notin> r1"
            using ttWFx_any_cons_end_tock ttWFx_healthy ObsEvent r1 yys.prems(2) by auto
          then have r1_good_pri:"\<not>(\<exists>b. b \<notin> r1 \<and> Tock <\<^sup>*p b)"
            using r1 ObsEvent Tock priMaxTTyys priMaxTT_rhs_refTock_imp_no_gt_Tock_pri
            by (metis TTwf_def TTwf_healthy append.assoc append_Cons append_Nil)
          
          text \<open>Then from the hypothesis we have the case:\<close>

          then obtain fl where fl:"ys @ [Ref r1] = fl2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and>  {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using r1 ys_y_fl by blast
          then have last_fl_acceptance:"last fl = [{x. x \<notin> r1}]\<^sub>\<F>\<^sub>\<L>"
            by (metis (mono_tags, lifting) last_fl2ttobs_eq_ref_imp_last snoc_eq_iff_butlast)
          then have r1_good_pri_acceptance:"\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> r1}]\<^sub>\<F>\<^sub>\<L> \<and> e1 <\<^sup>*p b)"
            using ObsEvent Tock r1_good_pri 
            by simp
          then have tock_in_last_fl: "Tock \<in>\<^sub>\<F>\<^sub>\<L> last fl"
            using last_fl_acceptance tock_not_in_r1 by simp
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            by (simp add: fl)
          then have "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using tock_in_last_fl by (simp add: fl2ttobs_last_tock fl)

          have "{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le> fl} \<subseteq> P"
            using TT1w_healthy 
            using FL1_def fl subset_eq by blast

          have fl2ttobs_strongFL_subset:"{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_fl2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy ObsEvent Tock \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs fl @ [[Tock]\<^sub>E] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl r1 yys.prems(2))

          have "(ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x))"
            using \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> tock_in_last_fl by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FL1_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by (metis (mono_tags, lifting) Collect_cong \<open>ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(Finite_Linear_Model.last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> fl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl  
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using FLTick0_extends_strong_less_eq_fltrace_last tock_in_last_fl
            by auto
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                    \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                    \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"
            using fl2ttobs_strongFL_subset
            by (smt Un_iff mem_Collect_eq subset_iff)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                \<and> fl \<in> x
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            by blast
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            using tock_in_last_fl by (simp add:flt2goodTock_extend_consFL_last_fl_e)
          then have 
               "ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                \<and> flt2goodAcceptance fl p 
                \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                \<and> flt2goodTock fl 
                \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z
                \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
            using flt2goodAcceptance_extend_consFL_last_fl_e
            by (metis (mono_tags, lifting) Tock last_fl_acceptance r1_good_pri_acceptance tock_in_last_fl)
          then have 
               "\<exists>fl. ys @ [[r1]\<^sub>R] @ [[Tock]\<^sub>E] = fl2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
            by blast
          then show ?thesis using Tock ObsEvent r1 by auto
        next
          case Tick
          then have "\<not>ttWF (ys @ [Ref r1, [Tick]\<^sub>E])"
            by (induct ys rule:ttWF.induct, auto)
          then show ?thesis
            using TTwf_healthy unfolding TTwf_def
            by (metis ObsEvent Tick append.assoc append_Cons append_Nil r1 ys_y_x yys.prems(2))
        qed
      qed
    next
      case e1:(ObsEvent e1)
      text \<open>Then from the hypothesis we have the case:\<close>
      then obtain fl where fl:"ys @ [[e1]\<^sub>E] = fl2ttobs fl \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        using ys_y_fl by blast
      then have ys_e1_x:"ys @ [[e1]\<^sub>E] @ [x] = fl2ttobs fl @ [x] \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x)"
        by auto
      then have last_fl:"last fl = \<bullet>"
        by (metis ttobs.distinct(1) fl fl2ttobs.simps(1) fl2ttobs_last_fl_not_bullet_dist_list_cons last_snoc)

      then show ?thesis
      proof (cases x)
        case e2:(ObsEvent e2)
        then have "ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E] \<in> P"
          using e1 fl ys_e1_x yys.prems(2) by presburger
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using TTwf_healthy TTwf_concat_prefix_set_no_Tick
          using e1 e2 yys.prems(2) by blast
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_fl2ttobs_imp_not_in_events fl)
          
        then show ?thesis
        proof (cases e2)
          case (Event e3)
          have "priMaxTT p ar (ys @ [[e1]\<^sub>E,[Event e3]\<^sub>E]) [] P \<and> (ys @ [[e1]\<^sub>E,[Event e3]\<^sub>E]) \<in> P"
             using priMaxTTyys e1 Event e2 by auto
          then show ?thesis
          proof (cases "maximal(p,Event e3)")
            case True
            then have fl2ttobs_strongFL_subset:"{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
              apply auto
              using strong_less_eq_fltrace_imp_fl2ttobs_tt
              by (metis (no_types, lifting) TT1w_def TT1w_healthy Event ttevent.simps(3) e1 e2 fl fl2ttobs_last_non_tock last_fl last_snoc yys.prems(2))
          
            from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs fl @ [[Event e3]\<^sub>E]
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              using ys_e1_x by auto
            also have "... =
                    (ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
              proof -
                from fl have "ys @ [[e1]\<^sub>E] = fl2ttobs fl"
                  by auto
                then have "List.last(fl2ttobs fl) = [e1]\<^sub>E"
                  by (metis last_snoc)
                then have "fl2ttobs fl @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  using fl last_fl fl2ttobs_last_non_tock
                  by (metis (no_types, lifting) ttevent.distinct(1))
                then show ?thesis using calculation  by auto
              qed
            finally have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
                apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
              by fastforce
            then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
              by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
             using fl2ttobs_strongFL_subset ttWFx_trace_cons_imp_cons
             by (smt Un_iff mem_Collect_eq subset_iff)
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                        \<and> fl \<in> x
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
              by (simp add: strong_less_eq_fltrace_refl)  
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
             by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
             using last_fl flt2goodTock_extend_consFL_last_fl_bullet
             by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p 
                    \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                    \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
             using flt2goodAcceptance_extend_consFL_last_fl_bullet_maximal_pri
             by (metis (no_types, lifting) True acceptance_event acceptance_set append_self_conv bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL fl_e3 fl2ttobs.simps(2) fl2ttobs_acceptance_cons_eq_list_cons last_fl not_Cons_self2)
           then have "
                    \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
             by blast
           then show ?thesis using Event e1 e2 by auto
          next
            case False
            then obtain Z where Z:"ys @ [[e1]\<^sub>E] @ [[Z]\<^sub>R] \<in> P \<and> Event e3 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> Event e3 <\<^sup>*p b)"
              using priMaxTT_nonmax_Tock_imp_exists_refusal
              by (metis TTwf_def TTwf_healthy Event append.assoc append_Nil ttevent.distinct(1) e1 e2 priMaxTTyys)
            then have Tick_in_Z:"Tick \<in> Z"
              using TTick_healthy
              by (metis TTick_def append_assoc)
            
            have "fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
              using fl Z
              by (metis (mono_tags, lifting) Nil_is_append_conv append.assoc fl2ttobs_fl_acceptance last_snoc not_Cons_self2)
            then have "fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
            proof -
              have "fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                    =
                    fl2ttobs (fl) @ fl2ttobs(\<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl e2 Event last_fl 
                by (metis (no_types, lifting) bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL fl2ttobs_acceptance_cons_eq_list_cons)
              also have "... = ys @ [[e1]\<^sub>E] @ fl2ttobs(\<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl by auto
              also have "... = ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E]"
                using Z by auto
              then show ?thesis
                using Event \<open>ys @ [[e1]\<^sub>E] @ [[e2]\<^sub>E] \<in> P\<close> calculation by auto
            qed

            (* Need to pick a different last fl here, which is prioritised instead ! *)
            then have fl2ttobs_strongFL_subset:"{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
              using False strong_less_eq_fltrace_imp_fl2ttobs_tt TT1w_def TT1w_healthy Event ttevent.simps(3) e1 e2 fl fl2ttobs_last_non_tock last_fl last_snoc yys.prems(2)
              using \<open>fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P\<close> by blast

            from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs fl @ [[Event e3]\<^sub>E]
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              using ys_e1_x by auto
            also have "... =
                    (ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
              proof -
                from fl have "ys @ [[e1]\<^sub>E] = fl2ttobs fl"
                  by auto
                then have "List.last(fl2ttobs fl) = [e1]\<^sub>E"
                  by (metis last_snoc)
                then have "fl2ttobs fl @ [[Event e3]\<^sub>E] = fl2ttobs(fl) @ fl2ttobs(\<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  using Z by auto
                also have "... = ys @ [[e1]\<^sub>E] @ fl2ttobs(\<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  by (simp add: fl)
                also have "... = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                  using fl last_fl fl2ttobs_last_non_tock
                  by (metis (no_types, lifting) \<open>fl2ttobs fl @ fl2ttobs \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = ys @ [[e1]\<^sub>E] @ fl2ttobs \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL fl2ttobs_acceptance_cons_eq_list_cons)
                then show ?thesis using calculation
                  using fl_e3 by auto
              qed
            finally have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick x \<and> FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              using FL1_extends_strong_less_eq_fltrace_last_bullet' last_fl
              proof -
                assume "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs fl @ [[Event e3]\<^sub>E] \<and> ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
                then obtain FF :: "'a ttevent fltrace set" where
                  f1: "ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs fl @ [[Event e3]\<^sub>E] \<and> ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> FLTick0 Tick FF \<and> FL1 FF \<and> {fl2ttobs f |f. f \<in> FF} \<subseteq> P \<and> fl \<in> FF"
                  by blast
                have f2: "\<forall>f c a F. (((FL1 (F \<union> {fa. fa \<le>\<^sub>\<F>\<^sub>\<L> f @\<^sub>\<F>\<^sub>\<L> \<langle>a\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> fa \<le>\<^sub>\<F>\<^sub>\<L> f @\<^sub>\<F>\<^sub>\<L> \<langle>(a,c)\<^sub>\<F>\<^sub>\<L>,Finite_Linear_Model.last fl\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<or> Finite_Linear_Model.last f \<noteq> Finite_Linear_Model.last fl) \<or> f \<notin> F) \<or> c \<notin>\<^sub>\<F>\<^sub>\<L> a) \<or> \<not> FL1 F"
                  by (metis (no_types) FL1_extends_strong_less_eq_fltrace_last_bullet' last_fl)
                have "Event e3 \<in>\<^sub>\<F>\<^sub>\<L> [{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>"
                  by (simp add: Z)
                then have "\<exists>F. ((FL1 (F \<union> {f. f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,Finite_Linear_Model.last fl\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {fl2ttobs f |f. f \<in> F} \<subseteq> P) \<and> fl \<in> F) \<and> FLTick0 Tick F"
                  using f2 f1 by blast
                then show ?thesis
                  using f1 last_fl by auto
              qed
            then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet' last_fl Tick_not_in_events_fl
              proof -
                fix xb :: "'a ttevent fltrace set"
                assume a1: "FL1 (xb \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
                  assume a2: "{fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> xb} \<subseteq> P"
                  assume a3: "fl \<in> xb"
                  assume a4: "FLTick0 Tick xb"
                  have "Tick \<in> Z"
                    using Tick_in_Z by auto
                  then have "FLTick0 Tick (xb \<union> {f. f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,Finite_Linear_Model.last fl\<rangle>\<^sub>\<F>\<^sub>\<L>})"
                    using a4 a3 by (simp add: FL0_Tick_extends_strong_less_eq_fltrace_last_bullet' Tick_not_in_events_fl Z last_fl)
                  then show "\<exists>F. FLTick0 Tick (F \<union> {f. f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> FL1 (F \<union> {f. f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> f \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{c. c \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {fl2ttobs f |f. f \<in> F} \<subseteq> P \<and> fl \<in> F"
                    using a3 a2 a1 last_fl by auto
                qed
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}} \<subseteq> P \<and> fl \<in> x)"    
             using fl2ttobs_strongFL_subset
             by (smt Un_iff mem_Collect_eq subset_iff)
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> FL1(x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}} \<subseteq> P 
                        \<and> fl \<in> x
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<or> fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"    
             by (simp add: strong_less_eq_fltrace_refl)
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                    \<and> (\<exists>z. FLTick0 Tick z 
                        \<and> FL1 z 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"   
             by blast
           then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p 
                    \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z 
                        \<and> FL1 z 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"   
             using flt2goodTock_extend_consFL_last_e'
             by (simp add: flt2goodTock_extend_consFL_last_e' Z)
            then have "
                    ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> flt2goodAcceptance fl p 
                    \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p 
                    \<and> flt2goodTock fl 
                    \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                    \<and> (\<exists>z. FLTick0 Tick z 
                        \<and> FL1 z 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>([{x. x \<notin> Z}]\<^sub>\<F>\<^sub>\<L>,Event e3)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"   
              using Z
              by (simp add: flt2goodAcceptance_extend_consFL)
           then have "
                    \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Event e3]\<^sub>E] = fl2ttobs fl
                    \<and> flt2goodAcceptance fl p 
                    \<and> flt2goodTock fl
                    \<and> (\<exists>z. FLTick0 Tick z 
                        \<and> FL1 z 
                        \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                        \<and> fl \<in> z)"   
             by blast
           then show ?thesis 
             by (metis (no_types, lifting) Event e1 e2 fl fl_e3)
         qed
        next
          case Tock
          then have "\<not>ttWF (ys @ [[e1]\<^sub>E, [Tock]\<^sub>E])"
            apply (induct ys rule:ttWF.induct, auto)
            using ttWF.elims(2) ttWF.simps(6) by blast+
          then show ?thesis
            using e1 e2 TTwf_healthy unfolding TTwf_def
            by (metis Tock append_eq_Cons_conv fl ys_e1_x yys.prems(2))
        next
          case Tick
          have fl2ttobs_strongFL_subset:"{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_fl2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy Tick ttevent.distinct(5) e1 e2 fl fl2ttobs_last_non_tock last_fl last_snoc yys.prems(2))
            
          from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs fl @ [[Tick]\<^sub>E]
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            using ys_e1_x by auto
          also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
            proof -
              from fl have "ys @ [[e1]\<^sub>E] = fl2ttobs fl"
                by auto
              then have "List.last(fl2ttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "fl2ttobs fl @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl fl2ttobs_last_non_tock
                by (metis (no_types, lifting) ttevent.simps(7))
              then show ?thesis using calculation  by auto
            qed
          finally have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_last_bullet last_fl 
            by fastforce
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          apply auto using FL0_Tick_extends_strong_less_eq_fltrace_last_bullet last_fl Tick_not_in_events_fl
            by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
           using fl2ttobs_strongFL_subset 
           by (smt Un_iff mem_Collect_eq subset_iff)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"
            by (simp add: strong_less_eq_fltrace_refl)  
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using last_fl flt2goodTock_extend_consFL_last_fl_bullet
           by blast
         then have "
                  ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p 
                  \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                  \<and> flt2goodTock fl 
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>(last fl,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
           using flt2goodAcceptance_extend_consFL_last_fl_bullet_Tick
           by (metis (no_types, lifting) bullet_right_zero2 butlast_last_cons2_FL fl_cons_acceptance_consFL fl_e3 last_fl)
         then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[Tick]\<^sub>E] = fl2ttobs(fl)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P \<and> fl \<in> z)"
           by blast
         then show ?thesis using Tick e1 e2 by auto
        qed
      next
        case (Ref r2)
        have Tick_in_r2:"Tick \<in> r2"
          using TTick_healthy Ref TTick_def xs_x_in_P by blast
        then have "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] \<in> P"
          using e1 Ref yys.prems(2) by auto
        then have "[Tick]\<^sub>E \<notin> set (ys @ [[e1]\<^sub>E])" 
          using TTwf_healthy TTwf_concat_prefix_of_ref_set_no_Tick
          using e1 Ref
          by (metis fl ys_e1_x)
        then have Tick_not_in_events_fl: "Tick \<notin> events fl"
          by (simp add: event_not_in_set_of_fl2ttobs_imp_not_in_events fl)

        from fl have fl_e3: "ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs fl @ [[r2]\<^sub>R]
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
          using ys_e1_x by auto
        also have "... =
                  (ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 x \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x))"
          proof -
              from fl have "ys @ [[e1]\<^sub>E] = fl2ttobs fl"
                by auto
              then have "List.last(fl2ttobs fl) = [e1]\<^sub>E"
                by (metis last_snoc)
              then have "fl2ttobs fl @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
                using fl last_fl fl2ttobs_fl_acceptance Tick_in_r2
              proof -
                have "fl2ttobs fl \<noteq> []"
                  by (metis (no_types) append_is_Nil_conv fl not_Cons_self2)
                then show ?thesis
                  by (simp add: Tick_in_r2 \<open>List.last (fl2ttobs fl) = [e1]\<^sub>E\<close> fl fl2ttobs_fl_acceptance)
                qed
              then show ?thesis using calculation by auto
            qed
         finally have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
              apply auto using FL1_extends_strong_less_eq_fltrace_acceptance last_fl 
           by fastforce 
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2}- {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)"
            apply auto using FL0Tick_extends_strong_less_eq_fltrace_acceptance last_fl Tick_in_r2 Tick_not_in_events_fl
           by (smt Collect_cong Diff_empty Diff_insert0 FLTick0_def Un_iff amember.simps(2) mem_Collect_eq tickWF_concatFL_acceptance_imp tickWF_prefix_imp)
         then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P \<and> fl \<in> x)"  
         proof -
           have
            "{fl2ttobs fl\<^sub>0|fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)} \<subseteq> P"
            apply auto
            using strong_less_eq_fltrace_imp_fl2ttobs_tt
            by (metis (no_types, lifting) TT1w_def TT1w_healthy Ref \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick x \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> e1 fl fl_e3 yys.prems(2))
          then show ?thesis 
            by (smt Un_iff \<open>ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}) \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> x} \<subseteq> P \<and> fl \<in> x)\<close> mem_Collect_eq subset_eq)
        qed
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>x. FLTick0 Tick (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})
                      \<and> FL1 (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}) 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)})} \<subseteq> P 
                      \<and> fl \<in> x
                      \<and> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> (x \<union> {fl\<^sub>0. fl\<^sub>0 \<le>\<^sub>\<F>\<^sub>\<L> (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)}))"  
         by (simp add: strong_less_eq_fltrace_refl)  
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          by blast
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          using flt2goodTock_extend_consFL_acceptance by blast
        then have "
                  ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> flt2goodAcceptance fl p 
                  \<and> flt2goodAcceptance (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) p
                  \<and> flt2goodTock fl
                  \<and> flt2goodTock (fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) 
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl @\<^sub>\<F>\<^sub>\<L> \<langle>[{x. x \<notin> r2} - {Tick}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> z)"
          by (simp add: flt2goodAcceptance_extend_consFL_acceptance)
        then have "
                  \<exists>fl. ys @ [[e1]\<^sub>E] @ [[r2]\<^sub>R] = fl2ttobs(fl)
                  \<and> flt2goodAcceptance fl p \<and> flt2goodTock fl
                  \<and> (\<exists>z. FLTick0 Tick z \<and> FL1 z 
                      \<and> {fl2ttobs fl\<^sub>0 |fl\<^sub>0. fl\<^sub>0 \<in> z} \<subseteq> P 
                      \<and> fl \<in> z)"
          by blast
        then show ?thesis using Ref e1 by auto
        qed
    qed
  qed
qed

lemma fl2ttobs_cons_no_extend_not_flt2goodTock:
  assumes "\<not> flt2goodTock fl"
  shows "fl2ttobs (fl &\<^sub>\<F>\<^sub>\<L> xs) = fl2ttobs(fl)"
  using assms apply (induct fl rule:fl2ttobs.induct, auto)
  by (case_tac A, auto)

lemma fl2ttobs_cons_acceptance_eq_cons:
  assumes "last fl = \<bullet>" "flt2goodTock fl"
  shows "fl2ttobs (fl &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs(fl) @ fl2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct fl rule:fl2ttobs.induct, auto)

lemma prirel_flt2goodTock_tgt_imp_src:
  assumes "pri p fl Y" "flt2goodTock fl"
  shows "flt2goodTock Y"
  using assms apply (induct p fl Y rule:pri.induct, auto)
       apply (case_tac A, auto, case_tac a, auto)
      apply (case_tac A, auto, case_tac a, auto)
     apply (case_tac A, auto, case_tac a, auto)
    apply (case_tac A, auto, case_tac a, auto)
   apply (case_tac A, auto, case_tac a, auto)
  by (case_tac A, auto, case_tac a, auto)

lemma priMaxTT_extend_both_events_non_maximal_ttWF:
  assumes "priMaxTT p xs ys s P" "ttWF (xs @ [[e\<^sub>1]\<^sub>E])" "ttWF (ys @ [[e\<^sub>1]\<^sub>E])" "TTwf P"
          "(\<exists>Z. s @ ys @ [[Z]\<^sub>R] \<in> P \<and> e\<^sub>1 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>1 <\<^sup>*p b))" 
  shows "priMaxTT p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:priMaxTT.induct, auto)
    apply (cases e\<^sub>1) apply auto[1]
  using TTwf_cons_end_not_refusal_refusal apply blast+
  by (metis append_Nil ttWF.simps(10) ttWF.simps(4) ttWF.simps(6) ttWF_prefix_is_ttWF ttevent.exhaust list.exhaust)+

lemma flt2goodTock_cons_imp_prefix:
  assumes "flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> ys)"
  shows "flt2goodTock (xs)"
  using assms by(induct xs, auto)

lemma prirel_rhs_tickWF_imp_lhs_tickWF:
  assumes "pri p xs ys" "tickWF Tick ys"
  shows "tickWF Tick xs"
  using assms pri_tickWF
  by fastforce

lemma prirel_cons_lasts_bullet_cons_bullet_iff:
  assumes "last xs = \<bullet>" "last ys = \<bullet>"
          "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        shows "x = \<bullet> \<longleftrightarrow> y = \<bullet>"
  using assms apply(induct p xs ys rule:pri.induct, auto)
  by (cases y, auto)
  
lemma fl2ttobs_is_ttWFx_trace [simp]:
  "ttWFx_trace (fl2ttobs xs)"
  apply (induct xs)
   apply (case_tac x, simp)
   apply auto[1]
  apply (case_tac x1a, case_tac y, case_tac a)
   apply auto[1]
   apply (metis ttWFx_trace.simps(2) ttWFx_trace.simps(4) neq_Nil_conv)
  apply (case_tac b, auto)
  apply (metis ttWFx_trace.simps(2) ttWFx_trace.simps(4) neq_Nil_conv)
  by (metis ttWFx_trace.simps(2) ttWFx_trace.simps(4) neq_Nil_conv)

text \<open> Key result below for establishing the connection with priMaxTT. \<close>

lemma pri_to_priMaxTT:
  assumes "pri p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2ttm fl\<^sub>0 \<subseteq> P"
          "fl2ttobs Y \<in> P"
          "flt2goodTock fl" "TTwf P"
    shows "priMaxTT p (fl2ttobs fl) (fl2ttobs Y) [] P"
  using assms  
proof (induct fl Y rule:ftrace_cons_induct_both_eq_length)
  case 1
  then show ?case using assms(1) prirel_same_length by blast
next
  case (2 x y)
  then show ?case 
    apply (cases y, auto)
       apply (cases x, auto)
     apply (cases x, auto)
    unfolding prirefMaxTT_def by auto
next
  case (3 x y xs ys)
  then have priMaxTT:"priMaxTT p (fl2ttobs xs) (fl2ttobs ys) [] P"
    by (metis (mono_tags, lifting) flt2goodTock_cons_imp_prefix fl2ttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1 prirel_cons_eq_length_imp_prirel_eq_prefix)
  then show ?case using 3
  proof (cases "flt2goodTock xs")
    case True
    then have "flt2goodTock ys"
      using 3 prirel_cons_eq_length_imp_prirel_eq_prefix prirel_flt2goodTock_tgt_imp_src by blast
    then have flt2_ys_y:"fl2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs (ys) @ fl2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using 3 by (simp add: fl2ttobs_cons_acceptance_eq_cons)
    then have "fl2ttobs (ys) @ fl2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
      using 3 by (simp)
    then show ?thesis using 3
      proof (cases x)
        case xnil:acnil
        then have "y = \<bullet>"
          using prirel_cons_lasts_bullet_cons_bullet_iff
          using "3.hyps"(3) "3.hyps"(4) "3.prems"(1) by blast
        then show ?thesis 
          using priMaxTT xnil by auto
      next
        case (acset x2)
        then obtain yA where yA:"y = [yA]\<^sub>\<F>\<^sub>\<L>"
          using "3.hyps"(3) "3.hyps"(4) "3.prems"(1) prirel_last_bullets_cons_imp by blast
        then have "pri p \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>[yA]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
          using "3.hyps"(2) "3.hyps"(3) "3.hyps"(4) "3.prems"(1) acset prirel_cons_eq_length_imp_prirel_acceptances_eq by blast
        then have prirefMaxTT_yA_x2:"prirefMaxTT p {x. x \<notin> yA} = {x. x \<notin> x2}"
          using yA unfolding prirefMaxTT_def by auto
        then obtain xR where xR:"fl2ttobs(\<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[xR]\<^sub>R]"
          by (simp add: acset)
        then obtain yR where yR:"fl2ttobs(\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> prirefMaxTT p yR = xR"
          using 3 yA prirefMaxTT_yA_x2  acceptance.distinct(1) acset fl2ttobs.simps(1) pri.simps(1) priacc_eq_priref_via_fl2ttobs
          by (cases x, auto)
          
        have "ttWF (fl2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          by (meson "3.prems"(4) FLTick0_def assms(3) fl2ttobs_is_ttWF)
        then have "ttWF ((fl2ttobs ys) @ [[yR]\<^sub>R])"
          by (metis flt2_ys_y yR)
        then have "priMaxTT p ((fl2ttobs xs) @ [[xR]\<^sub>R]) ((fl2ttobs ys) @ [[yR]\<^sub>R]) [] P"
          using priMaxTT_extend_both_refusal_ttWF
          using priMaxTT yR by blast
        then show ?thesis
          using "3.hyps"(3) True flt2_ys_y fl2ttobs_cons_acceptance_eq_cons xR yR by fastforce
      qed
  next
    case False
    then have flt2_xsx:"fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs (xs)"
      by (simp add: fl2ttobs_cons_no_extend_not_flt2goodTock)
    then have "y = \<bullet>"
      using prirel_cons_lasts_bullet_cons_bullet_iff
      using "3.prems"(7) False flt2goodTock_cons_imp_prefix by blast
    then show ?thesis
      by (simp add: flt2_xsx priMaxTT)
  qed
next
  case (4 x y xs ys)
  then have xs_is_flt2goodTock:"flt2goodTock xs"
    using flt2goodTock_cons_imp_prefix by blast
  then have ys_is_flt2goodTock:"flt2goodTock ys"
    using "4.hyps"(2) "4.prems"(1) prirel_cons_eq_length_imp prirel_flt2goodTock_tgt_imp_src by blast
  then have priMaxTT:"priMaxTT p (fl2ttobs xs) (fl2ttobs ys) [] P"
    using prirel_cons_eq_length_imp 4
    by (metis (mono_tags, lifting) xs_is_flt2goodTock fl2ttobs_extn mem_Collect_eq subset_eq x_le_concat2_FL1)
  then have "pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    using "4.hyps"(2) "4.hyps"(3) "4.prems"(1) prirel_cons_eq_length_imp_prirel_acceptances by blast
 
  from xs_is_flt2goodTock ys_is_flt2goodTock
  have flt2_ys_y:"fl2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs (ys) @ fl2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using 4 fl2ttobs_acceptance_cons_eq_list_cons by blast
  then have "fl2ttobs (ys) @ fl2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
    using 4 by (simp)

  from xs_is_flt2goodTock ys_is_flt2goodTock
  have flt2_xs_x:"fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = fl2ttobs (xs) @ fl2ttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using 4 fl2ttobs_acceptance_cons_eq_list_cons
    by blast

  then obtain yA yEvent where 
    yAE:"y = (yA,yEvent)\<^sub>\<F>\<^sub>\<L> \<and> (yA = \<bullet> \<or> yEvent \<in>\<^sub>\<F>\<^sub>\<L> yA)"
    by (cases y, auto)
  then obtain xA where 
    xAE:"x = (xA,yEvent)\<^sub>\<F>\<^sub>\<L> \<and> (xA = \<bullet> \<or> yEvent \<in>\<^sub>\<F>\<^sub>\<L> xA)"
    apply (cases x, auto)
    using 4 \<open>pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> by auto

  then show ?case
    proof (cases "yEvent = Tock")
      case True 
      then have xA_not_bullet:"xA \<noteq> \<bullet>"
        using \<open>flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)\<close> \<open>last xs = \<bullet>\<close>
        proof (induct xs)
          case (Acceptance z)
          then show ?case using xAE by auto
        next
          case (AEvent x1a xs)
          then show ?case apply auto
            by presburger
        qed
      then have yA_not_bullet:"yA \<noteq> \<bullet>"
        by (metis \<open>\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> pri\<^sub>[\<^sub>p\<^sub>] \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance_set not_bullet_less_eq_imp pri.simps(4) priacc.simps(1) xAE yAE)

      then have prirefMaxTT_yA_x2:"prirefMaxTT p {x. x \<notin>\<^sub>\<F>\<^sub>\<L> yA} = {x. x \<notin>\<^sub>\<F>\<^sub>\<L> xA}"
        using yAE xAE \<open>\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> pri\<^sub>[\<^sub>p\<^sub>] \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> unfolding prirefMaxTT_def  apply auto
             apply (cases yA, auto, cases xA, auto)
             apply (metis (mono_tags, lifting) Int_Collect)
            apply (cases yA, auto, cases xA, auto)
            apply (metis (no_types, lifting) Int_Collect)
           apply (cases yA, auto, cases xA, auto)
        using xA_not_bullet apply blast
        using xA_not_bullet apply blast
         apply (cases yA, auto, cases xA, auto)
        apply (smt Int_Collect)
        apply (cases yA, auto, cases xA, auto)
        by (smt Int_Collect) (* TODO: Fix the above *)
      then obtain xR where xR:"fl2ttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[xR]\<^sub>R,[Tock]\<^sub>E]"
        using True xAE xA_not_bullet by auto
      then obtain yR where yR:"fl2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R,[Tock]\<^sub>E] \<and> prirefMaxTT p yR = xR"
        using True xAE yAE xA_not_bullet apply auto
        using yA_not_bullet apply simp
        using yA_not_bullet apply simp
        using prirefMaxTT_yA_x2 \<open>pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acceptance_set fl2ttobs.simps(1) pri.simps(4) priacc_eq_priref_via_fl2ttobs less_eq_acceptance.elims(2) 
        by auto
        
      then have "ttWF (fl2ttobs (ys) @ [[yR]\<^sub>R,[Tock]\<^sub>E])"
        by (metis "4.prems"(4) FLTick0_def True assms(3) flt2_ys_y fl2ttobs_is_ttWF)
      then have "priMaxTT p (fl2ttobs (xs) @ [[xR]\<^sub>R,[Tock]\<^sub>E]) (fl2ttobs (ys) @ [[yR]\<^sub>R,[Tock]\<^sub>E]) [] P"
        using priMaxTT priMaxTT_extend_both_tock_refusal_ttWF
        using yR
        by (metis ttWFx_trace.simps(3) fl2ttobs_is_ttWFx_trace xR)
      then have "priMaxTT p (fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)) [] P"
        using flt2_xs_x flt2_ys_y xR yR by auto
      then show ?thesis by auto
    next
      case False
      then have "fl2ttobs(\<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yEvent]\<^sub>E]"
        using xAE by auto
      then have "fl2ttobs(\<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yEvent]\<^sub>E]"
        using xAE yAE
        using False by fastforce

      then have ttWF_ys_y:"ttWF (fl2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        using 4 
        by (meson FLTick0_def fl2ttobs_is_ttWF)

      then have ttWF_xs_x:"ttWF (fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
        using 4 
        using prirel_rhs_tickWF_imp_lhs_tickWF
        by (metis FLTick0_def fl2ttobs_is_ttWF)

      then have "priMaxTT p (fl2ttobs (xs) @ [[yEvent]\<^sub>E]) (fl2ttobs (ys) @ [[yEvent]\<^sub>E]) [] P"
        using priMaxTT
      proof (cases "maximal(p,yEvent)")
        case True
        then show ?thesis
          by (metis \<open>fl2ttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>fl2ttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> ttWF_xs_x ttWF_ys_y flt2_xs_x flt2_ys_y fl2ttobs_is_ttWFx_trace priMaxTT priMaxTT_extend_both_events_maximal_ttWF)
      next
        case False
        then show ?thesis
          proof (cases "xA")
            case acnil
            then have "yA \<noteq> \<bullet>"
              using False \<open>pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> xAE yAE by auto
            then have "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> yA \<and> yEvent <\<^sup>*p b)"
              by (metis \<open>pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> amember.elims(2) amember.simps(2) not_prirelAlt_less_eq_both_events yAE)

            from 4 have "ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> fl\<^sub>0"
              by auto
            then have "ys &\<^sub>\<F>\<^sub>\<L> \<langle>yA\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> fl\<^sub>0"
              using 4 fltrace_FL1_cons_acceptance_prefix yAE
              by (metis acceptance_set)
            then have "fl2ttobs(ys &\<^sub>\<F>\<^sub>\<L> \<langle>yA\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
              using 4 fl2ttm_def by blast
            then obtain yR where yR:"fl2ttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> fl2ttobs(\<langle>yA\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> yEvent \<notin> yR"
              using "4.hyps"(4) \<open>yA \<noteq> \<bullet>\<close> fl2ttobs_cons_acceptance_eq_cons yAE ys_is_flt2goodTock by fastforce
            then have "fl2ttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> yEvent \<notin> yR \<and> \<not>(\<exists>b. b \<notin> yR \<and> yEvent <\<^sup>*p b)"
              using \<open>\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> yA \<and> yEvent <\<^sup>*p b\<close> \<open>yA \<noteq> \<bullet>\<close> by auto
            then show ?thesis
              by (metis \<open>fl2ttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>fl2ttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> append_Nil assms(8) ttWF_xs_x ttWF_ys_y flt2_xs_x flt2_ys_y priMaxTT priMaxTT_extend_both_events_non_maximal_ttWF)
              
          next
            case (acset x2)
            then have "yA \<noteq> \<bullet>"
              using \<open>pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> xAE yAE by auto
            then obtain yASet where yASet:"[yASet]\<^sub>\<F>\<^sub>\<L> = yA \<and> yEvent \<in> yASet"
              using yAE by (cases yA, auto)
            then have "x2 = {a. a \<in> yASet \<and> \<not>(\<exists>b. b\<in>yASet \<and> a <\<^sup>*p b)}"
              using \<open>pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset xAE yAE False apply auto
                apply (metis (no_types, lifting) IntE)  
               apply (metis (no_types, lifting) Int_Collect)
            by (smt Int_Collect)
      
            then have "fl2ttobs(ys &\<^sub>\<F>\<^sub>\<L> \<langle>[yASet]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<in> P"
              by (metis (mono_tags, lifting) "4"(6) "4"(8) "4"(9) acceptance_set contra_subsetD fl2ttm_def fltrace_FL1_cons_acceptance_prefix mem_Collect_eq yAE yASet)
            then obtain yR where yR:"fl2ttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> fl2ttobs(\<langle>[yASet]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[yR]\<^sub>R] \<and> yEvent \<notin> yR"
              using "4.hyps"(4) \<open>yA \<noteq> \<bullet>\<close> fl2ttobs_cons_acceptance_eq_cons yAE yASet ys_is_flt2goodTock by fastforce
            then have "fl2ttobs (ys) @ [[yR]\<^sub>R] \<in> P \<and> yEvent \<notin> yR \<and> \<not>(\<exists>b. b \<notin> yR \<and> yEvent <\<^sup>*p b)"
              using \<open>pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> acset xAE yAE yASet False by auto
            then show ?thesis
              by (metis \<open>fl2ttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>fl2ttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> append_Nil assms(8) ttWF_xs_x ttWF_ys_y flt2_xs_x flt2_ys_y priMaxTT priMaxTT_extend_both_events_non_maximal_ttWF)
              
          qed
        qed
        then show ?thesis
          using \<open>fl2ttobs \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> \<open>fl2ttobs \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = [[yEvent]\<^sub>E]\<close> flt2_xs_x flt2_ys_y by auto
      qed
    qed

lemma
  assumes "pri p fl Y" "FL1 fl\<^sub>0" "FLTick0 Tick fl\<^sub>0"
          "Y \<in> fl\<^sub>0"
          "fl2ttm fl\<^sub>0 \<subseteq> P"
          "fl2ttobs Y \<in> P"
          "ar = fl2ttobs fl" "flt2goodTock fl" "TTwf P"
    shows "\<exists>zr. priMaxTT p (fl2ttobs fl) zr [] P \<and> zr \<in> P"
  using pri_to_priMaxTT 
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(8) assms(9) by blast

lemma priMaxTT_fl2ttobs_both_eq_length_flt2goodTock_both:
  assumes "priMaxTT p (fl2ttobs xs) (fl2ttobs ys) zs P" "flt2goodTock xs" "length xs = length ys"
  shows "flt2goodTock ys"
  using assms apply (induct p xs ys arbitrary: zs rule:pri.induct, auto)
  apply (smt priMaxTT.simps(3) priMaxTT.simps(30))
    apply (smt priMaxTT.simps(18) priMaxTT.simps(5))
  apply (case_tac A, auto, case_tac b, auto, case_tac a, auto)
       apply meson
      apply (case_tac a, auto)
     apply (case_tac a, auto)
    apply (case_tac a, auto)
   apply (case_tac b, auto)
  apply (case_tac A, auto, case_tac b, auto)
       apply (case_tac a, auto)
      apply (case_tac a, auto)
     apply (case_tac a, auto)
    apply (case_tac a, auto)
   apply (case_tac a, auto)
  by (case_tac b, auto)

lemma ttWF2_ttWF_imp:
  assumes "ttWF x" "ttWF y"
  shows "ttWF2 x y"
  using assms ttWF2_ttWF by blast

lemma not_priMaxTT_cases [simp]:
  "\<not> priMaxTT pa (x # xs # ys) [ysa] s P"
  apply (cases x, auto)
  by (cases ysa, auto)

lemma not_priMaxTT_cases_2 [simp]:
  assumes "ys \<noteq> []"
  shows "\<not> priMaxTT pa (x # xs @ ys) [ysa] s P"
  using assms apply (cases x, auto)
   apply (cases xs, auto, cases ys, auto)
  by (cases xs, auto, cases ys, auto)

lemma TT1w_prefix_is_in:
  assumes "TT1w P" "s @ t \<in> P"
  shows "s \<in> P"
  using assms unfolding TT1w_def 
  using tt_prefix_concat by blast

lemma priMaxTT_Event_common_extend:
  assumes "priMaxTT p ([[Event x1]\<^sub>E] @ xs) ([[Event x1]\<^sub>E] @ ys) s P"
  shows "priMaxTT p xs ys (s@[[Event x1]\<^sub>E]) P"
  using assms by (induct p xs ys s P arbitrary:xs ys rule:priMaxTT.induct, auto)

lemma priMaxTT_of_both_fl2ttobs_cons_acceptance_imp_prirel_acceptance:
  assumes "priMaxTT p (fl2ttobs (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P" 
          "last xs = \<bullet>" "last ys = \<bullet>"
          "flt2goodTock xs" "flt2goodTock ys"
  shows "pri p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>" (* FIXME: better proof please.. *)
  using assms 
proof (induct p xs ys arbitrary:s x y rule:pri.induct)
  case (1 p A Z)
  then show ?case 
  proof (cases y)
    case acnil
    then show ?thesis using 1
      apply auto
      by (cases x, auto)
  next
    case (acset x2)
    then show ?thesis using 1 
      apply auto
      apply (cases x, safe)
         apply force
        apply (simp_all add:acceptance.simps(1))
      unfolding prirefMaxTT_def by auto
  qed
next
case (2 p A Z zz)
  then show ?case
    apply (cases x, auto, cases A, auto)
    by (cases Z, auto, case_tac a, auto, case_tac b, auto, case_tac b, auto)+
next
case (3 p A aa Z)
  then show ?case
    apply (cases y, auto, cases Z, auto)
    by (cases A, auto, case_tac a, auto, case_tac b, auto, case_tac b, auto)+
next
  case (4 p A aa Z zz)
  then obtain Aa a Zz z where A:"A = (Aa,a)\<^sub>\<F>\<^sub>\<L> \<and> (Aa = \<bullet> \<or> a \<in>\<^sub>\<F>\<^sub>\<L> Aa)"
                          and Z:"Z = (Zz,z)\<^sub>\<F>\<^sub>\<L> \<and> (Zz = \<bullet> \<or> z \<in>\<^sub>\<F>\<^sub>\<L> Zz)"
    apply auto
    apply (cases A, auto, cases Z, auto)
    by (cases Z, auto)

  have flt2goodTocks:
        "flt2goodTock \<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "flt2goodTock (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
        "flt2goodTock \<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "flt2goodTock (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using "4.prems" apply auto
    by (metis Finite_Linear_Model.last.simps(1) butlast_last_FL flt2goodTock_extend_consFL_acceptance last_bullet_butlast_last)+
    
  from 4 have "priMaxTT p (fl2ttobs ((A #\<^sub>\<F>\<^sub>\<L> aa) &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs ((Z #\<^sub>\<F>\<^sub>\<L> zz) &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
    by auto
  then have "priMaxTT p (fl2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>))) (fl2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))) s P"
    by auto
  then have "priMaxTT p (fl2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
  proof -
    have "fl2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) = fl2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)"
              "fl2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) = fl2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
      using flt2goodTocks by auto
    then show ?thesis
      using \<open>priMaxTT p (fl2ttobs (\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>))) (fl2ttobs (\<langle>Z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))) s P\<close> by auto 
  qed

  then have pp:"priMaxTT p (fl2ttobs (\<langle>(Aa,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
    using A Z by auto

  (* Aim is to deduce priMaxTT p (fl2ttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>?x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>?y\<rangle>\<^sub>\<F>\<^sub>\<L>)) ?s P *)
  then show ?case
  proof (cases a)
    case (Event x1)
    then have p1:"priMaxTT p ([[Event x1]\<^sub>E] @ fl2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using pp A by auto
    then have "fl2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[Event x1]\<^sub>E]"
      using Z flt2goodTocks by (cases z, auto)
    
    then have "priMaxTT p ([[Event x1]\<^sub>E] @ fl2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) ([[Event x1]\<^sub>E] @ fl2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using p1 by auto
    then have "priMaxTT p (fl2ttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) (s@[[Event x1]\<^sub>E]) P"
      by auto

    then have "pri p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using 4 
      by (metis Finite_Linear_Model.last.simps(2) flt2goodTock_cons_imp_prefix flt2goodTocks(2) flt2goodTocks(4))

    then show ?thesis by auto
  next
    case Tock
    then have "Aa \<noteq> \<bullet>"
      using "4.prems"(4) A by auto
    then have p1:"priMaxTT p ([[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Aa}]\<^sub>R,[Tock]\<^sub>E] @ fl2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using pp A Tock by (cases Aa, auto)
    then have "fl2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Zz}]\<^sub>R,[Tock]\<^sub>E]"
      using Z flt2goodTocks by (cases z, auto)
    
    then have "priMaxTT p ([[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Aa}]\<^sub>R,[Tock]\<^sub>E] @ fl2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) ([[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Zz}]\<^sub>R,[Tock]\<^sub>E] @ fl2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using p1 by auto
    then have "priMaxTT p (fl2ttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) (s@[[{x. x \<notin>\<^sub>\<F>\<^sub>\<L> Zz}]\<^sub>R,[Tock]\<^sub>E]) P"
      by auto

    then have "pri p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using 4 
      by (metis Finite_Linear_Model.last.simps(2) flt2goodTock_cons_imp_prefix flt2goodTocks(2) flt2goodTocks(4))

    then show ?thesis by auto
  next
    case Tick
    then have p1:"priMaxTT p ([[Tick]\<^sub>E] @ fl2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using pp A by auto
    then have "fl2ttobs (\<langle>(Zz,z)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[Tick]\<^sub>E]"
      using Z flt2goodTocks by (cases z, auto)
    
    then have "priMaxTT p ([[Tick]\<^sub>E] @ fl2ttobs(aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) ([[Tick]\<^sub>E] @ fl2ttobs(zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) s P"
      using p1 by auto
    then have "priMaxTT p (fl2ttobs (aa &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)) (fl2ttobs (zz &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)) (s@[[Tick]\<^sub>E]) P"
      by auto

    then have "pri p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using 4 
      by (metis Finite_Linear_Model.last.simps(2) flt2goodTock_cons_imp_prefix flt2goodTocks(2) flt2goodTocks(4))

    then show ?thesis by auto
  qed
qed    

(* So we want... *)
lemma
  assumes "priMaxTT p ar zr [] P" 
          "zr \<in> P" 
    shows "\<exists>Z fl\<^sub>0 fl. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ttm fl\<^sub>0 \<subseteq> P \<and> fl2ttobs Z \<in> P \<and> fl2ttobs fl = ar"
  (* But this is easier if done inductively over fl Z... *)
  oops

lemma prirel_extend_both_prefix_imp:
  assumes "pri p fl zr" "pri p fla zra"
  shows "pri p (fla &\<^sub>\<F>\<^sub>\<L> fl) (zra &\<^sub>\<F>\<^sub>\<L> zr)"
  using assms prirel_consFL_both_imp' by blast

lemma priMaxTT_is_ttWFx_trace_closed:
  assumes "priMaxTT p xs ys s P" "ttWFx_trace ys"
  shows "ttWFx_trace xs"
  using assms apply(induct p xs ys s P rule:priMaxTT.induct, auto)
  using ttWFx_trace_cons_imp_cons by (metis ttWFx_trace.simps(2) ttWFx_trace.simps(4) neq_Nil_conv)+

lemma
  assumes "\<exists>z. Tick <\<^sup>*p z"
  shows "\<not>pri p x \<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply (cases x, auto)
  by (simp_all add: some_higher_not_maximal)

lemma flt2goodAcceptance_pair_consFL:
  assumes "Event e \<in>\<^sub>\<F>\<^sub>\<L> aE" "flt2goodAcceptance (\<langle>(aE,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt) p"
  shows "(flt2goodAcceptance (\<langle>(aE,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) p \<and> flt2goodAcceptance tt p)"
  using assms apply (induct tt p rule:flt2goodAcceptance.induct)
   apply (case_tac A, simp)
   apply auto[1]
   apply (metis acceptance_event ttevent.distinct(3))
  apply (case_tac A, safe)
     apply (cases aE)
      apply auto[2]
     apply (metis acceptance_event assms(1) ttevent.distinct(3))
  apply (metis acceptance_event acceptance_set amember.simps(1) assms(1) ttevent.distinct(3) flt2goodAcceptance.simps(2) fltrace_concat2.simps(2) fltrace_concat2.simps(3) some_higher_not_maximal)
   apply (case_tac b, safe) 
  apply auto[3]
     apply (metis acceptance_event ttevent.distinct(3))
  apply (metis acceptance_event ttevent.distinct(3))
  apply (metis acceptance_event ttevent.distinct(3))
  apply (case_tac b, safe) 
    apply (cases aE, auto)
  apply (metis acceptance_event acceptance_set ttevent.distinct(3) flt2goodAcceptance.simps(2))
    apply (metis (no_types, hide_lams) acceptance_event amember.simps(2) ttevent.distinct(3) flt2goodAcceptance.elims(2) flt2goodAcceptance.simps(2) fltrace.distinct(1) fltrace.inject(2) some_higher_not_maximal)
    apply (metis (no_types, hide_lams) acceptance_event acceptance_set flt2goodAcceptance.simps(2))
    by (metis acceptance_event acceptance_set ttevent.distinct(5) flt2goodAcceptance.simps(2))

lemma flt2goodTock_of_consFL_also_flt2goodTock:
  assumes "flt2goodTock xs" "flt2goodTock ys"
  shows "flt2goodTock (xs &\<^sub>\<F>\<^sub>\<L> ys)"
  using assms apply(induct xs, auto)
  apply (case_tac x, auto)
  by (induct ys, auto)

lemma priMaxTT_to_pri:
  assumes "priMaxTT p xs ys s P" "ttWFx_trace ys" "ttWF ys" "(fl2ttobs zr) = ys" 
          "flt2goodTock zr"
          "flt2goodAcceptance zr p"
          "TTM3 P"
        (*  "maximal(p,Tick)"*) (* FIXME: probably not needed *)
  shows "\<exists>fl. pri p fl zr \<and> (fl2ttobs fl) = xs \<and> flt2goodTock fl"
  using assms 
proof (induct p xs ys s P arbitrary:zr rule:priMaxTT.induct, auto simp add:ttWFx_trace_cons_imp_cons)
  fix pa::"'a ttevent partialorder"
  fix zra::"'a ttevent fltrace"
  assume assm1:"fl2ttobs zra = []"
  assume assm2:"flt2goodTock zra"
  from assm1 assm2 have "zra = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (metis fl2ttobs.simps(1) fl2ttobs_consFL_eq_Nil_imp_not_flt2goodTock list.simps(3))
  then show "\<exists>fl. pri pa fl zra \<and> fl2ttobs fl = [] \<and> flt2goodTock fl"
    using assm1 assm2 pri.simps(1) priacc.simps(1)
    by metis
next
  fix pa::"'a ttevent partialorder"
  fix S
  fix zra::"'a ttevent fltrace"
  assume assm1:"fl2ttobs zra = [[S]\<^sub>R]"
  assume assm2:"flt2goodTock zra"
  from assm1 assm2 have "zra = \<langle>[{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    apply (cases zra, auto)
     apply (case_tac x1, auto)
    apply (case_tac x21, auto, case_tac b, auto, case_tac a, auto)
    by (case_tac b, auto)
  then show "\<exists>fl. pri pa fl zra \<and> fl2ttobs fl = [[prirefMaxTT pa S]\<^sub>R] \<and> flt2goodTock fl"
    apply (intro exI[where x="\<langle>[{x. x \<notin> (prirefMaxTT pa S)}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
    unfolding prirefMaxTT_def by auto 
next
  fix pa::"'a ttevent partialorder"
  fix aa S zz sa Q
  fix zra::"'a ttevent fltrace"
  assume hyp:"(\<And>zr. fl2ttobs zr = zz \<Longrightarrow> flt2goodTock zr \<Longrightarrow> flt2goodAcceptance zr pa \<Longrightarrow> \<exists>fl. pri pa fl zr \<and> fl2ttobs fl = aa \<and> flt2goodTock fl)"
  assume assm1:"priMaxTT pa aa zz (sa @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
  assume assm2:"ttWF zz"
  assume assm3:"flt2goodTock zra"
  assume assm4:"Tock \<notin> S"
  assume assm5:"Tock \<notin> prirefMaxTT pa S"
  assume assm6:"ttWFx_trace zz"
  assume assm7:"fl2ttobs zra = [S]\<^sub>R # [Tock]\<^sub>E # zz"
  then have tocks:"Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> prirefMaxTT pa S}]\<^sub>\<F>\<^sub>\<L>"
                  "Tock \<in>\<^sub>\<F>\<^sub>\<L> [{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>"
    using assm4 assm5
    apply (metis amember.simps(2) mem_Collect_eq)
    by (simp_all add: assm4)
  assume assm8:"flt2goodAcceptance zra pa"
  have "fl2ttobs(\<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [S]\<^sub>R # [Tock]\<^sub>E # Nil"
    using tocks by auto
  then obtain tt where tt:"fl2ttobs tt = zz \<and> flt2goodTock tt \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt"
    using assm7 tocks assm3 assm4 assm8 apply (induct zra, auto)
     apply (metis list.inject neq_Nil_conv)
    apply (case_tac x1a, auto, case_tac b, auto, case_tac a, auto)
     apply metis
    by (case_tac b, auto)
  then obtain flaa where flaa:"pri pa flaa tt \<and> fl2ttobs flaa = aa \<and> flt2goodTock flaa"
    using hyp assm8 by blast
    
  show "\<exists>fl. pri pa fl zra \<and> fl2ttobs fl = [prirefMaxTT pa S]\<^sub>R # [Tock]\<^sub>E # aa \<and> flt2goodTock fl"
  proof -
    have "priMaxTT pa ([prirefMaxTT pa S]\<^sub>R # [Tock]\<^sub>E # aa) 
                        ([S]\<^sub>R # [Tock]\<^sub>E # zz) sa Q"
      by (simp add: assm1 assm5)

    obtain fla where fla:"fla = \<langle>([{x. x \<notin> prirefMaxTT pa S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" by auto

    have "flt2goodTock fla"
      using fla tocks(1) by auto
    then have "flt2goodTock (fla &\<^sub>\<F>\<^sub>\<L> flaa)"
      using flt2goodTock_of_consFL_also_flt2goodTock flaa by blast
    have "pri pa fla \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
      using tocks fla unfolding prirefMaxTT_def by auto
    have fl2ttobs_fla_flaa:"fl2ttobs(fla &\<^sub>\<F>\<^sub>\<L> flaa) = [prirefMaxTT pa S]\<^sub>R # [Tock]\<^sub>E # aa"
      using tocks fla flaa by auto
    have "pri pa (fla &\<^sub>\<F>\<^sub>\<L> flaa) zra"
      using tocks fla flaa apply auto
      by (metis FL_concat_equiv \<open>pri pa fla \<langle>([{x. x \<notin> S}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>\<close> local.tt prirel_extend_both_prefix_imp)
    then show ?thesis using fl2ttobs_fla_flaa
      using \<open>flt2goodTock (fla &\<^sub>\<F>\<^sub>\<L> flaa)\<close> by blast
  qed
next
  fix pa::"'a ttevent partialorder"
  fix aa e\<^sub>2 zz sa Q zra
  assume hyp:"(\<And>zr. ttWF zz \<Longrightarrow>
              fl2ttobs zr = zz \<Longrightarrow> flt2goodTock zr \<Longrightarrow> flt2goodAcceptance zr pa \<Longrightarrow> \<exists>fl. pri pa fl zr \<and> fl2ttobs fl = aa \<and> flt2goodTock fl)"
  assume assm1:"ttWFx_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm2:"ttWF ([e\<^sub>2]\<^sub>E # zz)"
  then have no_Tock:"e\<^sub>2 \<noteq> Tock"
    using ttWF.simps(6) by blast
  have zz_is_ttWF:"ttWF zz"
    using assm2
    by (metis ttWF.simps(1) ttWF.simps(4) ttWF.simps(8) ttevent.exhaust neq_Nil_conv no_Tock)
  assume assm3:"fl2ttobs zra = [e\<^sub>2]\<^sub>E # zz"
  assume assm4:"flt2goodTock zra"
  assume assm5:"priMaxTT pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm6:"maximal(pa,e\<^sub>2)"
  assume assm7:"flt2goodAcceptance zra pa"
  from assm3 obtain tt aE where tt:"fl2ttobs tt = zz \<and> flt2goodTock tt \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE \<or> aE = \<bullet>)"
    using assm3 assm4 assm7 no_Tock apply (induct zra, auto)
     apply (case_tac x, auto)
    apply (case_tac x1a, auto)
    apply (case_tac a, auto, case_tac b)
    apply (metis acceptance_event acceptance_set amember.simps(2) ttevent.distinct(1) ttevent.distinct(3) ttobs.inject(1) list.inject some_higher_not_maximal)
    
      apply auto[1]

  apply (metis acceptance_event acceptance_set amember.simps(2) ttevent.distinct(5) ttobs.inject(1) list.inject)
  apply (case_tac b)  
    apply (metis acceptance_event ttobs.inject(1) list.inject)
  by auto
  then obtain fl where fl:"pri pa fl tt \<and> fl2ttobs fl = aa \<and> flt2goodTock fl"
    using assm2 assm4 hyp zz_is_ttWF
    by blast
  show "\<exists>fl. pri pa fl zra \<and> fl2ttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2goodTock fl"
  proof -
    from assm5 assm6 have "priMaxTT pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      by simp

    then show ?thesis
    proof (cases "aE = \<bullet>")
      case True
      obtain fle2 where "fle2 = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl" by auto
      then have "pri pa fle2 zra"
        using assm6 fl local.tt by auto
      then show ?thesis
        using \<open>fle2 = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<close> fl no_Tock by auto
    next
      case False
      then obtain fle2 where fle2:"fle2 = \<langle>([{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl \<and> e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> [{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>"
        using assm6 local.tt some_higher_not_maximal by fastforce
      then have "pri pa fle2 zra"
        using False fl tt by (cases aE, auto)
      then show ?thesis
        using fl fle2 no_Tock by auto
    qed
  qed
next
  fix pa::"'a ttevent partialorder"
  fix aa e\<^sub>2 zz sa Q zra Z
  assume hyp:"(\<And>zr. ttWF zz \<Longrightarrow> fl2ttobs zr = zz \<Longrightarrow> flt2goodTock zr \<Longrightarrow> flt2goodAcceptance zr pa \<Longrightarrow> \<exists>fl. pri pa fl zr \<and> fl2ttobs fl = aa \<and> flt2goodTock fl)"
  assume assm1:"ttWFx_trace ([e\<^sub>2]\<^sub>E # zz)"
  assume assm2:"ttWF ([e\<^sub>2]\<^sub>E # zz)"
  then have no_Tock:"e\<^sub>2 \<noteq> Tock"
    using ttWF.simps(6) by blast
  have zz_is_ttWF:"ttWF zz"
    using assm2
    by (metis ttWF.simps(1) ttWF.simps(4) ttWF.simps(8) ttevent.exhaust neq_Nil_conv no_Tock)
  assume assm3:"fl2ttobs zra = [e\<^sub>2]\<^sub>E # zz"
  assume assm4:"flt2goodTock zra"
  assume assm5:"priMaxTT pa aa zz (sa @ [[e\<^sub>2]\<^sub>E]) Q"
  assume assm6:"sa @ [[Z]\<^sub>R] \<in> Q"
  assume assm7:"\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b"
  assume assm8:"e\<^sub>2 \<notin> Z"
  assume assm9:"flt2goodAcceptance zra pa"
  assume assm10:"TTM3 Q"
  (*assume assm10:"maximal(pa,Tick)"*) (* FIXME: Not needed, I think *)
  from assm3 obtain tt aE where tt:"fl2ttobs tt = zz \<and> flt2goodTock tt 
    \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt 
    \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE \<or> aE = \<bullet>)"
    using assm3 assm4 assm9 no_Tock apply (induct zra, auto)
    apply (case_tac x, auto)
    apply (case_tac x1a, auto)
    apply (metis acceptance_event acceptance_set ttWF.simps(6) ttobs.inject(1) list.inject zz_is_ttWF)
    by (metis acceptance_event ttobs.inject(1) list.inject)
  then obtain fl where fl:"pri pa fl tt \<and> fl2ttobs fl = aa \<and> flt2goodTock fl"
    using assm2 assm4 hyp zz_is_ttWF
    by blast
  show "\<exists>fl. pri pa fl zra \<and> fl2ttobs fl = [e\<^sub>2]\<^sub>E # aa \<and> flt2goodTock fl"
  proof -
    from assm5 assm6 assm7 have priMaxTT:"priMaxTT pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) sa Q"
      using priMaxTT.simps(4) assm8 by blast

    then show ?thesis
    proof (cases "aE = \<bullet>")
      case aE_is_bullet:True
      then show ?thesis
      proof (cases "e\<^sub>2")
        case (Event x1)
          then show ?thesis
            proof (cases "maximal(pa,e\<^sub>2)")
              case True
              then obtain fla where fla:"fla = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl"
                by auto
              then have flt2goodTock_fla:"flt2goodTock fla"
                using fla fl aE_is_bullet assm4 flt2goodTock_cons_imp_prefix flt2goodTock_of_consFL_also_flt2goodTock tt by blast
              
              have "pri pa fla zra"
                using fla True fl tt by auto
              then have "pri pa fla zra \<and> flt2goodTock fla"
                using flt2goodTock_fla by auto
              then show ?thesis
                using fl fla no_Tock by auto
            next
              case False
              then have "\<not> flt2goodAcceptance zra pa"
                using tt aE_is_bullet Event by auto
              then show ?thesis
                using assm9 by blast
            qed
      next
        case Tock
        then show ?thesis
          using no_Tock by blast
      next
        case Tick
        then obtain fla where fla:"fla = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl"
          by auto
        then have flt2goodTock_fla:"flt2goodTock fla"
          using fla fl aE_is_bullet assm4 flt2goodTock_cons_imp_prefix flt2goodTock_of_consFL_also_flt2goodTock tt by blast

        then show ?thesis
        proof (cases "maximal(pa,Tick)")
          case True
          then have "pri pa fla zra"
            using fla Tick fl tt by auto
          then have "pri pa fla zra \<and> flt2goodTock fla"
            using flt2goodTock_fla by auto
          then show ?thesis using fl fla no_Tock by auto
        next
          case False
          then have Tick_not_in:"Tick \<notin> Z"
            using assm8 Tick by auto
          have "Tick \<in> Z"
            using assm6 assm10 unfolding TTM3_def 
            apply (induct sa, auto)
            using TTickTrace.simps(3) TTickTrace_dist_concat by blast
          then show ?thesis using Tick_not_in by auto
        qed
      qed
 (*     obtain fle2 where "fle2 = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl" by auto
      then have "prirel pa fle2 zra"
        using assm6 assm7 fl local.tt 
      then show ?thesis
        using \<open>fle2 = \<langle>(\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl\<close> fl no_Tock by auto*)
    next
      case aE_not_bullet:False then 
      show ?thesis 
        proof (cases "maximal(pa,e\<^sub>2)")
          case True
          then show ?thesis
          proof -
            obtain ff :: "'a ttevent fltrace" and aaa :: "'a ttevent acceptance" where
              f1: "fl2ttobs ff = zz \<and> flt2goodTock ff \<and> flt2goodAcceptance ff pa \<and> zra = \<langle>(aaa,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> ff \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aaa \<or> aaa = \<bullet>)"
              using \<open>\<And>thesis. (\<And>tt aE. fl2ttobs tt = zz \<and> flt2goodTock tt \<and> flt2goodAcceptance tt pa \<and> zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt \<and> (e\<^sub>2 \<in>\<^sub>\<F>\<^sub>\<L> aE \<or> aE = \<bullet>) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
            then obtain ffa :: "'a ttevent fltrace \<Rightarrow> 'a ttevent fltrace" where
              f2: "pri pa (ffa ff) ff \<and> fl2ttobs (ffa ff) = aa \<and> flt2goodTock (ffa ff)"
              by (metis (full_types) hyp zz_is_ttWF)
            then have "fl2ttobs ((\<bullet>,e\<^sub>2)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> ffa ff) = [e\<^sub>2]\<^sub>E # aa"
              by (simp add: no_Tock)
            then show ?thesis
              using f2 f1 
              using FL_concat_equiv True acceptance_event acceptance_set flt2goodTock.simps(2) no_Tock pri.simps(4)
              by (metis less_eq_acceptance.simps(1)) (* TODO: Not particularly efficient *)
          qed
        next
          case False
          then show ?thesis
          proof (cases "e\<^sub>2")
                case (Event x1)
                have "zra = \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt"
                  using tt by auto
                have "flt2goodAcceptance (\<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> tt) pa"
                  using tt assm9 by blast
                then have "flt2goodAcceptance \<langle>(aE,e\<^sub>2)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> pa"
                  using tt False assm9 flt2goodAcceptance_pair_consFL
                  by (metis Event aE_not_bullet)
                then have "\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> Event x1 <\<^sup>*pa b)"
                  using tt Event aE_not_bullet apply auto
                  by (metis Event False acceptance_event ttevent.distinct(3))
                then have "Event x1 \<in>\<^sub>\<F>\<^sub>\<L> [{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>"
                  using assm7 assm8
                  using Event aE_not_bullet local.tt by auto
                then obtain fle2 where fle2:
                  "fle2 = \<langle>([{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>,Event x1)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> fl 
                   \<and> Event x1 \<in>\<^sub>\<F>\<^sub>\<L> [{a. a \<in>\<^sub>\<F>\<^sub>\<L> aE \<and> \<not>(\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>aE \<and> a <\<^sup>*pa b)}]\<^sub>\<F>\<^sub>\<L>"
                  by auto
                then have "pri pa fle2 zra"
                  using tt fl apply auto
                  apply (cases aE, auto)
                  using Collect_cong aE_not_bullet acceptance_set acceptances_same_set mem_Collect_eq priacc.simps(2) Event apply blast
                  apply (cases aE, auto)
                  using Collect_cong Event FL_concat_equiv aE_not_bullet acceptance.distinct(1) acceptance_event acceptance_set fl local.tt pri.simps(4) by blast
                then show ?thesis
                  using Event fl fle2 by auto
              next
                case Tock
                then show ?thesis 
                  using no_Tock by blast
              next
                case Tick
                then have Tick_not_in:"Tick \<notin> Z"
                    using assm8 Tick by auto
                have "Tick \<in> Z"
                    using assm6 assm10 unfolding TTM3_def 
                    apply (induct sa, auto)
                    using TTickTrace.simps(3) TTickTrace_dist_concat by blast
               then show ?thesis using Tick_not_in by auto
           qed
        qed 
      qed
    qed
  qed

lemma priMaxTT_to_pri':
  assumes "priMaxTT p xs ys [] P" "ys \<in> P" 
          "TT0 P" "TTwf P" "TT1w P" "ttWFx P" "TTick P" "TTM3 P" "TT3w P"
    shows "\<exists>fl. fl2ttobs fl = xs \<and> (\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ttm fl\<^sub>0 \<subseteq> P \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0)) \<and> flt2goodTock fl"
proof -
  have "ttWF ys"
    using TTwf_def assms by blast
  then obtain Z where fl:"ys = fl2ttobs Z \<and> flt2goodTock Z  \<and>
        (\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ttm fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0) \<and> fl2ttobs Z \<in> P \<and> flt2goodAcceptance Z p \<and> flt2goodTock Z 
        \<and> ttWF ys \<and> priMaxTT p xs ys [] P"
    unfolding fl2ttm_def using assms TTwf_1c_3_imp_fl2ttobs_FL1_mod by blast
  then have "\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ttm fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs Z \<in> P \<and> fl2ttobs Z = ys \<and> flt2goodAcceptance Z p 
        \<and> flt2goodTock Z 
        \<and> ttWFx_trace ys \<and> ttWF ys \<and> priMaxTT p xs ys [] P"
    by auto
  then have "\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ttm fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs Z \<in> P \<and> fl2ttobs Z = ys \<and> flt2goodAcceptance Z p 
        \<and> flt2goodTock Z 
        \<and> ttWFx_trace ys \<and> ttWF ys \<and> priMaxTT p xs ys [] P
        \<and> (\<exists>fl. pri p fl Z \<and> fl2ttobs fl = xs \<and> flt2goodTock fl)"
    using priMaxTT_to_pri assms
    by metis
  then have "\<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> fl2ttm fl\<^sub>0 \<subseteq> P \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs Z \<in> P \<and> flt2goodTock Z 
        \<and> (\<exists>fl. pri p fl Z \<and> fl2ttobs fl = xs \<and> flt2goodTock fl)"
    by blast
  then show ?thesis using fl by blast
qed

(* The key result we wish to establish is: *)
lemma fl2ttm_pri_ttm2fl_PriMax:
  fixes P :: "('e ttobs) list set"
  assumes TT0_healthy:  "TT0 P" 
      and TTwf_healthy: "TTwf P" 
      and TT1w_healthy: "TT1w P"
      and ttWFx_healthy:  "ttWFx P"
      and TTick_healthy:"TTick P"
      and TTM3:         "TTM3 P"
      and TT3w_healthy: "TT3w P"
     (* and Tick_max:"maximal(p,Tick)"*)
  shows "fl2ttm(Pri p (ttm2fl P)) = PriMax p P"
proof -
  have "fl2ttm(Pri p (ttm2fl P)) = {fl2ttobs fl|fl. fl \<in> (Pri p (ttm2fl P)) \<and> flt2goodTock fl} \<union> {[]}"
    using fl2ttm_FL0_FL1_flt2goodTock
    by (simp add: fl2ttm_FL0_FL1_flt2goodTock TT0_healthy TT1w_healthy TickTock_Max_FL.FL0_ttm2fl FL1_ttm2fl pri_FL0 pri_FL1)
  also have "... = {fl2ttobs fl|fl. fl \<in> (Pri p (\<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P})) \<and> flt2goodTock fl} \<union> {[]}"
    unfolding ttm2fl_def by auto
  also have "... = {fl2ttobs fl|fl. fl \<in> \<Union>{Pri p fl|fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P} \<and> flt2goodTock fl} \<union> {[]}"
  proof -
    have "Pri p (\<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}) = \<Union>{Pri p fl|fl. fl \<in> {fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}}"
      using Pri_univ_dist by (metis)
    also have "... = \<Union>{Pri p fl|fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
      by auto
    then show ?thesis
      using calculation by auto
  qed
  also have "... = {fl2ttobs fl|fl. \<exists>x. (\<exists>fl. x = Pri p fl \<and> FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P) \<and> fl \<in> x \<and> flt2goodTock fl} \<union> {[]}"
    unfolding fl2ttm_def by auto
  also have "... = {fl2ttobs fl|fl. \<exists>fl\<^sub>0. FLTick0 Tick fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> (fl2ttm fl\<^sub>0) \<subseteq> P \<and> (\<exists>Z. pri p fl Z \<and> Z \<in> fl\<^sub>0) \<and> flt2goodTock fl} \<union> {[]}"
    unfolding Pri_def by auto
  also have "... = {ar|ar zr. priMaxTT p ar zr [] P \<and> zr \<in> P}"
    using assms apply auto
    using TT0_TT1w_empty priMaxTT.simps(1) apply blast
    apply (meson fl2ttobs_extn pri_to_priMaxTT)
    using assms priMaxTT_to_pri' by metis 
  also have "... = PriMax p P"
    unfolding PriMax_def by auto
  finally show ?thesis .
qed

lemma prirel_extend_both_consFL:
  assumes "pri p xs ys" "last xs = \<bullet>" "last ys = \<bullet>" "pri p \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct p xs ys rule:pri.induct, auto)

lemma prirel_both_and_both_acceptances_imp_cons_both:
  assumes "pri p xs ys" "pri p \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "pri p (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply (induct p xs ys rule:pri.induct, auto)
  by (case_tac Z, auto)+

lemma fl2ttobs_exists_flt2goodTock_for_ttWF_ttWFx_trace:
  assumes "ttWF fl" "ttWFx_trace fl"
  shows "\<exists>zr. (fl2ttobs zr) = fl \<and> flt2goodTock zr"
  using assms
proof (induct fl rule:ttWF.induct, auto)
  show "\<exists>zr. fl2ttobs zr = [] \<and> flt2goodTock zr"
    by (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix X
  show "\<exists>zr. fl2ttobs zr = [[X]\<^sub>R] \<and> flt2goodTock zr"
    by (intro exI[where x="\<langle>[{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  show "\<exists>zr. fl2ttobs zr = [[Tick]\<^sub>E] \<and> flt2goodTock zr"
    by (intro exI[where x="\<langle>(\<bullet>,Tick)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
next
  fix e \<sigma>
  assume hyp:"(ttWFx_trace \<sigma> \<Longrightarrow> \<exists>zr. fl2ttobs zr = \<sigma> \<and> flt2goodTock zr)"
  assume assm1:"ttWF \<sigma>"
  assume assm2:"ttWFx_trace ([Event e]\<^sub>E # \<sigma>)"
  show "\<exists>zr. fl2ttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodTock zr"
  proof -
    from assm2 have "ttWFx_trace \<sigma>"
      using ttWFx_trace_cons_imp_cons by blast
    then have "\<exists>zr. fl2ttobs zr = \<sigma> \<and> flt2goodTock zr"
      using hyp by auto
    then have "\<exists>zr. fl2ttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs zr = [Event e]\<^sub>E # \<sigma> \<and> flt2goodTock zr"
      by auto
    then have "\<exists>zr. fl2ttobs(\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr) = [Event e]\<^sub>E # \<sigma> \<and> flt2goodTock (\<langle>(\<bullet>,Event e)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zr)"
      by auto
    then show ?thesis by blast
  qed
next
  fix X::"'a ttevent set"
  fix zr::"'a ttevent fltrace"
  assume assm1:"ttWF (fl2ttobs zr)"
  assume assm2:"Tock \<notin> X"
  assume assm4:"flt2goodTock zr"
  show "\<exists>zra. fl2ttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # fl2ttobs zr \<and> flt2goodTock zra"
  proof -
    have "\<exists>zra. fl2ttobs zra = fl2ttobs zr \<and> flt2goodTock zra"
      using assm4 by auto
    then have "\<exists>zra. fl2ttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @ fl2ttobs zra = [X]\<^sub>R # [Tock]\<^sub>E # fl2ttobs zr \<and> flt2goodTock zra"
      using assm2 by auto
    then have "\<exists>zra. fl2ttobs(\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra) = [X]\<^sub>R # [Tock]\<^sub>E # fl2ttobs zr \<and> flt2goodTock (\<langle>([{x. x \<notin> X}]\<^sub>\<F>\<^sub>\<L>,Tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> zra)"
      using assm2 by auto
    then show ?thesis by blast
  qed
qed

lemma priMaxTT_of_fl2ttobs_flt2goodTocks_is_eq_length:
  assumes "priMaxTT p (fl2ttobs fl) (fl2ttobs zr) s P" "flt2goodTock fl" "flt2goodTock zr" (*"xs = (fl2ttobs fl)" "ys = (fl2ttobs zr)"*) 
  shows "length fl = length zr"
  using assms (* TODO: I'm sure there is a nicer proof... *)
  apply (induct p fl zr arbitrary:s rule:pri.induct, auto)
  apply (case_tac A, auto, case_tac Z, auto, case_tac b, auto, case_tac a, auto)
     apply (case_tac b, auto, case_tac Z, auto, case_tac b, auto, case_tac a, auto)
    apply (case_tac b, auto, case_tac Z, auto, case_tac A, auto, case_tac b, auto, case_tac a, auto)
  apply (case_tac b, auto, case_tac A, auto, case_tac b, auto, case_tac a, auto)
   apply (case_tac b, auto)
  apply (case_tac A, auto, case_tac Z, auto, case_tac b, auto, case_tac a, auto, case_tac ba, auto)
  apply (case_tac aa, auto, case_tac aa, auto)
  apply (case_tac aa, auto, case_tac aa, auto)
       apply (case_tac ba, auto, case_tac a, auto, case_tac a, auto, case_tac a, auto)
       apply (case_tac ba, auto,case_tac a, auto)
  apply (case_tac aa, auto, case_tac aa, auto)
      apply (case_tac a, auto)
    apply (case_tac a, auto)
apply (case_tac aa, auto)
  apply (case_tac a, auto, case_tac ba, auto)
    apply (case_tac b, auto)
   apply (case_tac b, auto)
  apply (case_tac b, auto)
   apply (case_tac Z, auto, case_tac a, auto, case_tac b, auto, case_tac b, auto)
  by (case_tac Z, auto, case_tac a, auto, case_tac b, auto, case_tac b, auto)

lemma FL_Pri_ttm2fl:
  assumes "TT0 P" "TTwf P" "TT1w P" "TT2 P" "ttWFx P" "TT3 P" "TTM1 P" "TTM2 P"
  shows "FL0 (Pri p (ttm2fl P))"
        "FL1 (Pri p (ttm2fl P))"
        "FL2 (Pri p (ttm2fl P))"
        "FL3 (Pri p (ttm2fl P))"
  using assms 
  using FL0_ttm2fl FL1_ttm2fl pri_FL0 apply blast
  apply (simp add: FL1_ttm2fl pri_FL1)
  apply (simp add: FL2_Pri FL2_ttm2fl assms(3) assms(7) assms(8))
  by (simp add: FLTick0_Pri FLTick0_Tick_ttm2fl assms(2))

lemma TTMax_PriMax_closure:
  assumes "TT0 P" "TTwf P" "TT1w P" "TT2 P" "ttWFx P" "TT3 P" "TTM1 P" "TTM2 P" "TTM3 P"
  shows "TTwf(PriMax p P)"
        "TT0(PriMax p P)"
        "TT1w(PriMax p P)"
        "TT2(PriMax p P)"
        "ttWFx(PriMax p P)"
        "TT3(PriMax p P)"
        "TTM1(PriMax p P)"
        "TTM2(PriMax p P)"
        "TTM3(PriMax p P)"
proof -
  have FL_Pri:
       "FL0 (Pri p (ttm2fl P))"
       "FL1 (Pri p (ttm2fl P))"
       "FL2 (Pri p (ttm2fl P))"
       "FL3 (Pri p (ttm2fl P))"
    using assms FL_Pri_ttm2fl by blast+

  have PriMax_eq:"PriMax p P = fl2ttm(Pri p (ttm2fl P))"
    using assms fl2ttm_pri_ttm2fl_PriMax
    by (metis TT3w_def TTM3_TTick TTM3_TTick_part Un_insert_right in_mono insert_absorb set_eq_subset subsetD subset_refl sup_bot_right)

  show "TTwf (PriMax p P)"
    using PriMax_eq
    using FL_Pri(4) TTwf_fl2ttm by auto

  show "TT0 (PriMax p P)"
    using PriMax_eq
    by (simp add: FL_Pri(1) FL_Pri(2) FL_Pri(3) FL_Pri(4) TT0_fl2ttm)

  show "TT1w (PriMax p P)"
    using PriMax_eq 
    by (simp add: FL_Pri(2) TT1w_fl2ttm)

  show "TT2 (PriMax p P)"
    using PriMax_eq 
    using FL_Pri(1) FL_Pri(2) FL_Pri(3) FL_Pri(4) TT2_fl2ttm by auto

  show "ttWFx(PriMax p P)"
    using PriMax_eq
    using ttWFx_fl2ttm by auto

  show "TT3(PriMax p P)"
    using PriMax_eq
    by (simp add: FL_Pri(4) TT3_fl2ttm)

  show "TTM1(PriMax p P)"
    using PriMax_eq
    by (simp add: FL_Pri(1) FL_Pri(2) FL_Pri(3) TTM1_fl2ttm_for_FL2_FL1_FL0)

  show "TTM2(PriMax p P)"
    using PriMax_eq
    using FL_Pri(1) FL_Pri(2) FL_Pri(3) TTM2_fl2ttm_for_FL2_FL1_FL0 by auto

  show "TTM3(PriMax p P)"
    using PriMax_eq
    by (simp add: FL_Pri(1) FL_Pri(2) FL_Pri(4) TTM3_fl2ttm)
qed

end