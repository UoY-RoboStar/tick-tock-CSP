theory
  CTockTick_FL_Priority
imports
  CTockTick_FL
  Finite_Linear_Priority
begin

lemma pri_univ_dist:
  "pri p (\<Union> X) = \<Union>{pri p x|x. x \<in> X}"
  unfolding pri_def by auto

lemma flt2cttobs_extn:
  (*assumes CTwf_healthy: "CTwf P" 
        and CT1c_healthy: "CT1c P"
        and CT3_healthy:  "CT3 P"*)
    shows
  "(fl2ctt fl\<^sub>0 \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))
   =
   ({flt2cttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P))"
proof -

    have "((fl2ctt fl\<^sub>0) \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))
          =
          ((\<forall>x. x \<in> (fl2ctt fl\<^sub>0) \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>x. x \<in> {flt2cttobs fl|fl. fl \<in> fl\<^sub>0} \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      unfolding fl2ctt_def by auto
    also have "... =
          ((\<forall>x. (\<exists>fl. x = flt2cttobs(fl) \<and> fl \<in> fl\<^sub>0) \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>x fl. (x = flt2cttobs(fl) \<and> fl \<in> fl\<^sub>0) \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>fl. fl \<in> fl\<^sub>0 \<longrightarrow> flt2cttobs(fl) \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>fl. (fl \<in> fl\<^sub>0 \<longrightarrow> flt2cttobs(fl) \<in> P)) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          (\<forall>fl\<^sub>x. (fl\<^sub>x \<in> fl\<^sub>0 \<longrightarrow> flt2cttobs(fl\<^sub>x) \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
  then have "...
        =
        (\<forall>fl\<^sub>x. (fl\<^sub>x \<in> fl\<^sub>0 \<longrightarrow> flt2cttobs(fl\<^sub>x) \<in> P) \<and> 
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P))"
    by auto
  then have "... =
        ((\<forall>x fl. (x = flt2cttobs(fl) \<and> fl \<in> fl\<^sub>0) \<longrightarrow> x \<in> P) \<and>
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P))"
    by auto
  then have "... =
        (({flt2cttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P) \<and>
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P))"
    by auto
  ultimately show ?thesis
    by (smt \<open>((\<forall>x. x \<in> fl2ctt fl\<^sub>0 \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0)) = ((\<forall>x. x \<in> {flt2cttobs fl |fl. fl \<in> fl\<^sub>0} \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))\<close> mem_Collect_eq subset_eq)
qed


lemma
  "fl2ctt(pri p P) = priCT p fl2ctt(P)"
proof -
  have "fl2ctt(pri p P) = {flt2cttobs fl|fl. fl \<in> (pri p P)}"
    unfolding fl2ctt_def by simp
  also have "... = {flt2cttobs fl|fl. fl \<in> {A|A Z. prirel p A Z \<and> Z \<in> P}}"
    unfolding pri_def by simp
  also have "... = {flt2cttobs fl|fl A Z. prirel p fl Z \<and> Z \<in> P}"
    by auto
  oops

lemma
  assumes CTwf_healthy: "CTwf P" 
      and CT1c_healthy: "CT1c P"
      and CT3_healthy:  "CT3 P"
    shows
  "\<exists>fl. flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x) \<and> flt2cttobs(fl) \<in> P"
proof -
  have "(\<exists>fl. flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x) \<and> flt2cttobs(fl) \<in> P)
        =
        (\<exists>fl x. x = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x) \<and> x \<in> P)"
    by blast
  then have "(\<exists>fl x. x = flt2cttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {flt2cttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x))"
    using assms CTwf_1c_3_imp_flt2cttobs_FL1
    apply auto
    oops
  (*  "(\<exists>fl\<^sub>0. {flt2cttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P \<and> 
              (\<exists>Z.  Z \<in> fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> flt2goodTock Z \<and>  \<in> P))"*)



lemma flt2cttobs_base_prirelacc:
  assumes "prirelacc p A Z"
  shows "flt2cttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if A = \<bullet> then [] else [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R])"
  using assms
proof (cases Z)
  case acnil
  then show ?thesis using assms 
    apply auto
    by (cases A, auto)+
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
      then have a:"flt2cttobs(\<langle>[AS]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> [AS]\<^sub>\<F>\<^sub>\<L>}]\<^sub>R]"
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

lemma flt2cttobs_base_Z_prirelacc:
  assumes "prirelacc p A Z"
  shows "flt2cttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) 
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
      then have a:"flt2cttobs(\<langle>[ZS]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> [ZS]\<^sub>\<F>\<^sub>\<L>}]\<^sub>R]"
        by auto
      then show ?thesis using assms by auto
    qed
  qed

lemma flt2cttobs_base_Z_prirelacc_iff:
   "prirelacc p A Z \<longleftrightarrow>
         ((flt2cttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if Z = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R]))
          \<and> 
         (flt2cttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if A = \<bullet> then [] else (if Z \<noteq> \<bullet> then [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R] else []))))"
  by (induct A Z rule:prirelacc.induct, auto)

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

definition prirelref :: "('e cttevent) partialorder \<Rightarrow> ('e cttevent) set \<Rightarrow> ('e cttevent) set" where
"prirelref p Z = {z. z \<notin> Z \<longrightarrow> (\<exists>b. b \<notin> Z \<and> z <\<^sup>*p b)}"

lemma prirelacc_eq_prirelref_via_flt2cttobs:
  assumes "flt2cttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R]" "flt2cttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R]"
  shows "prirelacc p A Z \<longleftrightarrow> (prirelref p S = R)"
proof -
  have "prirelacc p A Z 
        =
        ((flt2cttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if Z = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R]))
          \<and> 
         (flt2cttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if A = \<bullet> then [] else (if Z \<noteq> \<bullet> then [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R] else []))))" 
    by (induct A Z rule:prirelacc.induct, auto)
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
  finally show ?thesis unfolding prirelref_def by auto
qed

lemma
  "acceptance(A) = \<bullet> \<longleftrightarrow> flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = []"
  by auto

lemma
  assumes "flt2cttobs(fl) = ctA" "flt2cttobs(Z) = ctZ"
  shows "prirel p fl Z \<longleftrightarrow> prirelRef p ctA ctZ" 
  oops

lemma acceptances_same_set:
  assumes "acceptance Z \<noteq> \<bullet>"
  shows "acceptance Z = [{z. z \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z}]\<^sub>\<F>\<^sub>\<L>"
  using assms apply (cases Z, auto)
  by (case_tac a, auto)

lemma
  assumes "flt2cttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = ctA" "flt2cttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = ctZ"
          "event(Z) = Tock \<and> acceptance(Z) \<noteq> \<bullet>"
  shows "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
      =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(zz) \<and> (prirel p aa zz) \<and>
      ((ctA = [] \<and> (\<forall>b. (Tock <\<^sup>*p b) \<longrightarrow> b \<in> ref))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(aa)))"
proof -
  from assms(3) have event_Tock:"event(Z) = Tock \<and> acceptance(Z) \<noteq> \<bullet>"
      by auto
  then have ctZA:"ctZ = [{z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(Z)}]\<^sub>R # [Tock]\<^sub>E # (flt2cttobs zz)"
    using assms(2) by auto
  then have "\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> acceptance(Z) = [{z. z \<notin> ref}]\<^sub>\<F>\<^sub>\<L> \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R]"
    using event_Tock acceptances_same_set by auto
  then have "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> 
      (prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> [{z. z \<notin> ref}]\<^sub>\<F>\<^sub>\<L> \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    using event_Tock by (metis cttobs.inject(2) prirel.simps(4))
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> 
      (prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = Tock
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
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> 
      (prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = Tock
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
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      (acceptance(A) \<noteq> \<bullet> \<and> prirelacc p (acceptance A) (acceptance Z))))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
     \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> 
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      (\<exists>ref\<^sub>1. flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref\<^sub>1]\<^sub>R] \<and> prirelacc p (acceptance A) (acceptance Z))))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> 
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      (\<exists>ref\<^sub>1. flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref\<^sub>1]\<^sub>R] \<and> prirelref p ref = ref\<^sub>1)))"
    using prirelacc_eq_prirelref_via_flt2cttobs
    by blast
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[prirelref p ref]\<^sub>R]))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[prirelref p ref]\<^sub>R]))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((flt2cttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[prirelref p ref]\<^sub>R]))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[prirelref p ref]\<^sub>R]))"
    using assms(1) by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      flt2cttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(aa)))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(aa)))"
    using assms(1) by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> flt2cttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = [ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(zz) \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(aa)))"
    using event_Tock by auto
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(zz) \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(aa)))"
    using assms(2) by auto
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(zz) \<and> (prirel p aa zz) \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(aa)))"
    using assms(1) by force
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(zz) \<and> (prirel p aa zz) \<and>
      ((ctA = [] \<and> \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(aa)))"
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
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(zz) \<and> (prirel p aa zz) \<and>
      ((ctA = [] \<and> (\<forall>b. (Tock <\<^sup>*p b) \<longrightarrow> b \<in> ref))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # flt2cttobs(aa)))"  
    by auto
  finally show ?thesis .
qed

lemma
  assumes "flt2cttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = ctA" "flt2cttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = ctZ"
          "event(Z) = Tock \<and> acceptance(Z) = \<bullet>"
  shows "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) = (ctZ = [] \<and> ctA = [] \<and> (prirel p aa zz) \<and> maximal(p,Tock))"
proof -
  from assms(3) have event_Tock_bullet:"event(Z) = Tock \<and> acceptance(Z) = \<bullet>"
      by auto
  then have "ctZ = []"
    using assms(2) by auto
  then have "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
    =
    (flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> 
      (prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    using event_Tock_bullet by auto
  also have "... =
    (flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> acceptance(A) = \<bullet> \<and>
      (prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      (maximal(p,event(A)) 
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    using acceptance_not_bullet_imp_prirelacc event_Tock_bullet by blast
  also have "... =
    (flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> acceptance(A) = \<bullet> \<and>
      (prirel p aa zz) \<and> event(A) = Tock \<and> maximal(p,event(A)))"  
    using event_Tock_bullet by auto
  also have "... =
    (ctZ = [] \<and> acceptance(A) = \<bullet> \<and>
      (prirel p aa zz) \<and> event(A) = Tock \<and> maximal(p,event(A)))"  
    using assms event_Tock_bullet by auto
  also have "... =
    (ctZ = [] \<and> ctA = [] \<and>
      (prirel p aa zz) \<and> event(A) = Tock \<and> maximal(p,event(A)))" 
    using assms(1) by force
  also have "... =
    (ctZ = [] \<and> ctA = [] \<and> (prirel p aa zz) \<and> maximal(p,Tock))" 
    using assms(1) by force
  finally show ?thesis .
qed


lemma
  assumes "flt2cttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = ctA" "flt2cttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = ctZ"
          "event(Z) \<noteq> Tock"
    shows "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
        =
        (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs(aa) \<and>
         ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> (\<exists>S. flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. prirelref p S = R \<and> flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
proof -
    from assms have event_Tock_bullet:"event(Z) \<noteq> Tock"
      by auto
    then have "ctZ = [event Z]\<^sub>E # flt2cttobs(zz)"
      using assms(2) by auto
    then have "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
      =
      ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      by auto
    also have "... =
      ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event A]\<^sub>E # flt2cttobs(aa) \<and>
      (maximal(p,event(A))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      using assms by auto
    also have "... =
      ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event A]\<^sub>E # flt2cttobs(aa) \<and>
       (maximal(p,event(A))
       \<or> 
       (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
       acceptance(A) \<noteq> \<bullet>))"
      using assms by auto
    also have "... =
      ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event Z]\<^sub>E # flt2cttobs(aa) \<and>
      (maximal(p,event(Z))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      by auto
    then have p1:"prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) = 
      ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event Z]\<^sub>E # flt2cttobs(aa) \<and>
      (maximal(p,event(Z))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      using calculation assms by auto

    then have "(prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)) =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs(aa) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> event(A) = event(Z))
         \<or> 
        (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b) \<and> event(A) = event(Z))
         \<or>
        (prirelacc p (acceptance A) (acceptance Z) \<and> acceptance(A) \<noteq> \<bullet> \<and> event(A) = event(Z))))"
      by auto
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs(aa) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> event(A) = event(Z))
         \<or> 
        (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(Z) <\<^sup>*p b))
         \<or>
        (prirelacc p (acceptance A) (acceptance Z) \<and> acceptance(A) \<noteq> \<bullet> \<and> event(A) = event(Z))))"
      using assms(1) cttobs.inject(1) flt2cttobs.simps(2) by force
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(Z) <\<^sup>*p b))
         \<or>
         (prirelacc p (acceptance A) (acceptance Z) \<and> acceptance(A) \<noteq> \<bullet>)))"
      using assms(1) cttobs.inject(1) flt2cttobs.simps(2) by force
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(Z) <\<^sup>*p b))
         \<or>
         (\<exists>R S. prirelref p S = R \<and> flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by (smt acceptance_not_bullet_imp_prirelacc flt2cttobs.simps(1) list.discI prirelacc_eq_prirelref_via_flt2cttobs)
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> (\<exists>S. flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. prirelref p S = R \<and> flt2cttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> flt2cttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by auto

    finally show ?thesis
      using \<open>(prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event A <\<^sup>*p b) \<and> event A = event Z \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z)) = (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z))\<close> \<open>(prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z)) = (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs aa \<and> (maximal(p,event Z) \<and> acceptance A = \<bullet> \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet>))\<close> \<open>(prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs aa \<and> (maximal(p,event Z) \<and> acceptance A = \<bullet> \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet>)) = (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs aa \<and> (maximal(p,event Z) \<and> acceptance A = \<bullet> \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> (\<exists>R S. prirelref p S = R \<and> flt2cttobs \<langle>acceptance A\<rangle>\<^sub>\<F>\<^sub>\<L> = [[R]\<^sub>R] \<and> flt2cttobs \<langle>acceptance Z\<rangle>\<^sub>\<F>\<^sub>\<L> = [[S]\<^sub>R])))\<close> \<open>prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) = (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # flt2cttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event A <\<^sup>*p b) \<and> event A = event Z \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z))\<close> by auto
        
  qed

lemma flt2cttobs_consFL_eq_Nil: "flt2cttobs (A #\<^sub>\<F>\<^sub>\<L> fl) = [] \<longleftrightarrow> event(A) = Tock \<and> acceptance(A) = \<bullet>"
  by auto

lemma flt2cttobs_consFL_eq_Nil_imp_not_flt2goodTock: 
  assumes "\<forall>Z. A \<noteq> \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>" "flt2cttobs (A) = []"
  shows "\<not> flt2goodTock A"
proof (cases A)
  case (Acceptance x1)
  then show ?thesis using assms by auto
next
  case (AEvent x21 x22)
  have "event(x21) = Tock \<and> acceptance(x21) = \<bullet>"
    using assms AEvent flt2cttobs_consFL_eq_Nil by blast
  then have "\<not> flt2goodTock (x21 #\<^sub>\<F>\<^sub>\<L> x22)"
    by auto
  then have "\<not> flt2goodTock (A)"
    using AEvent by auto
  then show ?thesis by auto
qed

fun prirelcttobs :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> bool" where
"prirelcttobs p [[R]\<^sub>R] [[S]\<^sub>R] = (prirelref p S = R)" |
"prirelcttobs p [[A]\<^sub>R] [[e]\<^sub>E] = (maximal(p,e))"

lemma flt2cttobs_base_prirelacc_2:
  assumes "prirelacc p A Z"
  shows "flt2cttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) 
        = 
        (if A = \<bullet> then [] 
          else (if Z = \<bullet> then [[UNIV]\<^sub>R] else [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R]))"
proof -
  have "flt2cttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) 
        = 
        (if A = \<bullet> then [] else [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R])"
    using assms flt2cttobs_base_prirelacc by blast
  then show ?thesis by (cases Z, auto)
qed  

lemma
  assumes "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)"
  shows "flt2cttobs(A #\<^sub>\<F>\<^sub>\<L> aa) 
         = 
         (if event(Z) = Tock then
             (if acceptance(A) \<noteq> \<bullet> then
                 ((if acceptance(Z) = \<bullet> then [UNIV]\<^sub>R else [{z. z \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>acceptance(Z) \<and> z <\<^sup>*p b)}]\<^sub>R) # [Tock]\<^sub>E # (flt2cttobs aa))
              else []) 
          else ([event Z]\<^sub>E # flt2cttobs aa))"
proof -
  have "flt2cttobs(A #\<^sub>\<F>\<^sub>\<L> aa) 
        =
        (if event(A) = Tock then
             (if acceptance(A) \<noteq> \<bullet> then
                 ([{z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # (flt2cttobs aa))
              else []) 
          else ([event A]\<^sub>E # flt2cttobs aa))"
    by auto
  also have "... = 
        (if event(A) = Tock then
             (if acceptance(A) \<noteq> \<bullet> then
                 ((if acceptance(Z) = \<bullet> then [UNIV]\<^sub>R else [{z. z \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>acceptance(Z) \<and> z <\<^sup>*p b)}]\<^sub>R) # [Tock]\<^sub>E # (flt2cttobs aa))
              else []) 
          else ([event A]\<^sub>E # flt2cttobs aa))"
    using assms
    by (smt Collect_cong amember.simps(2) mem_Collect_eq prirel_cons_imp1 prirel_two_acceptances_bullet_not_bullet)
  also have "... = 
        (if event(Z) = Tock then
             (if acceptance(A) \<noteq> \<bullet> then
                 ((if acceptance(Z) = \<bullet> then [UNIV]\<^sub>R else [{z. z \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>acceptance(Z) \<and> z <\<^sup>*p b)}]\<^sub>R) # [Tock]\<^sub>E # (flt2cttobs aa))
              else []) 
          else ([event Z]\<^sub>E # flt2cttobs aa))"
    using assms
    by simp
  finally show ?thesis by auto
qed

lemma
  fixes P :: "('e cttobs) list set"
  shows "fl2ctt(pri p (ctt2fl P)) = P"
  unfolding fl2ctt_def ctt2fl_def apply auto
proof -
  have "fl2ctt(pri p (ctt2fl P)) = {flt2cttobs fl|fl. fl \<in> (pri p (ctt2fl P))}"
    unfolding fl2ctt_def by auto
  also have "... = {flt2cttobs fl|fl. fl \<in> (pri p (\<Union>{fl. FL1 fl \<and> (fl2ctt fl) \<subseteq> P}))}"
    unfolding ctt2fl_def by auto
  also have "... = {flt2cttobs fl|fl. fl \<in> \<Union>{pri p fl|fl. FL1 fl \<and> (fl2ctt fl) \<subseteq> P}}"
  proof -
    have "pri p (\<Union>{fl. FL1 fl \<and> (fl2ctt fl) \<subseteq> P}) = \<Union>{pri p fl|fl. fl \<in> {fl. FL1 fl \<and> (fl2ctt fl) \<subseteq> P}}"
      using pri_univ_dist by (metis Collect_cong)
    also have "... = \<Union>{pri p fl|fl. FL1 fl \<and> (fl2ctt fl) \<subseteq> P}"
      by auto
    then show ?thesis
      using calculation by auto
  qed
  also have "... = {flt2cttobs fl|fl. \<exists>x. (\<exists>fl. x = pri p fl \<and> FL1 fl \<and> (fl2ctt fl) \<subseteq> P) \<and> fl \<in> x}"
    unfolding fl2ctt_def by simp
  also have "... = {flt2cttobs fl|fl. \<exists>x. (\<exists>fl\<^sub>0. x = pri p fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> (fl2ctt fl\<^sub>0) \<subseteq> P) \<and> fl \<in> x}"
    by blast
  also have "... = {flt2cttobs fl|fl. \<exists>fl\<^sub>0. FL1 fl\<^sub>0 \<and> (fl2ctt fl\<^sub>0) \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0)}"
    unfolding pri_def by auto
  then have "... = {flt2cttobs fl|fl. \<exists>fl\<^sub>0. FL1 fl\<^sub>0 \<and> ({flt2cttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P) \<and>
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P)}"
  proof -
    have "\<forall>fl fl\<^sub>0. ((FL1 fl\<^sub>0 \<and> (fl2ctt fl\<^sub>0) \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))
          =
          (FL1 fl\<^sub>0 \<and> ({flt2cttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P) \<and>
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> flt2cttobs(Z) \<in> P)))"
      by (simp add: flt2cttobs_extn)
    then show ?thesis
      by auto
  qed
  oops

definition after :: "('e cttobs) list \<Rightarrow> ('e cttobs) list set \<Rightarrow> ('e cttobs) list set" where
"after x P = {z|z. x @ z \<in> P}"

fun prirelRef :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list set \<Rightarrow> bool" where
"prirelRef p [] [] s Q = True" |
(*"prirelRef p [] [[R]\<^sub>R] s Q = True" |*)
(* Very likely unnecessary case: 
"prirelRef p [] ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q = ((\<forall>b. (Tock <\<^sup>*p b) \<longrightarrow> b \<in> S) \<and> prirelRef p [] zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |*)
"prirelRef p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (prirelref p S = R)" |
"prirelRef p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q = ((R = prirelref p S) \<and> Tock \<notin> R \<and> prirelRef p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"prirelRef p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> prirelRef p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))))" |
"prirelRef p x y s Q = False"

(*
fun prirelAltRef :: "('e cttevent) partialorder \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list \<Rightarrow> ('e cttobs) list set \<Rightarrow> bool" where
"prirelAltRef p [] [] Q = True" |
"prirelAltRef p [[R]\<^sub>R] [[S]\<^sub>R] Q = (prirelref p S = R)" |
"prirelAltRef p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) Q = ((R = prirelref p S) \<and> prirelAltRef p aa zz (after [[S]\<^sub>R,[Tock]\<^sub>E] Q))" |
"prirelAltRef p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> prirelAltRef p aa zz (after [[e\<^sub>1]\<^sub>E] Q) \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. [[Z]\<^sub>R] \<in> Q \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))))" |
"prirelAltRef p x y Q = False"

thm prirelAltRef.induct*)

(* This is a nasty definition, but could be proved with 'function' using the
   following methods. *)

(*  apply (pat_completeness, simp_all)
  done
termination prirelRef
  by (relation "measure (\<lambda>(p,l,r,s,q). (size r + size l))", auto)
*)



end