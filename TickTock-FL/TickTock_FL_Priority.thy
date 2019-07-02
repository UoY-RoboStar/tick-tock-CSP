theory
  TickTock_FL_Priority
imports
  "TickTock.TickTock_Prioritise"
  TickTock_Max_FL
  "FL.Finite_Linear_Priority"
begin

lemma pri_univ_dist:
  "pri p (\<Union> X) = \<Union>{pri p x|x. x \<in> X}"
  unfolding pri_def by auto

lemma fl2ttobs_extn:
  (*assumes TTwf_healthy: "TTwf P" 
        and TT1w_healthy: "TT1w P"
        and TT3_healthy:  "TT3 P"*)
    shows
  "(fl2ttm fl\<^sub>0 \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))
   =
   ({fl2ttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs(Z) \<in> P))"
proof -

    have "((fl2ttm fl\<^sub>0) \<subseteq> P \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))
          =
          ((\<forall>x. x \<in> (fl2ttm fl\<^sub>0) \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>x. x \<in> {fl2ttobs fl|fl. fl \<in> fl\<^sub>0} \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      unfolding fl2ttm_def by auto
    also have "... =
          ((\<forall>x. (\<exists>fl. x = fl2ttobs(fl) \<and> fl \<in> fl\<^sub>0) \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>x fl. (x = fl2ttobs(fl) \<and> fl \<in> fl\<^sub>0) \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>fl. fl \<in> fl\<^sub>0 \<longrightarrow> fl2ttobs(fl) \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          ((\<forall>fl. (fl \<in> fl\<^sub>0 \<longrightarrow> fl2ttobs(fl) \<in> P)) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
    also have "... =
          (\<forall>fl\<^sub>x. (fl\<^sub>x \<in> fl\<^sub>0 \<longrightarrow> fl2ttobs(fl\<^sub>x) \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))"
      by auto
  then have "...
        =
        (\<forall>fl\<^sub>x. (fl\<^sub>x \<in> fl\<^sub>0 \<longrightarrow> fl2ttobs(fl\<^sub>x) \<in> P) \<and> 
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs(Z) \<in> P))"
    by auto
  then have "... =
        ((\<forall>x fl. (x = fl2ttobs(fl) \<and> fl \<in> fl\<^sub>0) \<longrightarrow> x \<in> P) \<and>
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs(Z) \<in> P))"
    by auto
  then have "... =
        (({fl2ttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P) \<and>
              (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0 \<and> fl2ttobs(Z) \<in> P))"
    by auto
  ultimately show ?thesis
    by (smt \<open>((\<forall>x. x \<in> fl2ttm fl\<^sub>0 \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0)) = ((\<forall>x. x \<in> {fl2ttobs fl |fl. fl \<in> fl\<^sub>0} \<longrightarrow> x \<in> P) \<and> (\<exists>Z. prirel p fl Z \<and> Z \<in> fl\<^sub>0))\<close> mem_Collect_eq subset_eq)
qed


lemma
  "fl2ttm(pri p P) = priTT p fl2ttm(P)"
proof -
  have "fl2ttm(pri p P) = {fl2ttobs fl|fl. fl \<in> (pri p P)}"
    unfolding fl2ttm_def by simp
  also have "... = {fl2ttobs fl|fl. fl \<in> {A|A Z. prirel p A Z \<and> Z \<in> P}}"
    unfolding pri_def by simp
  also have "... = {fl2ttobs fl|fl A Z. prirel p fl Z \<and> Z \<in> P}"
    by auto
  oops

lemma
  assumes TTwf_healthy: "TTwf P" 
      and TT1w_healthy: "TT1w P"
      and TT3_healthy:  "TT3 P"
    shows
  "\<exists>fl. flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x) \<and> fl2ttobs(fl) \<in> P"
proof -
  have "(\<exists>fl. flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x) \<and> fl2ttobs(fl) \<in> P)
        =
        (\<exists>fl x. x = fl2ttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x) \<and> x \<in> P)"
    by blast
  then have "(\<exists>fl x. x = fl2ttobs fl \<and> flt2goodTock fl \<and> (\<exists>x. FL1 x \<and> {fl2ttobs fl |fl. fl \<in> x} \<subseteq> P \<and> fl \<in> x))"
    using assms TTwf_1c_3_imp_fl2ttobs_FL1
    apply auto
    oops
  (*  "(\<exists>fl\<^sub>0. {fl2ttobs fl|fl. fl \<in> fl\<^sub>0} \<subseteq> P \<and> 
              (\<exists>Z.  Z \<in> fl\<^sub>0 \<and> FL1 fl\<^sub>0 \<and> flt2goodTock Z \<and>  \<in> P))"*)



lemma fl2ttobs_base_prirelacc:
  assumes "prirelacc p A Z"
  shows "fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if A = \<bullet> then [] else [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R])"
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

lemma fl2ttobs_base_Z_prirelacc:
  assumes "prirelacc p A Z"
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

lemma fl2ttobs_base_Z_prirelacc_iff:
   "prirelacc p A Z \<longleftrightarrow>
         ((fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if Z = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R]))
          \<and> 
         (fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if A = \<bullet> then [] else (if Z \<noteq> \<bullet> then [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R] else []))))"
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

lemma prirelacc_eq_prirelref_via_fl2ttobs:
  assumes "fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R]" "fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R]"
  shows "prirelacc p A Z \<longleftrightarrow> (prirelref p S = R)"
proof -
  have "prirelacc p A Z 
        =
        ((fl2ttobs(\<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if Z = \<bullet> then [] else [[{z. z \<notin>\<^sub>\<F>\<^sub>\<L> Z}]\<^sub>R]))
          \<and> 
         (fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) = (if A = \<bullet> then [] else (if Z \<noteq> \<bullet> then [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R] else []))))" 
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
  "acceptance(A) = \<bullet> \<longleftrightarrow> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = []"
  by auto

lemma acceptances_same_set:
  assumes "acceptance Z \<noteq> \<bullet>"
  shows "acceptance Z = [{z. z \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z}]\<^sub>\<F>\<^sub>\<L>"
  using assms apply (cases Z, auto)
  by (case_tac a, auto)

lemma
  assumes "fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = ctA" "fl2ttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = ctZ"
          "event(Z) = Tock \<and> acceptance(Z) \<noteq> \<bullet>"
  shows "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
      =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (prirel p aa zz) \<and>
      ((ctA = [] \<and> (\<forall>b. (Tock <\<^sup>*p b) \<longrightarrow> b \<in> ref))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
proof -
  from assms(3) have event_Tock:"event(Z) = Tock \<and> acceptance(Z) \<noteq> \<bullet>"
      by auto
  then have ctZA:"ctZ = [{z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(Z)}]\<^sub>R # [Tock]\<^sub>E # (fl2ttobs zz)"
    using assms(2) by auto
  then have "\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> acceptance(Z) = [{z. z \<notin> ref}]\<^sub>\<F>\<^sub>\<L> \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R]"
    using event_Tock acceptances_same_set by auto
  then have "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> 
      (prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or> 
      (\<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> [{z. z \<notin> ref}]\<^sub>\<F>\<^sub>\<L> \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    using event_Tock by (metis ttobs.inject(2) prirel.simps(4))
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> 
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
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> 
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
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
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
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
     \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> 
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      (\<exists>ref\<^sub>1. fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref\<^sub>1]\<^sub>R] \<and> prirelacc p (acceptance A) (acceptance Z))))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> 
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      (\<exists>ref\<^sub>1. fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref\<^sub>1]\<^sub>R] \<and> prirelref p ref = ref\<^sub>1)))"
    using prirelacc_eq_prirelref_via_fl2ttobs
    by blast
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((acceptance(A) = \<bullet> \<and> 
        (maximal(p,event(A)) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> event(A) <\<^sup>*p b)))
      \<or>
      fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[prirelref p ref]\<^sub>R]))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[prirelref p ref]\<^sub>R]))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      ((fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[prirelref p ref]\<^sub>R]))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[prirelref p ref]\<^sub>R]))"
    using assms(1) by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[ref]\<^sub>R] \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    using assms(1) by auto
  also have "...
    =
    (\<exists>ref. [ref]\<^sub>R = hd ctZ \<and> fl2ttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    using event_Tock by auto
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    using assms(2) by auto
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (prirel p aa zz) \<and>
      ((ctA = [] \<and> 
        (maximal(p,Tock) 
        \<or> 
        \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b)))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
    using assms(1) by force
  also have "...
    =
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (prirel p aa zz) \<and>
      ((ctA = [] \<and> \<not>(\<exists>b. b \<notin> ref \<and> Tock <\<^sup>*p b))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"
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
    (\<exists>ref. ctZ = [ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(zz) \<and> (prirel p aa zz) \<and>
      ((ctA = [] \<and> (\<forall>b. (Tock <\<^sup>*p b) \<longrightarrow> b \<in> ref))
      \<or>
      ctA = [prirelref p ref]\<^sub>R # [Tock]\<^sub>E # fl2ttobs(aa)))"  
    by auto
  finally show ?thesis .
qed

lemma
  assumes "fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = ctA" "fl2ttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = ctZ"
          "event(Z) = Tock \<and> acceptance(Z) = \<bullet>"
  shows "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) = (ctZ = [] \<and> ctA = [] \<and> (prirel p aa zz) \<and> maximal(p,Tock))"
proof -
  from assms(3) have event_Tock_bullet:"event(Z) = Tock \<and> acceptance(Z) = \<bullet>"
      by auto
  then have "ctZ = []"
    using assms(2) by auto
  then have "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
    =
    (fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> 
      (prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = Tock 
      \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,event(A)) 
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    using event_Tock_bullet by auto
  also have "... =
    (fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> acceptance(A) = \<bullet> \<and>
      (prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = Tock \<and>
      (maximal(p,event(A)) 
       \<or>
      acceptance(A) \<noteq> \<bullet>))
    "
    using acceptance_not_bullet_imp_prirelacc event_Tock_bullet by blast
  also have "... =
    (fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [] \<and> acceptance(A) = \<bullet> \<and>
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
  assumes "fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) = ctA" "fl2ttobs(Z #\<^sub>\<F>\<^sub>\<L> zz) = ctZ"
          "event(Z) \<noteq> Tock"
    shows "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)
        =
        (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
         ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> (\<exists>S. fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> event(Z) \<notin> S \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. prirelref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
proof -
    from assms have event_Tock_bullet:"event(Z) \<noteq> Tock"
      by auto
    then have "ctZ = [event Z]\<^sub>E # fl2ttobs(zz)"
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
        ctA = [event A]\<^sub>E # fl2ttobs(aa) \<and>
      (maximal(p,event(A))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      using assms by auto
    also have "... =
      ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event A]\<^sub>E # fl2ttobs(aa) \<and>
       (maximal(p,event(A))
       \<or> 
       (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
       acceptance(A) \<noteq> \<bullet>))"
      using assms by auto
    also have "... =
      ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
      (maximal(p,event(Z))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      by auto
    then have p1:"prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) = 
      ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
        \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
      (maximal(p,event(Z))
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"
      using calculation assms by auto

    then have "(prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)) =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> event(A) = event(Z))
         \<or> 
        (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(A) <\<^sup>*p b) \<and> event(A) = event(Z))
         \<or>
        (prirelacc p (acceptance A) (acceptance Z) \<and> acceptance(A) \<noteq> \<bullet> \<and> event(A) = event(Z))))"
      by auto
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
        ((maximal(p,event(A)) \<and> acceptance(A) = \<bullet> \<and> event(A) = event(Z))
         \<or> 
        (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(Z) <\<^sup>*p b))
         \<or>
        (prirelacc p (acceptance A) (acceptance Z) \<and> acceptance(A) \<noteq> \<bullet> \<and> event(A) = event(Z))))"
      using assms(1) ttobs.inject(1) fl2ttobs.simps(2) by force
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(Z) <\<^sup>*p b))
         \<or>
         (prirelacc p (acceptance A) (acceptance Z) \<and> acceptance(A) \<noteq> \<bullet>)))"
      using assms(1) ttobs.inject(1) fl2ttobs.simps(2) by force
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> event(Z) <\<^sup>*p b))
         \<or>
         (\<exists>R S. prirelref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by (smt acceptance_not_bullet_imp_prirelacc fl2ttobs.simps(1) list.discI prirelacc_eq_prirelref_via_fl2ttobs)
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> (\<exists>S. fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. prirelref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by auto
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> event(Z) \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> (\<exists>S. fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. prirelref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by auto
    also have "... =
      (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs(aa) \<and>
        ((maximal(p,event(Z)) \<and> acceptance(A) = \<bullet>)
         \<or> 
         (acceptance(A) = \<bullet> \<and> event(Z) \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> (\<exists>S. fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R] \<and> event(Z) \<notin> S \<and> \<not>(\<exists>b. b \<notin> S \<and> event(Z) <\<^sup>*p b)))
         \<or>
         (\<exists>R S. prirelref p S = R \<and> fl2ttobs(\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[R]\<^sub>R] \<and> fl2ttobs(\<langle>acceptance(Z)\<rangle>\<^sub>\<F>\<^sub>\<L>) = [[S]\<^sub>R])))"
      by auto
    finally show ?thesis
      using \<open>(prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event A <\<^sup>*p b) \<and> event A = event Z \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z)) = (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z))\<close> \<open>(prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z)) = (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (maximal(p,event Z) \<and> acceptance A = \<bullet> \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet>))\<close> \<open>(prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (maximal(p,event Z) \<and> acceptance A = \<bullet> \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet>)) = (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (maximal(p,event Z) \<and> acceptance A = \<bullet> \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event Z <\<^sup>*p b) \<or> (\<exists>R S. prirelref p S = R \<and> fl2ttobs \<langle>acceptance A\<rangle>\<^sub>\<F>\<^sub>\<L> = [[R]\<^sub>R] \<and> fl2ttobs \<langle>acceptance Z\<rangle>\<^sub>\<F>\<^sub>\<L> = [[S]\<^sub>R])))\<close> \<open>prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) = (prirel p aa zz \<and> ctA = [event Z]\<^sub>E # fl2ttobs aa \<and> (event A \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and> (maximal(p,event A) \<and> acceptance A = \<bullet> \<and> event A = event Z \<or> acceptance A = \<bullet> \<and> acceptance Z \<noteq> \<bullet> \<and> (\<nexists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance Z \<and> event A <\<^sup>*p b) \<and> event A = event Z \<or> prirelacc p (acceptance A) (acceptance Z) \<and> acceptance A \<noteq> \<bullet> \<and> event A = event Z))\<close> by auto
        
  qed

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

fun prirelttobs :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> bool" where
"prirelttobs p [[R]\<^sub>R] [[S]\<^sub>R] = (prirelref p S = R)" |
"prirelttobs p [[A]\<^sub>R] [[e]\<^sub>E] = (maximal(p,e))"

lemma fl2ttobs_base_prirelacc_2:
  assumes "prirelacc p A Z"
  shows "fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) 
        = 
        (if A = \<bullet> then [] 
          else (if Z = \<bullet> then [[UNIV]\<^sub>R] else [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R]))"
proof -
  have "fl2ttobs(\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>) 
        = 
        (if A = \<bullet> then [] else [[{z. z \<in>\<^sub>\<F>\<^sub>\<L> Z \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>Z \<and> z <\<^sup>*p b)}]\<^sub>R])"
    using assms fl2ttobs_base_prirelacc by blast
  then show ?thesis by (cases Z, auto)
qed  

lemma
  assumes "prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz)"
  shows "fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) 
         = 
         (if event(Z) = Tock then
             (if acceptance(A) \<noteq> \<bullet> then
                 ((if acceptance(Z) = \<bullet> then [UNIV]\<^sub>R else [{z. z \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>acceptance(Z) \<and> z <\<^sup>*p b)}]\<^sub>R) # [Tock]\<^sub>E # (fl2ttobs aa))
              else []) 
          else ([event Z]\<^sub>E # fl2ttobs aa))"
proof -
  have "fl2ttobs(A #\<^sub>\<F>\<^sub>\<L> aa) 
        =
        (if event(A) = Tock then
             (if acceptance(A) \<noteq> \<bullet> then
                 ([{z. z \<notin>\<^sub>\<F>\<^sub>\<L> acceptance(A)}]\<^sub>R # [Tock]\<^sub>E # (fl2ttobs aa))
              else []) 
          else ([event A]\<^sub>E # fl2ttobs aa))"
    by auto
  also have "... = 
        (if event(A) = Tock then
             (if acceptance(A) \<noteq> \<bullet> then
                 ((if acceptance(Z) = \<bullet> then [UNIV]\<^sub>R else [{z. z \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>acceptance(Z) \<and> z <\<^sup>*p b)}]\<^sub>R) # [Tock]\<^sub>E # (fl2ttobs aa))
              else []) 
          else ([event A]\<^sub>E # fl2ttobs aa))"
    using assms
    by (smt Collect_cong amember.simps(2) mem_Collect_eq prirel_cons_imp1 prirel_two_acceptances_bullet_not_bullet)
  also have "... = 
        (if event(Z) = Tock then
             (if acceptance(A) \<noteq> \<bullet> then
                 ((if acceptance(Z) = \<bullet> then [UNIV]\<^sub>R else [{z. z \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<longrightarrow> (\<exists>b. b\<in>\<^sub>\<F>\<^sub>\<L>acceptance(Z) \<and> z <\<^sup>*p b)}]\<^sub>R) # [Tock]\<^sub>E # (fl2ttobs aa))
              else []) 
          else ([event Z]\<^sub>E # fl2ttobs aa))"
    using assms
    by simp
  finally show ?thesis by auto
qed

definition after :: "('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttobs) list set" where
"after x P = {z|z. x @ z \<in> P}"



(*
fun prirelAltRef :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> bool" where
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