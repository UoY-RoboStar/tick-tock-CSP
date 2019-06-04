theory Finite_Linear_Priority_Tau

imports
  Finite_Linear_Priority
  Finite_Linear_Tick_Param
begin
(*
fun prirelacc :: "'a prievent partialorder \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> bool" where
\<comment> \<open>Any acceptance Z is related to \<bullet>.\<close>
"prirelacc p \<bullet> Z = True" |
\<comment> \<open>Any acceptance Z, that is not \<bullet>, is related to A, where A is a set that 
    contains events in Z, such that no event b in Z is of higher priority as
    given by the partial order p.\<close>
"prirelacc p [A]\<^sub>\<F>\<^sub>\<L> [Z]\<^sub>\<F>\<^sub>\<L> = (A = {a. a \<in> Z \<and> \<not>(\<exists>b. b\<in>Z \<and> \<ee>(a) <\<^sup>*p \<ee>(b))})" |
"prirelacc p X Y = False"

text \<open> Pri is defined by the relation prirel below. The recursive case has been
       simplified in comparison to that in the paper, while the base case has
       been made clear. \<close>

fun prirel :: "'a prievent partialorder \<Rightarrow> 'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where
\<comment> \<open>The base case of this relation is given by prirelacc. \<close>
"prirel p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = (prirelacc p A Z \<and> (A = \<bullet> \<longrightarrow> Z = \<bullet>))" |
\<comment> \<open>The relation is defined for sequences of the same length. Observe, however,
    that this would not preclude the definition of a weaker relation whereby a
    longer sequence is related to a shorter sequence (see definition commented out). \<close>
"prirel p \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> (Z #\<^sub>\<F>\<^sub>\<L> zz) = False" | (* (prirelacc p A (acceptance Z)) *)
"prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) \<langle>Z\<rangle>\<^sub>\<F>\<^sub>\<L> = False" |
\<comment> \<open>The acceptance(A) and acceptance(Z) satisfy prirelacc, the events are the same, 
    and it is not the case that there is an event b in Z that has higher priority
    than event(A).\<close>
"prirel p (A #\<^sub>\<F>\<^sub>\<L> aa) (Z #\<^sub>\<F>\<^sub>\<L> zz) 
  = 
  ((prirelacc p (acceptance A) (acceptance Z)) \<and> (prirel p aa zz) \<and> event(A) = event(Z) 
    \<and> (event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance A \<or> acceptance A = \<bullet>) \<and>
      (maximal(p,\<ee>(event A)) 
       \<or> 
      (acceptance(Z) \<noteq> \<bullet> \<and> \<not>(\<exists>b. b \<in>\<^sub>\<F>\<^sub>\<L> acceptance(Z) \<and> \<ee>(event A) <\<^sup>*p \<ee>(b)))
       \<or>
      acceptance(A) \<noteq> \<bullet>))"

text \<open>We would like to relate traces that do not refer to \<tau> as events, but
      who contain such a special event to complete the partial order as in
      Roscoe's paper, with those who do not, and show that the result of 
      prirel is the same. \<close>
*)
fun accprievent2acc :: "'e prievent acceptance \<Rightarrow> 'e acceptance" where
"accprievent2acc \<bullet> = \<bullet>" |
"accprievent2acc [A]\<^sub>\<F>\<^sub>\<L> = [{x. \<ee>(x) \<in> A}]\<^sub>\<F>\<^sub>\<L>"

fun flprievent2fl :: "'e prievent fltrace \<Rightarrow> 'e fltrace" where
"flprievent2fl \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>accprievent2acc A\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"flprievent2fl (A #\<^sub>\<F>\<^sub>\<L> xs) = (accprievent2acc (acceptance A), (THE e. \<ee>(e) = event A))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> flprievent2fl xs"

definition poprievent2po :: "'e prievent partialorder \<Rightarrow> 'e partialorder" where
"poprievent2po p = f2porder (\<lambda> x y. \<ee>(x) \<le>\<^sup>*p \<ee>(y))"

thm f2porder_inverse
thm f2porder_inject
thm f2porder_induct

lemma class_order_less: 
  assumes "class.order ya (Event_Priority.less ya)"
  shows "(\<lambda>x y. ya \<ee>(x) \<ee>(y)) \<in> {x. class.order x (Event_Priority.less x)}"
  using assms apply auto
  apply (simp add:class.order_def class.preorder_def class.order_axioms_def)
  using class.order_def class.preorder_def class.order_axioms_def by blast


lemma poprievent2po_p:
  assumes "(x \<le>\<^sup>*(poprievent2po p) y)"
  shows "(\<ee>(x) \<le>\<^sup>*p \<ee>(y))"
  using assms 
proof (induct p)
  case (f2porder z)
  then have class_z:"class.order z (Event_Priority.less z)"
    by auto
  then have a:"(x \<le>\<^sup>*(poprievent2po (f2porder z)) y)
            =
            porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y))) x y"
    apply auto
    unfolding poprievent2po_def my_le_def 
    by (simp_all add:f2porder_inverse)
  then have b:"(\<ee>(x) \<le>\<^sup>*(f2porder z) \<ee>(y)) = (z \<ee>(x) \<ee>(y))"
    using class_z unfolding poprievent2po_def my_le_def 
    by (simp_all add:f2porder_inverse)

  from class_z have "(\<lambda>x y. z \<ee>(x) \<ee>(y)) \<in> {x. class.order x (Event_Priority.less x)}"
    using class_order_less by blast
  then have "porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y))) x y = (z \<ee>(x) \<ee>(y))"
    by (simp add:f2porder_inverse)
 
  then have "(z \<ee>(x) \<ee>(y))"
   using a f2porder.prems by blast
  then show ?case using b by auto
qed

lemma p_poprievent2po:
  assumes "(\<ee>(x) \<le>\<^sup>*p \<ee>(y))" 
  shows "(x \<le>\<^sup>*(poprievent2po p) y)"
  using assms 
proof (induct p)
  case (f2porder z)
  then have class_z:"class.order z (Event_Priority.less z)"
    by auto
  then have a:"(x \<le>\<^sup>*(poprievent2po (f2porder z)) y)
            =
            porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y))) x y"
    apply auto
    unfolding poprievent2po_def my_le_def 
    by (simp_all add:f2porder_inverse)
  then have b:"(\<ee>(x) \<le>\<^sup>*(f2porder z) \<ee>(y)) = (z \<ee>(x) \<ee>(y))"
    using class_z unfolding poprievent2po_def my_le_def 
    by (simp_all add:f2porder_inverse)

  from class_z have "(\<lambda>x y. z \<ee>(x) \<ee>(y)) \<in> {x. class.order x (Event_Priority.less x)}"
    using class_order_less by blast
  then have "porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y))) x y = (z \<ee>(x) \<ee>(y))"
    by (simp add:f2porder_inverse)
  then have "(z \<ee>(x) \<ee>(y))"
   using b f2porder.prems by blast
  then show ?case using a b
    using \<open>porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y))) x y = z \<ee>(x) \<ee>(y)\<close> by blast
qed

lemma poprievent2po_iff:
  "(\<ee>(x) \<le>\<^sup>*p \<ee>(y)) = (x \<le>\<^sup>*(poprievent2po p) y)"
  using poprievent2po_p p_poprievent2po by metis

lemma poprievent2po_lt_p:
  assumes "(x <\<^sup>*(poprievent2po p) y)"
  shows "(\<ee>(x) <\<^sup>*p \<ee>(y))"
  using assms
proof (induct p)
  case (f2porder z)
  then have class_z:"class.order z (Event_Priority.less z)"
    by auto
  then have a:"(x <\<^sup>*(poprievent2po (f2porder z)) y)
            =
            less (porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y)))) x y"
    apply auto
    unfolding poprievent2po_def my_lt_def my_le_def
    by (simp_all add:f2porder_inverse)
  then have b:"(\<ee>(x) <\<^sup>*(f2porder z) \<ee>(y)) = ((less z) \<ee>(x) \<ee>(y))"
    using class_z unfolding poprievent2po_def my_le_def my_lt_def
    by (simp_all add:f2porder_inverse)

  from class_z have "(\<lambda>x y. z \<ee>(x) \<ee>(y)) \<in> {x. class.order x (Event_Priority.less x)}"
    using class_order_less by blast
  then have "less (porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y)))) x y = ((less z) \<ee>(x) \<ee>(y))"
    by (simp add:f2porder_inverse)
 
  then have "((less z) \<ee>(x) \<ee>(y))"
   using a f2porder.prems by blast
  then show ?case using b by auto
qed

lemma p_poprievent2po_lt:
  assumes "(\<ee>(x) <\<^sup>*p \<ee>(y))" 
  shows "(x <\<^sup>*(poprievent2po p) y)"
  using assms 
proof (induct p)
  case (f2porder z)
  then have class_z:"class.order z (Event_Priority.less z)"
    by auto
  then have a:"(x <\<^sup>*(poprievent2po (f2porder z)) y)
            =
            less (porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y)))) x y"
    apply auto
    unfolding poprievent2po_def my_lt_def my_le_def
    by (simp_all add:f2porder_inverse)
  then have b:"(\<ee>(x) <\<^sup>*(f2porder z) \<ee>(y)) = ((less z) \<ee>(x) \<ee>(y))"
    using class_z unfolding poprievent2po_def my_le_def my_lt_def
    by (simp_all add:f2porder_inverse)

  from class_z have "(\<lambda>x y. z \<ee>(x) \<ee>(y)) \<in> {x. class.order x (Event_Priority.less x)}"
    using class_order_less by blast
  then have "less (porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y)))) x y = ((less z) \<ee>(x) \<ee>(y))"
    by (simp add:f2porder_inverse)
 
 then have "(less z) \<ee>(x) \<ee>(y)"
   using b f2porder.prems by blast
  then show ?case using a b
    using \<open>less (porder2f (f2porder (\<lambda>x y. z \<ee>(x) \<ee>(y)))) x y = ((less z) \<ee>(x) \<ee>(y))\<close> by blast
qed

lemma poprievent2po_lt_iff:
  "(\<ee>(x) <\<^sup>*p \<ee>(y)) = (x <\<^sup>*(poprievent2po p) y)"
  using poprievent2po_lt_p p_poprievent2po_lt by metis


lemma
  assumes "prirelacc (poprievent2po p) (accprievent2acc A) (accprievent2acc Z)"
  shows "prirelacc p A Z" 
  using assms apply (induct p A Z rule:prirelacc.induct, auto)
  sledgehammer
  apply (auto simp add:poprievent2po_iff)
  
  unfolding poprievent2po_def apply auto

lemma
  assumes "prirelacc p A Z" "maximal(p,\<tau>)" "\<forall>a b. (a <\<^sup>*p b) \<longrightarrow> a <\<^sup>*p \<tau>"
  shows "prirelacc (poprievent2po p) (accprievent2acc A) (accprievent2acc Z)"
  using assms apply (induct p A Z rule:prirelacc.induct, auto)
  
   apply (meson partialorder.less_le_not_le poprievent2po_iff)
  apply (simp add:poprievent2po_lt_iff[symmetric])
  apply (case_tac b, auto)
 
lemma 
  assumes "\<tau> \<notin> events(aa)" "\<tau> \<notin> events(zz)" "prirel p aa zz"
  shows "prirel (poprievent2po p) (flprievent2fl aa) (flprievent2fl zz)"
  using assms apply(induct p aa zz rule:prirel.induct, auto)


lemma 
  assumes "\<tau> \<notin> events(aa)" "\<tau> \<notin> events(zz)"
  shows "prirel p aa zz
        = 
        prirel (poprievent2po p) (flprievent2fl aa) (flprievent2fl zz)"
  using assms nitpick

end