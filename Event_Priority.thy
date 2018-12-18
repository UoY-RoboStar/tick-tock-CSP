theory Event_Priority
imports
  "Main"
begin

text \<open> This theory defines a partial order type, which is used to define a
       type for event priority partial orders. \<close>

abbreviation less :: "('e \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> 'e \<Rightarrow> 'e \<Rightarrow> bool" where
"less f a b == f a b \<and> \<not>(f b a)"

typedef 'e partialorder = "{x :: 'e \<Rightarrow> 'e \<Rightarrow> bool. class.order x (less x)}"
  morphisms porder2f f2porder
  apply (simp add:class.order_def class.preorder_def class.order_axioms_def)
  apply (rule exI[where x="(=)"])
  by simp

thm porder2f_induct
thm f2porder_inverse

definition my_le :: "'a partialorder \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where "my_le P = (porder2f P)"
definition my_lt :: "'a partialorder \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where "my_lt P = (less (my_le P))"

lemma porder2f_ref: "porder2f p x x"
  apply (induct p)
  apply (simp add:f2porder_inverse)
  by (simp add:class.order_def class.preorder_def class.order_axioms_def)

interpretation partialorder: order "my_le p" "my_lt p"
  apply (unfold_locales)
     apply (auto simp add:my_le_def my_lt_def)
    apply (induct p, simp add:f2porder_inverse)
    apply (simp add:class.order_def class.preorder_def class.order_axioms_def)
   apply (induct p, simp add:f2porder_inverse)
   apply (simp add:class.order_def class.order_axioms_def)
   apply (auto simp only:class.preorder_def)
  apply (induct p, simp add:f2porder_inverse)
  by (simp add:class.order_def class.order_axioms_def)

text \<open> The following datatype defines the elements to be compared in the
       event partial order, which includes also \<tau>, the internal event. \<close>

datatype 'e prievent = tau ("\<tau>") | prievent "'e" ("\<ee>'(_')")

definition trivial_tau :: "'e prievent \<Rightarrow> 'e prievent \<Rightarrow> bool" where "trivial_tau x y = (y = \<tau> \<or> x = y)"

lemma trivial_tau_order: "class.order trivial_tau (less trivial_tau)"
  by (simp add:trivial_tau_def class.order_def class.preorder_def class.order_axioms_def)

lemma trivial_tau_porder2f: "porder2f (f2porder (trivial_tau)) x \<tau>"
  using trivial_tau_def by (auto simp add:f2porder_inverse trivial_tau_order)

(*
class porder =
  fixes less_eq_p :: "'a partialorder \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
  and   less_p    :: "'a partialorder \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
*)
syntax
  "_porder_le"    :: "'a \<Rightarrow> 'a partialorder \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ \<le>\<^sup>*_ _)" [51, 51] 50)
  "_porder_lt"    :: "'a \<Rightarrow> 'a partialorder  \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ <\<^sup>*_ _)" [51, 51] 50)

translations
  "x \<le>\<^sup>*p y" == "CONST my_le p x y"
  "x <\<^sup>*p y" == "CONST my_lt p x y"

definition maximal :: "'a partialorder \<Rightarrow> 'a \<Rightarrow> bool" ("maximal'(_,_')" 65) where
"maximal(p,a) = (\<forall>x. (\<not> (a \<le>\<^sup>*p x) \<or> x \<le>\<^sup>*p a))"

lemma some_higher_not_maximal:
  assumes "z <\<^sup>*p b"
  shows "\<not>maximal(p,z)"
  using assms unfolding maximal_def apply auto
  by (meson partialorder.less_le_not_le)

lemma maximal_iff:
  "maximal(p,z) = (\<not>(\<exists>x. z <\<^sup>*p x))"
  unfolding maximal_def apply auto
  by (meson partialorder.less_le_not_le)+

(* Is this useful to endow a type with such an operator? *)
(*
instantiation prievent :: (type) porder 
begin
  definition less_eq_p_prievent :: "'a prievent partialorder \<Rightarrow> 'a prievent \<Rightarrow> 'a prievent \<Rightarrow> bool" where "less_eq_p_prievent p a b = my_le p a b"
  definition less_p_prievent :: "'a prievent partialorder \<Rightarrow> 'a prievent \<Rightarrow> 'a prievent \<Rightarrow> bool" where "less_p_prievent p a b = my_lt p a b"

interpretation prievent: order "my_le p" "my_lt p"
  by (unfold_locales)
 
instance 
  by intro_classes
end*)

lemma tau_max: "(\<forall>x. (x \<le>\<^sup>*(p) \<tau>)) \<Longrightarrow> \<not>(\<exists>x. (\<tau> <\<^sup>*(p) x))"
  apply auto
  by (simp add: partialorder.less_le_not_le)

lemma tau_max_imp_any_le_imp_le_tau:
  assumes "(\<forall>x. (x \<le>\<^sup>*(p) \<tau>))" "a <\<^sup>*p b"
  shows "a <\<^sup>*(p) \<tau>"
  using assms
  by (metis my_lt_def partialorder.order.not_eq_order_implies_strict)

text \<open> A priority order requires that \<tau> has maximal priority. This required,
       at least, for the Finite Linear model. \<close>

typedef 'e priorder = "{p :: ('e prievent) partialorder. \<forall>x. (x \<le>\<^sup>*(p) \<tau>)}"
  morphisms priorder2p p2priorder
  apply (simp add:my_le_def)
  by (rule exI[where x="f2porder (trivial_tau)"], auto simp add:trivial_tau_porder2f)

declare [[coercion_enabled]]
        [[coercion priorder2p]]

lemma
  fixes x :: "'e prievent"
  and   p :: "'e priorder"
  shows "x \<le>\<^sup>*p tau"
  using priorder2p by auto

end