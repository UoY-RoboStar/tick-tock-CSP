theory Event_Priority
imports
  "Main"
begin

text \<open> This theory defines a partial order type. \<close>

abbreviation less :: "('e \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> 'e \<Rightarrow> 'e \<Rightarrow> bool" where
"less f a b == f a b \<and> \<not>(f b a)"

text \<open> Here less is used to satisfy the axiom less_le_not_le of preorders. \<close>

typedef 'e partialorder = "{x :: 'e \<Rightarrow> 'e \<Rightarrow> bool. class.order x (less x)}"
  morphisms porder2f f2porder
  apply (simp add:class.order_def class.preorder_def class.order_axioms_def)
  apply (rule exI[where x="(=)"])
  by simp

text \<open> Thus @{type partialorder} is the type of all partial orders over the
       given type. \<close>

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

text \<open> We define the following notation so that the operator \<le> and < can be parametrised
       with a specific partial order. \<close>

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

lemma tau_max: "(\<forall>x. (x \<le>\<^sup>*(p) \<tau>)) \<Longrightarrow> \<not>(\<exists>x. (\<tau> <\<^sup>*(p) x))"
  apply auto
  by (simp add: partialorder.less_le_not_le)

lemma tau_max_imp_any_le_imp_le_tau:
  assumes "(\<forall>x. (x \<le>\<^sup>*(p) \<tau>))" "a <\<^sup>*p b"
  shows "a <\<^sup>*(p) \<tau>"
  using assms
  by (metis my_lt_def partialorder.order.not_eq_order_implies_strict)

end