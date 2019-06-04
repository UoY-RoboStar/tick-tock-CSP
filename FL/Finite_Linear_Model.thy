theory Finite_Linear_Model

imports
  Main
begin

text \<open> This theory is an encoding of the Finite Linear model, the most discriminating CSP 
       denotational model in the hierarchy of CSP models. It is just as discriminating as 
       weak bisimulation over the operational semantics of CSP. \<close>

section \<open> Model \<close>

subsection \<open> Acceptances \<close>

text \<open> An acceptance is either \<bullet> or a set. \<close>

datatype 'e acceptance = acnil ("\<bullet>") | acset "'e set" ("[_]\<^sub>\<F>\<^sub>\<L>")

text \<open> Here we define an order on acceptances, whereby \<bullet> is related to
       any element, and otherwise sets need to be equal. \<close>

instantiation acceptance :: (type) order
begin
  fun less_eq_acceptance :: "'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> bool" where
  "\<bullet> \<le> S = True" |
  "R \<le> \<bullet> = (R = \<bullet>)" |
  "[X]\<^sub>\<F>\<^sub>\<L> \<le> [Y]\<^sub>\<F>\<^sub>\<L> = (if X = Y then True else False)"
  definition less_acceptance :: "'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> bool" where
  "less_acceptance S R = (S \<le> R \<and> \<not> R \<le> S)"
instance proof
  fix x y z :: "'a acceptance"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_acceptance_def)
  show "x \<le> x"
    by (cases x, simp_all)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    apply (cases x, simp_all, cases y, simp_all, cases z, simp_all)
    by presburger
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis less_eq_acceptance.elims(2) less_eq_acceptance.simps(2))
qed
end

text \<open> We also define a plus operator on acceptances that allows \<bullet> to
       be augmented, but nothing else. \<close>

instantiation acceptance :: (type) plus
begin

fun plus_acceptance :: "'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance"  where
  "plus_acceptance \<bullet> R = R" |
  "plus_acceptance S \<bullet> = S" |
  "plus_acceptance [S]\<^sub>\<F>\<^sub>\<L> [R]\<^sub>\<F>\<^sub>\<L> = [S]\<^sub>\<F>\<^sub>\<L>"

instance
  by intro_classes
end

text \<open> It is associative, and thus we have a semigroup. \<close>

lemma acceptance_assoc:
  fixes a b c :: "'a acceptance"
  shows "(a + b) + c = a + (b + c)"
  apply (induct a)
   apply (case_tac b, auto)
  apply (case_tac b, auto)
  by (case_tac c, auto)

instantiation acceptance :: (type) semigroup_add
begin

instance
  apply (intro_classes)
  by (simp add:acceptance_assoc)
end

lemma acceptance_right_zero[simp]:
  fixes a :: "'a acceptance"
  shows "a + \<bullet> = a"
  by (induct a, auto)

lemma acceptance_left_zero[simp]:
  fixes a :: "'a acceptance"
  shows "\<bullet> + a = a"
  by (induct a, auto)

text \<open> Taking \<bullet> as the zero, we have thus a monoid. \<close>

instantiation acceptance :: (type) monoid_add
begin

definition zero_acceptance where "zero_acceptance = \<bullet>"
instance 
  apply (intro_classes)
  by (simp add:zero_acceptance_def)+
end

instantiation acceptance :: (type) minus
begin

fun minus_acceptance :: "'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance"  where
  "minus_acceptance \<bullet> R = \<bullet>" |
  "minus_acceptance S \<bullet> = S" |
  "minus_acceptance [S]\<^sub>\<F>\<^sub>\<L> [R]\<^sub>\<F>\<^sub>\<L> = [S - R]\<^sub>\<F>\<^sub>\<L>"

instance
  by intro_classes
end

fun amember :: "'a \<Rightarrow> 'a acceptance \<Rightarrow> bool" ("(_/ \<in>\<^sub>\<F>\<^sub>\<L> _)" [51, 51] 50) where
"x \<in>\<^sub>\<F>\<^sub>\<L> \<bullet> = False" | "x \<in>\<^sub>\<F>\<^sub>\<L> [R]\<^sub>\<F>\<^sub>\<L> = (x \<in> R)"

abbreviation rnot_member ("(_/ \<notin>\<^sub>\<F>\<^sub>\<L> _)" [51, 51] 50)
  where "rnot_member x A \<equiv> \<not> (x \<in>\<^sub>\<F>\<^sub>\<L>  A)"

text \<open> Note that we adopt the following definition following page 257 of UCS, rather
       than use our definition of plus. \<close>

fun aunion :: "'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance" (infixl "\<union>\<^sub>\<F>\<^sub>\<L>" 65) where
"aunion \<bullet> X = \<bullet>" |
"aunion X \<bullet> = \<bullet>" |
"aunion [S]\<^sub>\<F>\<^sub>\<L> [R]\<^sub>\<F>\<^sub>\<L> = [S \<union> R]\<^sub>\<F>\<^sub>\<L>"

lemma aunion_idem: "a \<union>\<^sub>\<F>\<^sub>\<L> a = a"
  by (cases a, auto)

lemma aunion_assoc: "(a \<union>\<^sub>\<F>\<^sub>\<L> b) \<union>\<^sub>\<F>\<^sub>\<L> c = a \<union>\<^sub>\<F>\<^sub>\<L> (b \<union>\<^sub>\<F>\<^sub>\<L> c)"
  by (cases a, auto, cases b, auto, cases c, auto)

lemma aunion_comm: "a \<union>\<^sub>\<F>\<^sub>\<L> b = b \<union>\<^sub>\<F>\<^sub>\<L> a"
  by (cases a, auto, cases b, auto, cases b, auto)

interpretation aunion_comm_monoid: comm_monoid "aunion" "[{}]\<^sub>\<F>\<^sub>\<L>"
  apply (unfold_locales)
  using aunion_assoc apply blast
  using aunion_comm apply blast
  by (case_tac a, auto)+

subsection \<open> Acceptance Events \<close>

text \<open> Here we define the type for an acceptance followed by an event as
       an aevent type definition of pairs (X,a) where the event a belongs 
       to the acceptance X or X is \<bullet>. \<close>

typedef 'e aevent = "{(X :: 'e acceptance, a :: 'e). a \<in>\<^sub>\<F>\<^sub>\<L> X \<or> X = \<bullet>}" by auto

syntax
  "_revent"     :: "args \<Rightarrow> 'e \<Rightarrow> 'e aevent"    ("'(_,_')\<^sub>\<F>\<^sub>\<L>")

translations
  "(x,y)\<^sub>\<F>\<^sub>\<L>" == "CONST Abs_aevent (x,y)"

setup_lifting type_definition_aevent

thm Rep_aevent
thm Abs_aevent_inverse
thm type_definition_aevent

lift_definition acceptance :: "'e aevent \<Rightarrow> 'e acceptance" is fst .
lift_definition event   :: "'e aevent \<Rightarrow> 'e" is snd .

subsubsection \<open> Partial order \<close>

instantiation aevent :: (type) order
begin
  definition less_eq_aevent :: "'e aevent \<Rightarrow> 'e aevent \<Rightarrow> bool" where "less_eq_aevent a b \<equiv> acceptance a \<le> acceptance b \<and> event a = event b"
  definition less_aevent :: "'e aevent \<Rightarrow> 'e aevent \<Rightarrow> bool" where "less_aevent a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)"

instance apply intro_classes
     apply (auto simp add:less_aevent_def less_eq_aevent_def)
  by (metis Rep_aevent_inject acceptance.rep_eq event.rep_eq prod.expand)
end

instantiation aevent :: (type) plus
begin

definition plus_aevent :: "'a aevent \<Rightarrow> 'a aevent \<Rightarrow> 'a aevent" where
"plus_aevent A B = (if event(B) \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A)+acceptance(B) then
                        (acceptance(A)+acceptance(B),event(B))\<^sub>\<F>\<^sub>\<L>
                    else (\<bullet>,event(B))\<^sub>\<F>\<^sub>\<L> ) "

instance by intro_classes
end

subsubsection \<open> Simplification rules \<close>

text \<open> Next we define simplification rules that aid in the manipulation of acceptances and
       aevents. \<close>

lemma event_in_acceptance [simp]:
  assumes "acceptance(A) \<noteq> \<bullet>"
  shows "event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance(A)"
  by (metis (mono_tags, lifting) Rep_aevent acceptance.rep_eq assms event.rep_eq mem_Collect_eq prod.collapse prod.simps(2))
  
lemma acceptance_set [simp]: 
  assumes "b \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>"
  shows "acceptance (A,b)\<^sub>\<F>\<^sub>\<L> = A"
  by (simp add: Abs_aevent_inverse acceptance.rep_eq assms)

lemma acceptance_event [simp]: "e \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet> \<Longrightarrow> event (A,e)\<^sub>\<F>\<^sub>\<L> = e"
  by (simp add: Abs_aevent_inverse event.rep_eq)

lemma acceptance_acceptance_pair [simp]: "acceptance (acceptance(a), event(a))\<^sub>\<F>\<^sub>\<L> = acceptance(a)"
  apply (auto simp add:acceptance_def Abs_aevent_inverse)
  by (simp add: Rep_aevent_inverse event.rep_eq)

lemma event_accepance_pair [simp]: "event (acceptance(a), event(a))\<^sub>\<F>\<^sub>\<L> = event(a)"
  apply (auto simp add:event_def Abs_aevent_inverse)
  by (simp add: Rep_aevent_inverse acceptance.rep_eq)

lemma acceptance_pair_eq:
  assumes "b \<in>\<^sub>\<F>\<^sub>\<L> a" "d \<in>\<^sub>\<F>\<^sub>\<L> c"
  shows "(a, b)\<^sub>\<F>\<^sub>\<L> = (c, d)\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> a = c \<and> b = d"
  using assms
  using acceptance_event acceptance_set by force

lemma unionA_sym [simp]: "A \<union>\<^sub>\<F>\<^sub>\<L> B = B \<union>\<^sub>\<F>\<^sub>\<L> A"
  by (cases A, auto, cases B, auto, cases B, auto)

lemma acceptance_of_aevent_aunion_acceptances_1 [simp]:
 "acceptance (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event A)\<^sub>\<F>\<^sub>\<L> = acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B"
 by (cases A, auto, cases B, auto, case_tac a, auto, case_tac aa, auto, case_tac a, auto)

lemma acceptance_of_aevent_aunion_acceptances_2 [simp]:
 "acceptance (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event B)\<^sub>\<F>\<^sub>\<L> = acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B"
  by (cases A, auto)

lemma prefix_aevent_acceptance_not_bullet:
  assumes "s \<le> (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> X,event A)\<^sub>\<F>\<^sub>\<L>"
          "acceptance(s) \<noteq> \<bullet>"
    shows "event(A) \<in>\<^sub>\<F>\<^sub>\<L> acceptance(s)"
  using assms 
  apply (simp add: less_eq_aevent_def)
  apply (cases A, auto, cases X, auto)
  apply (cases s, auto, case_tac a, auto)
  by (cases s, auto, case_tac a, auto)

lemma aevent_less_eq_iff_components:
  assumes "e \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>"
  shows "x \<le> (A,e)\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> x = (A,e)\<^sub>\<F>\<^sub>\<L> \<or> x = (\<bullet>,e)\<^sub>\<F>\<^sub>\<L>"
  using assms 
  apply (simp add: less_eq_aevent_def)
  apply auto
    apply (cases A, auto, cases x, auto, case_tac a, auto)
   apply presburger
  by (cases A, auto, cases x, auto, case_tac a, auto)

subsection \<open> Finite Linear Trace \<close>

text \<open> Finally we define the finite linear trace as a datatype. Observe that this is an instance
       of a terminated list whereby the final element is an acceptance. \<close>

datatype 'e fltrace = Acceptance "'e acceptance" ("\<langle>_\<rangle>\<^sub>\<F>\<^sub>\<L>") | AEvent "'e aevent" "'e fltrace" (infix "#\<^sub>\<F>\<^sub>\<L>" 65)

syntax
  "_rtrace"     :: "args \<Rightarrow> 'e \<Rightarrow> 'e fltrace"    ("\<langle>(_),(_)\<rangle>\<^sub>\<F>\<^sub>\<L>")

translations
  "\<langle>x,xs,y\<rangle>\<^sub>\<F>\<^sub>\<L>" == "(x#\<^sub>\<F>\<^sub>\<L>\<langle>xs,y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  "\<langle>x,y\<rangle>\<^sub>\<F>\<^sub>\<L>" == "x#\<^sub>\<F>\<^sub>\<L>\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"

lemma fl_cons_never_fixpoint [simp]: "\<not> aa = x #\<^sub>\<F>\<^sub>\<L> aa"
  by (induct aa, auto)

subsubsection \<open> Partial orders \<close>

text \<open> We can define the partial order on fltraces by using the order over acceptances
       in the following way. \<close>

instantiation fltrace :: (type) order
begin

fun less_eq_fltrace :: "'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where
"less_eq_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = (x \<le> y)" |
"less_eq_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> (y#\<^sub>\<F>\<^sub>\<L>ys) = (x \<le> acceptance y)" |
"less_eq_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) (y#\<^sub>\<F>\<^sub>\<L>ys) = (x \<le> y \<and> less_eq_fltrace xs ys)" |
"less_eq_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = False"

definition less_fltrace :: "'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where 
    "less_fltrace a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)"

lemma fltrace_refl:
  fixes x :: "'a fltrace"
  shows "x \<le> x"
  apply (induct x rule:fltrace.induct)
  by auto

lemma fltrace_trans:
  fixes x y z :: "'a fltrace"
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  apply (induct x z arbitrary:y rule:less_eq_fltrace.induct)
  apply (case_tac ya)
      apply auto
     apply (metis less_eq_fltrace.simps(2) less_eq_fltrace.simps(3) less_eq_aevent_def less_eq_fltrace.simps(1) order_trans fltrace.exhaust)
  by (metis less_eq_fltrace.simps(3) less_eq_fltrace.simps(4) order_trans fltrace.exhaust)+

lemma fltrace_antisym:
  fixes x y z :: "'a fltrace"
  shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
  apply (induct x y rule:less_eq_fltrace.induct)
  by auto

instance apply intro_classes
    apply (auto simp add:less_fltrace_def)
   apply (simp add: fltrace_refl)
  using fltrace_trans apply blast
  using fltrace_antisym by blast
end

fun strong_less_eq_fltrace :: "'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" (infix "\<le>\<^sub>\<F>\<^sub>\<L>" 50) where
"strong_less_eq_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = (x \<le> y)" |
"strong_less_eq_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> (y#\<^sub>\<F>\<^sub>\<L>ys) = (False)" |
"strong_less_eq_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) (y#\<^sub>\<F>\<^sub>\<L>ys) = (x \<le> y \<and> strong_less_eq_fltrace xs ys)" |
"strong_less_eq_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = False"

lemma strong_less_eq_fltrace_refl:
  fixes x :: "'a fltrace"
  shows "x \<le>\<^sub>\<F>\<^sub>\<L> x"
  apply (induct x rule:fltrace.induct)
  by auto

lemma strong_less_eq_fltrace_trans:
  fixes x y z :: "'a fltrace"
  shows "x \<le>\<^sub>\<F>\<^sub>\<L> y \<Longrightarrow> y \<le>\<^sub>\<F>\<^sub>\<L> z \<Longrightarrow> x \<le>\<^sub>\<F>\<^sub>\<L> z"
  apply (induct x z arbitrary:y rule:strong_less_eq_fltrace.induct)
     apply (case_tac ya, auto, case_tac x, auto, case_tac ya, auto, case_tac ya, auto)
  apply (metis (no_types, hide_lams) dual_order.trans fltrace.exhaust strong_less_eq_fltrace.simps(3) strong_less_eq_fltrace.simps(4))
  apply (metis (no_types, hide_lams) fltrace.exhaust  strong_less_eq_fltrace.simps(3) strong_less_eq_fltrace.simps(4))
  by (case_tac y, auto, case_tac ya, auto, case_tac ya, auto)

lemma strong_less_eq_fltrace_antisym:
  fixes x y z :: "'a fltrace"
  shows "x \<le>\<^sub>\<F>\<^sub>\<L> y \<Longrightarrow> y \<le>\<^sub>\<F>\<^sub>\<L> x \<Longrightarrow> x = y"
  apply (induct x y rule:strong_less_eq_fltrace.induct)
  by auto

lemma strongFL_imp_less_eq [simp]:
  assumes "x \<le>\<^sub>\<F>\<^sub>\<L> y"
  shows "x \<le> y"
  using assms by(induct x y rule:less_eq_fltrace.induct, auto)

subsubsection \<open> Operators \<close>

text \<open> Below we define a concatenation operator that is associative. Observe that,
       in the context of a trace algebra, this definition is not suitable to define
       a prefix relation that captures prefix closure for the FL-model. A consequence
       of this is that it is rather impractical to use it for induction rules.

       Note: I think it is possible to define the appropriate prefix closure relation
             by using the disjoint trace algebra. \<close>

fun fltrace_concat :: "'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> 'e fltrace" (infix "@\<^sub>\<F>\<^sub>\<L>" 65) where 
"fltrace_concat \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L>" | 
"fltrace_concat (A #\<^sub>\<F>\<^sub>\<L> fl) b = (A #\<^sub>\<F>\<^sub>\<L> fltrace_concat fl b)" |
"fltrace_concat \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> (B #\<^sub>\<F>\<^sub>\<L> fl) = (B #\<^sub>\<F>\<^sub>\<L> fl)"

lemma bullet_left_zero[simp]:
  "(\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> @\<^sub>\<F>\<^sub>\<L> z) = z"
  by (case_tac z, auto simp add:Rep_aevent_inverse acceptance.rep_eq event.rep_eq)

lemma fltrace_concat_assoc: "(s @\<^sub>\<F>\<^sub>\<L> t) @\<^sub>\<F>\<^sub>\<L> z = s @\<^sub>\<F>\<^sub>\<L> (t @\<^sub>\<F>\<^sub>\<L> z)"
  apply (induct s, auto)
  apply (induct t, auto)
  apply (case_tac x, auto)
   apply (case_tac xa, auto)
   apply (induct z, auto)
  apply (case_tac xa, auto)
  by (induct z, auto)

fun fltrace_concat2 :: "'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> 'e fltrace" (infix "&\<^sub>\<F>\<^sub>\<L>" 65) where 
"fltrace_concat2 \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>A+B\<rangle>\<^sub>\<F>\<^sub>\<L>" | 
"fltrace_concat2 (A #\<^sub>\<F>\<^sub>\<L> fl) b = (A #\<^sub>\<F>\<^sub>\<L> fltrace_concat2 fl b)" |
"fltrace_concat2 \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> (B #\<^sub>\<F>\<^sub>\<L> fl) = (B #\<^sub>\<F>\<^sub>\<L> fl)" |
"fltrace_concat2 \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> (B #\<^sub>\<F>\<^sub>\<L> fl) = \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"

lemma bullet_left_zero2[simp]:
  "(\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> z) = z"
  by (case_tac z, auto simp add:Rep_aevent_inverse acceptance.rep_eq event.rep_eq)

lemma bullet_right_zero2[simp]:
  "x &\<^sub>\<F>\<^sub>\<L> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = x"
  by (induct x, auto)
 
lemma fltrace_concat2_assoc: "(s &\<^sub>\<F>\<^sub>\<L> t) &\<^sub>\<F>\<^sub>\<L> z = s &\<^sub>\<F>\<^sub>\<L> (t &\<^sub>\<F>\<^sub>\<L> z)"
  apply (induct s, auto)
  apply (induct t, auto)
  apply (case_tac x, auto)
   apply (case_tac xa, auto)
   apply (induct z, auto)
   apply (case_tac x, auto)
  apply (case_tac x, auto)
  apply (induct z, auto)
  by (case_tac x, auto)

lemma x_le_x_concat2:
  "x \<le> x &\<^sub>\<F>\<^sub>\<L> y"
  apply (induct x, auto)
  apply (case_tac x, auto)
   apply (case_tac y, auto)
  apply (case_tac y, auto)
  by (case_tac x1, auto)

text \<open> Below we define auxiliary functions on FL traces using the concatenation
       operators we defined earlier. \<close>

primrec rev :: "'a fltrace \<Rightarrow> 'a fltrace" where
"rev \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"rev (x #\<^sub>\<F>\<^sub>\<L> xs) = rev xs @\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"

primrec rev2 :: "'a fltrace \<Rightarrow> 'a fltrace" where
"rev2 \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"rev2 (x #\<^sub>\<F>\<^sub>\<L> xs) = rev2 xs @\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"

primrec butlast :: "'a fltrace \<Rightarrow> 'a fltrace" where
"butlast \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"butlast (x #\<^sub>\<F>\<^sub>\<L> xs) = (x #\<^sub>\<F>\<^sub>\<L> butlast xs)"

primrec last :: "'a fltrace \<Rightarrow> 'a acceptance" where
"last \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> = x" |
"last (x #\<^sub>\<F>\<^sub>\<L> xs) = last xs"

primrec first :: "'a fltrace \<Rightarrow> 'a acceptance" where
"first \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> = x" |
"first (x #\<^sub>\<F>\<^sub>\<L> xs) = acceptance(x)"

lemma "rev \<langle>x,y\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  by (auto simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)

lemma "butlast \<langle>x,y\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  by auto

lemma rev2_little: "rev2((xs @\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = y #\<^sub>\<F>\<^sub>\<L> rev2(xs @\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  by (induct xs, auto simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)

lemma rev_little: "rev((xs @\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) @\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = y #\<^sub>\<F>\<^sub>\<L> rev(xs @\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  by (induct xs, auto simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)

lemma rev_little_cons: "rev(rev(x #\<^sub>\<F>\<^sub>\<L> xs)) = x #\<^sub>\<F>\<^sub>\<L> rev(rev(xs))"
  apply (induct xs, auto simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)
  by (simp add: rev_little)

lemma rev_rev_butlast: "rev(rev(x)) = butlast x"
  apply (induct x, auto)
  by (metis rev.simps(2) rev_little_cons)

lemma butlast_last_FL: "butlast x @\<^sub>\<F>\<^sub>\<L> \<langle>last x\<rangle>\<^sub>\<F>\<^sub>\<L> = x"
  by (induct x, auto)

lemma butlast_last_cons2_FL: "butlast x &\<^sub>\<F>\<^sub>\<L> \<langle>last x\<rangle>\<^sub>\<F>\<^sub>\<L> = x"
  by (induct x, auto)

lemma rev_rev_last: "rev(rev(x)) @\<^sub>\<F>\<^sub>\<L> \<langle>last x\<rangle>\<^sub>\<F>\<^sub>\<L>= x"
  by (simp add: butlast_last_FL rev_rev_butlast)

primrec rev3 :: "'a fltrace \<Rightarrow> 'a fltrace" where
"rev3 \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"rev3 (x #\<^sub>\<F>\<^sub>\<L> xs) = rev3 xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"

definition rev4 :: "'a fltrace \<Rightarrow> 'a fltrace" where
"rev4 xs = rev3(xs) &\<^sub>\<F>\<^sub>\<L> \<langle>last xs\<rangle>\<^sub>\<F>\<^sub>\<L>"

lemma last_fltrace_acceptance: "last (\<langle>y,z\<rangle>\<^sub>\<F>\<^sub>\<L>) = z"
  by auto

lemma last_cons_fltrace_acceptance: "last (\<langle>ys,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<langle>y,z\<rangle>\<^sub>\<F>\<^sub>\<L>) = z"
  by auto

lemma last_dist_plus: "last(xs &\<^sub>\<F>\<^sub>\<L> ys) = last xs + last ys"
  apply (induct xs, auto)
  apply (induct ys, auto)
  apply (case_tac x, auto)
  by (metis acceptance.simps(3) plus_acceptance.elims)

lemma last_rev3_is_bullet: "last(rev3 xs) = \<bullet>"
  apply (induct xs, auto)
  by (auto simp add:last_dist_plus)

lemma last_rev3_acceptance: "last(rev3 xs &\<^sub>\<F>\<^sub>\<L> \<langle>z\<rangle>\<^sub>\<F>\<^sub>\<L>) = z"
  apply (auto simp add:last_dist_plus)
  by (simp add:last_rev3_is_bullet)

lemma last_rev3_cons2_is_last_cons: "last(rev3 xs &\<^sub>\<F>\<^sub>\<L> ys) = last ys"
  apply (auto simp add:last_dist_plus)
  by (simp add:last_rev3_is_bullet)

lemma "rev3 \<langle>x,y\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  by (auto simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)

lemma "rev4 \<langle>x,y\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>x,y\<rangle>\<^sub>\<F>\<^sub>\<L>"
  unfolding rev4_def by (auto simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)

lemma fltrace_cons2_last: "\<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>x1a,last(xs)\<rangle>\<^sub>\<F>\<^sub>\<L>"
  by (induct xs, auto)

lemma rev3_little: "rev3(\<langle>xs,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = y #\<^sub>\<F>\<^sub>\<L> rev3(\<langle>xs,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  by (induct xs, auto)

lemma rev3_little_bullet: "rev3(\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = y #\<^sub>\<F>\<^sub>\<L> rev3(\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  by auto

lemma rev3_little_more: 
  assumes "last(zs) = \<bullet>"
  shows "rev3(zs &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = y #\<^sub>\<F>\<^sub>\<L> rev3(zs)"
  using assms
  apply (induct zs)
  by auto

lemma rev3_little_more_extra: 
  assumes "last(zs) = \<bullet>"
  shows "rev3(zs &\<^sub>\<F>\<^sub>\<L> \<langle>y,z\<rangle>\<^sub>\<F>\<^sub>\<L>) = y #\<^sub>\<F>\<^sub>\<L> rev3(zs)"
  using assms
  apply (induct zs)
  by auto

lemma rev3_little_complete: "rev3(rev3 xs &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = y #\<^sub>\<F>\<^sub>\<L> rev3(rev3(xs))"
  by (simp add: last_rev3_is_bullet rev3_little_more)  

lemma rev3_little_complete_extensive: "rev3(rev3 xs &\<^sub>\<F>\<^sub>\<L> \<langle>y,z\<rangle>\<^sub>\<F>\<^sub>\<L>) = y #\<^sub>\<F>\<^sub>\<L> (rev3(rev3(xs)))"
  by (simp add: last_rev3_is_bullet rev3_little_more_extra)

lemma rev_little_cons2: "rev3(rev3(x #\<^sub>\<F>\<^sub>\<L> xs)) = x #\<^sub>\<F>\<^sub>\<L> rev3(rev3(xs))"
  apply (induct xs, auto simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)
  by (simp add: last_rev3_cons2_is_last_cons rev3_little_more)

lemma FL_concat_equiv: "x1a #\<^sub>\<F>\<^sub>\<L> xs = \<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> xs"
  by auto

lemma last_butlast_cons_bullet: "last(butlast x &\<^sub>\<F>\<^sub>\<L> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = \<bullet>"
  by (induct x, auto)

lemma rev3_cons2_little:
   "rev3(xs &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,z\<rangle>\<^sub>\<F>\<^sub>\<L>) = rev3(xs &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  apply (induct xs, auto)
  by (case_tac x, auto)

lemma rev3_rev3_const2_last: "rev3(rev3(xs)) &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L> = xs"
  apply (induct xs, auto)
  by (simp add: rev3_little_complete)

lemma rev4_rev4: "rev4(rev4(xs)) = xs"
(* No need for induction at all!
  unfolding rev4_def apply (case_tac xs, auto)
  sledgehammer[debug=true] *)
proof (induct xs)
  case (Acceptance x)
  then show ?case unfolding rev4_def by auto
next
  case (AEvent x1a xs)
  have "rev4 (rev4 (x1a #\<^sub>\<F>\<^sub>\<L> xs)) = (rev4(rev3(x1a #\<^sub>\<F>\<^sub>\<L> xs) &\<^sub>\<F>\<^sub>\<L> \<langle>last (x1a #\<^sub>\<F>\<^sub>\<L> xs)\<rangle>\<^sub>\<F>\<^sub>\<L>))"
    unfolding rev4_def by auto
  also have "... = (rev4(rev3(x1a #\<^sub>\<F>\<^sub>\<L> xs) &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>))"
    by auto
  also have "... = (rev4((rev3 xs &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>))"
    by auto
  also have "... = (rev4(rev3 xs &\<^sub>\<F>\<^sub>\<L> (\<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>)))"
    by (auto simp add:fltrace_concat2_assoc)
  also have "... = (rev3(rev3 xs &\<^sub>\<F>\<^sub>\<L> (\<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>)) 
                    &\<^sub>\<F>\<^sub>\<L> \<langle>last (rev3 xs &\<^sub>\<F>\<^sub>\<L> (\<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>))\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    unfolding rev4_def by auto
  also have "... = (rev3(rev3 xs &\<^sub>\<F>\<^sub>\<L> (\<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>)) &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    by (auto simp add:last_rev3_cons2_is_last_cons)
  also have "... = (rev3(rev3 xs &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>) &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    by auto
  also have "... = (rev3(rev3 xs &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    using rev3_cons2_little
    by metis
  also have "... = (x1a #\<^sub>\<F>\<^sub>\<L> rev3(rev3(xs))) &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (simp add: rev3_little_complete)
  also have "... = x1a #\<^sub>\<F>\<^sub>\<L> (rev3(rev3(xs)) &\<^sub>\<F>\<^sub>\<L> \<langle>last (xs)\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    by simp
  also have "... = x1a #\<^sub>\<F>\<^sub>\<L> xs"
    by (auto simp add:rev3_rev3_const2_last)

  then show ?case using AEvent
    by (simp add: calculation)
qed

primrec length :: "'a fltrace \<Rightarrow> nat" where
"length \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> = 0" |
"length (x #\<^sub>\<F>\<^sub>\<L> xs) = 1 + (length xs)"

lemma last_bullet_butlast:
  assumes "last xs = \<bullet>"
  shows "butlast(xs &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,last x\<rangle>\<^sub>\<F>\<^sub>\<L>) = xs &\<^sub>\<F>\<^sub>\<L> \<langle>x1a,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms by(induct xs, auto)

lemma last_bullet_butlast_last:
  assumes "last xs = \<bullet>"
  shows "butlast(xs &\<^sub>\<F>\<^sub>\<L> \<langle>last x\<rangle>\<^sub>\<F>\<^sub>\<L>) = xs"
  using assms by(induct xs, auto)

lemma length_cons:
  assumes "last xs = \<bullet>"
  shows "length(xs &\<^sub>\<F>\<^sub>\<L> ys) = length(xs) + length(ys)"
  using assms by (induct xs, auto)

lemma last_not_bullet_then_last_cons [simp]:
  assumes "last(xs) \<noteq> \<bullet>"
  shows "last (xs &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = last (xs)"
  using assms apply (induct xs, auto)
  by (case_tac x, auto, case_tac y, auto)

lemma last_bullet_then_last_cons [simp]:
  assumes "last(xs) = \<bullet>"
  shows "last (xs &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) = last (\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms by (induct xs, auto)

lemma last_bullet_concatmix:
  assumes "last xs = \<bullet>"
  shows "(xs &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>) @\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = (xs &\<^sub>\<F>\<^sub>\<L> (\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> @\<^sub>\<F>\<^sub>\<L> \<langle>z,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
  using assms by (induct xs, auto)

lemma xs_less_eq_z_two_only:
  assumes "xs &\<^sub>\<F>\<^sub>\<L> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> z" "z \<le> xs &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "z = xs &\<^sub>\<F>\<^sub>\<L> \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> z = xs &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,tock)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms 
  apply (auto)
  apply (induct xs z rule:less_eq_fltrace.induct, auto)  
  apply (metis acceptance_set fltrace_concat2.simps(3) less_eq_acceptance.elims(2) less_eq_fltrace.simps(2))
  apply (case_tac x, auto)
   apply (simp add: eq_iff less_eq_aevent_def)
  by (case_tac ys, auto, case_tac x1, auto)

section \<open> Finite Linear Traces \<close>

lemma last_cons_acceptance_not_bullet[simp]:
  "last (ys &\<^sub>\<F>\<^sub>\<L> \<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<noteq> \<bullet>"
  apply (induct ys, auto)
  by (case_tac x, auto)

lemma last_cons_bullet_iff:
  "last (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = \<bullet> \<longleftrightarrow> last(xs) = \<bullet>"
  apply (induct xs, auto)
  by (case_tac xa, auto)

lemma fl_cons_acceptance_consFL:
  "fl @\<^sub>\<F>\<^sub>\<L> \<langle>e,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = butlast fl &\<^sub>\<F>\<^sub>\<L> \<langle>e,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  by (induct fl, auto)

lemma strong_less_eq_fltrace_cons_imp_lhs:
  assumes "(xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>\<F>\<^sub>\<L> t"
  shows "xs \<le>\<^sub>\<F>\<^sub>\<L> t"
  using assms apply (induct xs t rule:strong_less_eq_fltrace.induct, auto)
  apply (cases x, auto)
  by (case_tac xa, auto)

lemma strong_less_eq_fltrace_eq_length:
  assumes "s \<le>\<^sub>\<F>\<^sub>\<L> t"
  shows "length s = length t"
  using assms 
  by (induct s t rule:strong_less_eq_fltrace.induct, auto)

lemma strong_less_eq_fltrace_cons_last_less_eq:
  assumes "last xs = \<bullet>" "last ys = \<bullet>"
          "(xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>\<F>\<^sub>\<L> (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    shows "x \<le> y"
  using assms apply(induct xs ys rule:strong_less_eq_fltrace.induct, auto)
  apply (metis fltrace.distinct(1) rev3.simps(1) rev3_little_more strong_less_eq_fltrace.elims(2))
  by (metis fltrace.distinct(1) rev3.simps(1) rev3_little_more strong_less_eq_fltrace.elims(2))

lemma strong_less_eq_fltrace_cons_iff_lhs_bullet:
  assumes "x \<le> y"
  shows "(xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> xs = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply (induct xs, auto)
   apply (case_tac xa, auto)
  apply (case_tac xs, auto)
  by (case_tac x1, auto)

lemma concat_FL_last_not_bullet_absorb:
  assumes "last xs \<noteq> \<bullet>"
  shows "xs &\<^sub>\<F>\<^sub>\<L> ys = xs"
  using assms
  by (metis Finite_Linear_Model.last.simps(1)  butlast_last_cons2_FL fltrace_concat2.simps(2) fltrace_concat2.simps(4) fltrace_concat2_assoc plus_acceptance.elims)

lemma strong_less_eq_fltrace_last_cons_bullet_imp_le:
  assumes "(xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) \<le>\<^sub>\<F>\<^sub>\<L> (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "last (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) = \<bullet>"
  shows "x \<le> y"
  using assms apply(induct xs ys rule:strong_less_eq_fltrace.induct, auto)
  apply (metis Finite_Linear_Model.last.simps(1) concat_FL_last_not_bullet_absorb fltrace_concat2.simps(3)  strong_less_eq_fltrace.simps(2) strong_less_eq_fltrace.simps(3))
  apply (metis (no_types, lifting) FL_concat_equiv  concat_FL_last_not_bullet_absorb fltrace_concat2_assoc last_cons_bullet_iff last_rev3_cons2_is_last_cons rev3.simps(1) rev_little_cons2 strong_less_eq_fltrace.simps(2) strong_less_eq_fltrace_cons_last_less_eq)
  by (metis (no_types, lifting) Finite_Linear_Model.last.simps(1) antisym_conv fltrace.distinct(1) fltrace.inject(2) fltrace_concat2.simps(3) last_cons_bullet_iff rev3.simps(1) rev3_little_more rev3_rev3_const2_last strong_less_eq_fltrace.elims(2) strongFL_imp_less_eq x_le_x_concat2)

text \<open> The set of finite linear traces is fltraces. \<close>

type_synonym 'e fltraces = "('e fltrace) set"

subsection \<open> Healthiness Conditions \<close>

subsubsection \<open> FL0 \<close>

text \<open> The set of fltraces is non-empty. \<close>

definition FL0 :: "'a fltraces \<Rightarrow> bool" where
"FL0 P \<equiv> P \<noteq> {}"

subsubsection \<open> FL1 \<close>

text \<open> The set of fltraces is prefix-closed according to the order over {@type fltrace}. \<close>

definition FL1 :: "'a fltraces \<Rightarrow> bool" where
"FL1 P \<equiv> \<forall>s t. (t \<in> P \<and> s \<le> t) \<longrightarrow> s \<in> P"

definition mkFL1 :: "'a fltraces \<Rightarrow> 'a fltraces" where
"mkFL1 P \<equiv> P \<union> {s. \<exists>z. z \<in> P \<and> s \<le> z}"

lemma mkFL1_disj_univ: "mkFL1 (\<Union> P) = \<Union> ({mkFL1(x)|x. x \<in> P})"
  unfolding mkFL1_def by auto

lemma FL1_fixpoint: "FL1 P \<longleftrightarrow> mkFL1 P = P"
  unfolding FL1_def mkFL1_def by auto

subsubsection \<open> FL2 \<close>

text \<open> If an event a is offered in an acceptance A after a trace \<B> then it is also possible
       to find a pair (A,a) after \<B> also in P. \<close>

definition FL2 :: "'a fltraces \<Rightarrow> bool" where
"FL2 P \<equiv> \<forall>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"



(*{t. \<exists>A B \<alpha> \<B>. (t = (\<langle>A \<union>\<^sub>\<F>\<^sub>\<L> B\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<alpha>) \<or> t = (\<langle>A \<union>\<^sub>\<F>\<^sub>\<L> B\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<B>)) \<and> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<alpha> \<in> P \<and> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> &\<^sub>\<F>\<^sub>\<L> \<B> \<in> Q}" *)

lemma FL0_FL1_bullet_in [simp]:
  assumes "FL0 A" "FL1 A"
  shows "\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> A"
  using assms unfolding FL0_def FL1_def apply simp
  by (metis all_not_in_conv fltrace.exhaust less_eq_acceptance.simps(1) less_eq_fltrace.simps(1) less_eq_fltrace.simps(2))

lemma FL0_FL1_bullet_in_so [simp]:
  assumes "FL1 P" "x \<in> P"
  shows "\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
  using FL0_FL1_bullet_in FL0_def assms(1) assms(2) by blast

lemma FL_cons_acceptance:
  assumes "FL1 A" "Aa #\<^sub>\<F>\<^sub>\<L> fl \<in> A"
  shows "\<langle>acceptance(Aa)\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> A"
  using assms unfolding FL1_def apply auto
  by (meson dual_order.refl less_eq_fltrace.simps(2))

lemma x_le_concat2_FL1 [simp]:
  assumes "x &\<^sub>\<F>\<^sub>\<L> y \<in> P" "FL1 P"
  shows "x \<in> P"
  using assms x_le_x_concat2 
  using FL1_def by blast

(*
lemma ExtChoiceH_emptyset:
  assumes "ExtChoiceH \<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> B x" "B \<in> P"
  shows "x \<in> P"
  using assms by (cases B, auto, case_tac x1, auto)
*)

lemma bullet_event_acceptance [simp]:
  "(\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> \<le> A"
  apply (cases A, auto, case_tac a, auto)
  by (simp add: less_eq_aevent_def)

lemma
  assumes "b \<in>\<^sub>\<F>\<^sub>\<L> [x2]\<^sub>\<F>\<^sub>\<L>"
  shows "\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> \<langle>([x2]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms by auto

lemma aevent_less_eq_FL1:
  assumes "([x2]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> x22 \<in> P" "FL1 P" "b \<in>\<^sub>\<F>\<^sub>\<L> [x2]\<^sub>\<F>\<^sub>\<L>"
  shows "\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
  using assms
  apply (induct x22, auto, case_tac x, auto)
  using FL_cons_acceptance by fastforce+

lemma fltrace_acceptance_FL1:
  assumes "A #\<^sub>\<F>\<^sub>\<L> xs \<in> P" "FL1 P" 
  shows "\<langle>A,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P"
  using assms by (induct xs, auto)

lemma fltrace_acceptance_FL1_less_eq:
  assumes "A #\<^sub>\<F>\<^sub>\<L> xs \<in> P" "FL1 P" 
          "x \<le> A"
    shows "x #\<^sub>\<F>\<^sub>\<L> xs \<in> P"
  using assms
  apply (cases A, auto, cases x, auto)
  by (meson FL1_def eq_iff less_eq_fltrace.simps(3))+

lemma acceptance_bullet_event_FL1:
  assumes "A #\<^sub>\<F>\<^sub>\<L> xs \<in> P" "FL1 P"
  shows "(\<bullet>,event A)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> xs \<in> P"
  using assms 
  apply (cases A, auto)
  by (metis acceptance_event bullet_event_acceptance fltrace_acceptance_FL1_less_eq)

subsection \<open> Refinement \<close>

abbreviation Refines :: "'e fltraces \<Rightarrow> 'e fltraces \<Rightarrow> bool" (infixl "\<sqsubseteq>\<^sub>\<F>\<^sub>\<L>" 65) where
"P \<sqsubseteq>\<^sub>\<F>\<^sub>\<L> Q \<equiv> Q \<subseteq> P"

end
