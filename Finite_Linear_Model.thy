theory Finite_Linear_Model

imports
  Main
  Event_Priority
begin

text \<open> This theory is an encoding of the Finite Linear model, the finest finite CSP denotational 
       model in the CSP hierarchy. For processes that observe the healthiness condition FL1 of 
       this model we have that such processes are congruent to the operational semantics of CSP 
       under weak bisimulation (not proved here).

       FL1 ensures that it is not possible to know whether an event definitely takes place from
       a stable state, only that it may. Instability is always a possibility, and indeed Div is
       maximal in the refinement order, whereby only instability is observed. \<close>

section \<open> Model \<close>

subsection \<open> Acceptances \<close>

text \<open> An acceptance is either \<bullet> or a set. \<close>

datatype 'e acceptance = acnil ("\<bullet>") | acset "'e set" ("[_]\<^sub>\<F>\<^sub>\<L>")

text \<open> Here we define an order on acceptances, whereby \<bullet> is related to
       any element, and otherwise sets need to be equal to be related. \<close>

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

instantiation acceptance :: (type) plus
begin

fun plus_acceptance :: "'a acceptance \<Rightarrow> 'a acceptance \<Rightarrow> 'a acceptance"  where
  "plus_acceptance \<bullet> R = R" |
  "plus_acceptance S \<bullet> = S" |
  "plus_acceptance [S]\<^sub>\<F>\<^sub>\<L> [R]\<^sub>\<F>\<^sub>\<L> = [S]\<^sub>\<F>\<^sub>\<L>"

instance
  by intro_classes
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

subsection \<open> Finite Linear Trace \<close>

text \<open> Finally we define the finite linear trace as a datatype. Observe that this is an instance
       of a terminated list whereby the final element is an acceptance. \<close>

datatype 'e fltrace = Acceptance "'e acceptance" ("\<langle>_\<rangle>\<^sub>\<F>\<^sub>\<L>") | AEvent "'e aevent" "'e fltrace" (infix "#\<^sub>\<F>\<^sub>\<L>" 65)

syntax
  "_rtrace"     :: "args \<Rightarrow> 'e \<Rightarrow> 'e fltrace"    ("\<langle>(_),(_)\<rangle>\<^sub>\<F>\<^sub>\<L>")

translations
  "\<langle>x,xs,y\<rangle>\<^sub>\<F>\<^sub>\<L>" == "(x#\<^sub>\<F>\<^sub>\<L>\<langle>xs,y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  "\<langle>x,y\<rangle>\<^sub>\<F>\<^sub>\<L>" == "x#\<^sub>\<F>\<^sub>\<L>\<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>"


fun strict_less_eq_fltrace :: "'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where
"strict_less_eq_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = (x = y)" |
"strict_less_eq_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> (y#\<^sub>\<F>\<^sub>\<L>ys) = (x = acceptance y)" |
"strict_less_eq_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) (y#\<^sub>\<F>\<^sub>\<L>ys) = (x = y \<and> strict_less_eq_fltrace xs ys)" |
"strict_less_eq_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = False"

subsubsection \<open> Partial order \<close>

text \<open> We can define the partial order on fltraces by defining the order over acceptances
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

instantiation fltrace :: (type) plus
begin

fun plus_fltrace :: "'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> 'e fltrace" where
"plus_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = \<langle>x+y\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"plus_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> (y#\<^sub>\<F>\<^sub>\<L>ys) = (
        if event(y) \<in>\<^sub>\<F>\<^sub>\<L> x+acceptance(y) \<or> x+acceptance(y) = \<bullet> then 
          (x+acceptance(y),event(y))\<^sub>\<F>\<^sub>\<L>#\<^sub>\<F>\<^sub>\<L> ys
        else \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>)" |
"plus_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) (y#\<^sub>\<F>\<^sub>\<L>ys) = (x+y)#\<^sub>\<F>\<^sub>\<L>(plus_fltrace xs ys)" |
"plus_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = (
        if event(x) \<in>\<^sub>\<F>\<^sub>\<L> acceptance(x)+y \<or> acceptance(x)+y = \<bullet> then
           (acceptance(x)+y,event(x))\<^sub>\<F>\<^sub>\<L>#\<^sub>\<F>\<^sub>\<L>xs
        else
            (x#\<^sub>\<F>\<^sub>\<L>xs))"

instance by intro_classes
end

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

fun weak_less_eq_fltrace :: "'a fltrace \<Rightarrow> 'a fltrace \<Rightarrow> bool" where
"weak_less_eq_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = (x \<le> y)" |
"weak_less_eq_fltrace \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> (y#\<^sub>\<F>\<^sub>\<L>ys) = False" |
"weak_less_eq_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) (y#\<^sub>\<F>\<^sub>\<L>ys) = (x \<le> y \<and> weak_less_eq_fltrace xs ys)" |
"weak_less_eq_fltrace (x#\<^sub>\<F>\<^sub>\<L>xs) \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L> = False"

lemma weak_less_eq_fltrace_is_less_eq:
  assumes "weak_less_eq_fltrace x y"
  shows "x \<le> y"
  using assms by(induct x y rule:less_eq_fltrace.induct, auto)

lemma acceptance_right_zero[simp]:
  fixes a :: "'a acceptance"
  shows "a + \<bullet> = a"
  by (induct a, auto)

lemma acceptance_left_zero[simp]:
  fixes a :: "'a acceptance"
  shows "\<bullet> + a = a"
  by (induct a, auto)

lemma fltrace_add_idem [simp]:
  fixes a :: "'a fltrace"
  shows "a + a = a"
  apply (induct a, auto)
   apply (case_tac x, auto)
  apply (case_tac x1a, auto)
   apply (case_tac aa, auto)
  by (simp_all add: plus_aevent_def)
  
lemma fltrace_left_zero [simp]:
  fixes a :: "'a fltrace"
  shows "\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> + a = a"
  apply (induct a, auto)
   apply (simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)
  by (metis Rep_aevent_inverse acceptance.rep_eq event.rep_eq prod.collapse)

(*
lemma fltrace_right_zero [simp]:
  fixes a :: "'a fltrace"
  shows "a + \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> = a"
  apply (induct a, auto)
  apply (case_tac a, auto)
  by (simp_all add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)

lemma
  fixes a b c :: "'a fltrace"
  shows "(a + b) + c = a + (b + c)"
  nitpick
  apply (induct c)
    apply (case_tac x, auto)
  apply (case_tac b, auto)
   apply (case_tac x1, auto)
  apply (case_tac a, auto)
     apply (simp add: add.assoc)
    apply (case_tac x21)
  apply(auto)
     apply (case_tac aa, auto)
     apply (simp add: inf_sup_aci(6))
  sledgehammer[debug=true]
     apply (case_tac aa, auto)
  
proof -
  fix x1 :: "'a acceptance" and x21 :: "'a aevent" and x22 :: "'a fltrace"
  have "\<forall>a. (a::'a acceptance) + \<bullet> = a \<or> a = \<bullet>"
    by (metis (full_types) dual_order.refl less_eq_acceptance.elims(2) plus_acceptance.simps(2))
  moreover
  { assume "(\<bullet>, snd (Rep_aevent x21)) \<noteq> Rep_aevent x21"
    then have "fst (Rep_aevent x21) \<noteq> \<bullet>"
      by (metis (full_types) prod.exhaust_sel) }
  ultimately show "(acceptance (acceptance x21 + x1,event x21)\<^sub>\<F>\<^sub>\<L> + \<bullet>,event (acceptance x21 + x1,event x21)\<^sub>\<F>\<^sub>\<L>)\<^sub>\<F>\<^sub>\<L> = (acceptance x21 + (x1 + \<bullet>),event x21)\<^sub>\<F>\<^sub>\<L>"
    by (metis Rep_aevent_inverse acceptance.rep_eq event.rep_eq plus_acceptance.simps(1) prod.exhaust_sel)
next
  show ?thesis
  apply (auto)
  apply (metis Rep_aevent_inverse acceptance.rep_eq dual_order.refl event.rep_eq less_eq_acceptance.elims(2) plus_acceptance.simps(1) plus_acceptance.simps(2) prod.exhaust_sel)
  apply (smt Rep_aevent_inverse acceptance.rep_eq event.rep_eq plus_acceptance.elims prod.collapse)
  apply (induct a)
  apply (case_tac b, auto)
    apply (case_tac c, auto)
     apply (metis acceptance.simps(3) plus_acceptance.elims)
    apply (case_tac x, auto)
  apply (case_tac x1, auto)
     apply (simp add: Rep_aevent_inverse acceptance.rep_eq event.rep_eq)  
    apply (case_tac x1, auto)
    apply (case_tac x21, auto)
  apply (case_tac a, auto)
  sledgehammer[debug=true]
*)

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

(*
perhaps conditionally...
lemma "x &\<^sub>\<F>\<^sub>\<L> y = z &\<^sub>\<F>\<^sub>\<L> y \<Longrightarrow> x = z"
  nitpick
*)

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

datatype 'a fltracel = FAcc "'a acceptance" | FAEvent "'a aevent"

primrec fltrace2list :: "'a fltrace \<Rightarrow> 'a fltracel list" where
"fltrace2list (A #\<^sub>\<F>\<^sub>\<L> fl) = [FAEvent A] @ fltrace2list fl" |
"fltrace2list \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> = [FAcc A]"

fun list2fltrace :: "'a fltracel list \<Rightarrow> 'a fltrace" where
"list2fltrace [] = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"list2fltrace (FAEvent A # xs) = A #\<^sub>\<F>\<^sub>\<L> list2fltrace xs" |
"list2fltrace (FAcc A # xs) = \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"

lemma list2fltrace_fltrace2list: "list2fltrace(fltrace2list(xs)) = xs"
  by (induct xs, auto)

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

primrec length :: "'a fltrace \<Rightarrow> nat" where
"length \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> = 0" |
"length (x #\<^sub>\<F>\<^sub>\<L> xs) = 1 + (length xs)"

primrec kind :: "'a acceptance \<Rightarrow> bool" where
"kind \<bullet> = False" |
"kind [x]\<^sub>\<F>\<^sub>\<L> = True"
           
thm list_induct2

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

(*
lemma ftrace_cons_induct_both_kind:
  assumes "length x = length y" "kind (last x) = kind (last y)"
  shows "\<lbrakk>(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>);
          (\<And>x x1a y y1a. P x y 
              \<Longrightarrow> length x = length y 
              \<Longrightarrow> kind (last x) = kind (last y)
              \<Longrightarrow> P (x1a #\<^sub>\<F>\<^sub>\<L> x) (y1a #\<^sub>\<F>\<^sub>\<L> y))\<rbrakk> \<Longrightarrow> P x y"
  using assms proof (induct x arbitrary: y)
case (Acceptance x)
then show ?case 
next
  case (AEvent x1a x)
  then show ?case sorry
qed
*)

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

lemma length_rev3_eq:
  assumes "length x = length y"
  shows "length (rev3 x) = length (rev3 y)"
  using assms apply(induct x y rule:ftrace_cons_induct_both, auto)
  by (simp add: last_rev3_is_bullet length_cons)

lemma ftrace_cons_induct_both_butlast_rev4:
  assumes "length x = length y"
          "(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
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
      using eq_length by blast
    then show ?case
      using calculation by blast
qed

lemma ftrace_cons_induct_both_butlast:
  assumes "length x = length y"
          "(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
    shows "P (butlast(x)) (butlast(y))"
proof -
  have "P (butlast(x)) (butlast(y))
        =
        P (butlast(rev4(rev4(x)))) (butlast(rev4(rev4(y))))"
    by (auto simp add:rev4_rev4)
  then show ?thesis
    by (metis (no_types, lifting) assms(1) assms(2) assms(3) ftrace_cons_induct_both_butlast_rev4 last_rev3_is_bullet length.simps(1) length_cons length_rev3_eq rev4_def)
qed

lemma ftrace_cons_induct_both_butlast_eq_length:
  assumes "length x = length y"
          "(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          "P (butlast(x)) (butlast(y))"
        shows "P x y"
  by (metis assms(1) assms(3) assms(5) bullet_right_zero2 butlast_last_cons2_FL last_butlast_cons_bullet length.simps(1) length_cons)

lemma ftrace_cons_induct_both_eq_length:
  assumes "length x = length y"
          "(\<And>x y. P \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>)"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y\<rangle>\<^sub>\<F>\<^sub>\<L>))"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> length xs = length ys \<Longrightarrow> P (xs &\<^sub>\<F>\<^sub>\<L> \<langle>x,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>) (ys &\<^sub>\<F>\<^sub>\<L> \<langle>y,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))"
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

section \<open> Finite Linear Traces \<close>

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

subsection \<open> Operators \<close>

definition Div :: "'e fltraces" where
"Div = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

definition Stop :: "'e fltraces" where
"Stop = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>} \<union> {\<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

definition prefixH :: "'e \<Rightarrow> 'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> bool" where
"prefixH a aa X = (X = \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa \<or> X = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)"

definition Prefix :: "'e \<Rightarrow> 'e fltraces \<Rightarrow> 'e fltraces" (infixl "\<rightarrow>\<^sub>\<F>\<^sub>\<L>" 65) where
"a \<rightarrow>\<^sub>\<F>\<^sub>\<L> P = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>} \<union> {\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>} \<union> {([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>#\<^sub>\<F>\<^sub>\<L>\<rho>| \<rho>. \<rho> \<in> P} \<union> {(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>#\<^sub>\<F>\<^sub>\<L>\<rho>| \<rho>. \<rho> \<in> P}"

definition PrefixAlt :: "'e \<Rightarrow> 'e fltraces \<Rightarrow> 'e fltraces" where
"PrefixAlt a P = {x|s x. prefixH a s x \<and> s\<in>P}"

(*
lemma eq_acceptances [simp]:
  "([{aa}]\<^sub>\<F>\<^sub>\<L>,aa)\<^sub>\<F>\<^sub>\<L> = ([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> a = aa"
  apply auto
  by (simp add: acceptance_pair_eq)

lemma unequal_acceptances [simp]:
  "([{aa}]\<^sub>\<F>\<^sub>\<L>,aa)\<^sub>\<F>\<^sub>\<L> \<noteq> (\<bullet>,a)\<^sub>\<F>\<^sub>\<L>"
  apply auto
  by (metis acceptance.distinct(1) acceptance_set amember.simps(2) singletonI)

lemma unequal_acceptances_2 [simp]:
  "(\<bullet>,a)\<^sub>\<F>\<^sub>\<L> \<noteq> ([{aa}]\<^sub>\<F>\<^sub>\<L>,aa)\<^sub>\<F>\<^sub>\<L>"
  apply auto
  by (metis acceptance.distinct(1) acceptance_set amember.simps(2) singletonI)

lemma eq_acceptances_bullet [simp]:
  "(\<bullet>,aa)\<^sub>\<F>\<^sub>\<L> = (\<bullet>,a)\<^sub>\<F>\<^sub>\<L> \<longleftrightarrow> aa = a"
  apply auto
  by (metis acceptance_event)*)

lemma Prefix_PrefixAlt_eq:
  assumes "FL0 P" "FL1 P"
  shows "Prefix a P = PrefixAlt a P"
  using assms unfolding Prefix_def PrefixAlt_def prefixH_def apply auto
  using FL0_def apply fastforce
  using FL0_def by fastforce

definition IntChoice :: "'e fltraces \<Rightarrow> 'e fltraces \<Rightarrow> 'e fltraces" (infixl "\<sqinter>\<^sub>\<F>\<^sub>\<L>" 65) where
"P \<sqinter>\<^sub>\<F>\<^sub>\<L> Q \<equiv> P \<union> Q"

fun ExtChoiceH :: "'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> bool" where
"ExtChoiceH \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L> X = (X = \<langle>A \<union>\<^sub>\<F>\<^sub>\<L> B\<rangle>\<^sub>\<F>\<^sub>\<L>)" |
"ExtChoiceH (A #\<^sub>\<F>\<^sub>\<L> aa) (B #\<^sub>\<F>\<^sub>\<L> bb) X = 
  (X = ((acceptance(A) \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B),event(A))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa)
   \<or> 
   X = ((acceptance(A) \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B),event(B))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb))" |
"ExtChoiceH \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> (B #\<^sub>\<F>\<^sub>\<L> bb) X = 
  (X = \<langle>A \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B)\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = ((A \<union>\<^sub>\<F>\<^sub>\<L> acceptance(B),event(B))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> bb))" |
"ExtChoiceH (A #\<^sub>\<F>\<^sub>\<L> aa) \<langle>B\<rangle>\<^sub>\<F>\<^sub>\<L> X = 
  (X = \<langle>acceptance(A) \<union>\<^sub>\<F>\<^sub>\<L> B\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> X = ((acceptance(A) \<union>\<^sub>\<F>\<^sub>\<L> B,event(A))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> aa))"

definition ExtChoice :: "'e fltraces \<Rightarrow> 'e fltraces \<Rightarrow> 'e fltraces" (infixl "\<box>\<^sub>\<F>\<^sub>\<L>" 65) where
"P \<box>\<^sub>\<F>\<^sub>\<L> Q = {X| X A B. ExtChoiceH A B X \<and> A \<in> P \<and> B \<in> Q}"

fun HideAcceptance :: "'e acceptance \<Rightarrow> 'e set \<Rightarrow> 'e acceptance" where
"HideAcceptance \<bullet> X = \<bullet>" |
"HideAcceptance [A]\<^sub>\<F>\<^sub>\<L> X = (if A \<inter> X = {} then [A]\<^sub>\<F>\<^sub>\<L> else \<bullet>)"

fun HideFL :: "'e fltrace \<Rightarrow> 'e set \<Rightarrow> 'e fltrace" where
"HideFL \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> X = \<langle>HideAcceptance A X\<rangle>\<^sub>\<F>\<^sub>\<L>" |
"HideFL (A #\<^sub>\<F>\<^sub>\<L> aa) X = (if event(A) \<in> X then (HideFL aa X) 
                          else (HideAcceptance (acceptance(A)) X,event(A))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> (HideFL aa X))"

definition Hiding :: "'e fltraces \<Rightarrow> 'e set \<Rightarrow> 'e fltraces" (infixl "\\\<^sub>\<F>\<^sub>\<L>" 65) where
"P \\\<^sub>\<F>\<^sub>\<L> X = {HideFL s X|s. s \<in> P}"

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
  
lemma ExtChoiceH_bullet:
  assumes "ExtChoiceH \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> B x" "B \<in> P" "FL1 P"
  shows "x \<in> P"
  using assms apply (cases B, auto)
  using acceptance_bullet_event_FL1 by blast

lemma ExtChoiceH_emptyset:
  assumes "ExtChoiceH \<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> B x" "B \<in> P" "FL1 P"
  shows "x \<in> P"
  using assms apply (cases B, auto, case_tac x21, auto)
    apply (case_tac a, auto)
    apply (simp add: aevent_less_eq_FL1)
  by (case_tac x21, auto)

(*
lemma ExtChoice_Div_zero:
  assumes "FL0 P" "FL1 P"
  shows "Div \<box>\<^sub>\<F>\<^sub>\<L> P = Div"
  using assms unfolding Div_def ExtChoice_def apply auto
   apply (simp add: ExtChoiceH_bullet_then)
  using FL0_FL1_bullet_in by force
*)

lemma ExtChoiceH_exists:
  assumes "x \<in> P"
  shows "\<exists>B. (ExtChoiceH \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> B x \<or> ExtChoiceH \<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> B x) \<and> B \<in> P"
  using assms
proof (cases x)
  case (Acceptance x1)
  then show ?thesis
  proof (cases x1)
    case acnil
    then show ?thesis using Acceptance assms apply auto
      by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  next
    case (acset x2)
    then show ?thesis using Acceptance assms apply auto
      by (rule exI[where x="\<langle>[x2]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  qed
next
  case (AEvent x21 x22)
  then show ?thesis 
  proof (cases "acceptance(x21) = \<bullet>")
    case True
    then show ?thesis using AEvent assms apply auto
      apply (case_tac x21, auto)
      by (rule exI[where x="((\<bullet>,event(x21))\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> x22)"], auto)
  next
    case acceptance_not_bullet:False
    then obtain A b where Ab:"x21 = ([A]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L> \<and> b \<in>\<^sub>\<F>\<^sub>\<L> [A]\<^sub>\<F>\<^sub>\<L>"
      by (metis Rep_aevent_inverse acceptance.rep_eq amember.elims(2) event.rep_eq event_in_acceptance prod.collapse)
    then show ?thesis 
    proof (cases "A = {}")
      case True
      then show ?thesis using acceptance_not_bullet AEvent Ab by auto
    next
      case False
      then show ?thesis using acceptance_not_bullet AEvent Ab assms
        by (intro exI[where x="(([A]\<^sub>\<F>\<^sub>\<L>,b)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> x22)"], auto)
    qed
  qed
qed

lemma
  assumes "FL1 P" "x \<in> P" 
  shows "(\<exists>B. ExtChoiceH \<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L> B x \<and> B \<in> P) \<or> (\<exists>B. ExtChoiceH \<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> B x \<and> B \<in> P)"
  using assms apply auto
  apply (intro exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  oops

lemma ExtChoiceH_triple_refl: "ExtChoiceH x x x"
  apply (induct x rule:fltrace.induct, auto)
  by (case_tac x, auto, case_tac x1a, auto, case_tac a, auto)

lemma unionA_sym [simp]: "A \<union>\<^sub>\<F>\<^sub>\<L> B = B \<union>\<^sub>\<F>\<^sub>\<L> A"
  by (cases A, auto, cases B, auto, cases B, auto)

lemma ExtChoiceH_sym: "ExtChoiceH A B x = ExtChoiceH B A x"
  by (induct A B x rule:ExtChoiceH.induct, auto)

lemma acceptance_of_aevent_aunion_acceptances_1 [simp]:
 "acceptance (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event A)\<^sub>\<F>\<^sub>\<L> = acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B"
 by (cases A, auto, cases B, auto, case_tac a, auto, case_tac aa, auto, case_tac a, auto)

lemma acceptance_of_aevent_aunion_acceptances_2 [simp]:
 "acceptance (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event B)\<^sub>\<F>\<^sub>\<L> = acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B"
  by (cases A, auto)

lemma fl_cons_never_fixpoint [simp]: "\<not> aa = x #\<^sub>\<F>\<^sub>\<L> aa"
  by (induct aa, auto)

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

(*
lemma
  assumes "s \<le> t" "FL1 P" "FL1 Q"
          "ExtChoiceH A B t" "A \<in> P" "B \<in> Q"
    shows "\<exists>A B. ExtChoiceH A B s \<and> A \<in> P \<and> B \<in> Q"
  using assms 
proof (induct A B t arbitrary:s rule:ExtChoiceH.induct)
  case (1 A B X)
  then show ?case 
    apply auto
    apply (cases s, auto, case_tac x1, auto)
     apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
     apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (cases A, auto, cases B, auto, cases B, auto)
    by (metis "1.prems"(4))
next
  case ExtChoiceH2:(2 A aa B bb X)
  then show ?case
  proof (induct s X rule:less_eq_fltrace.induct)
    case (1 x y)
    then show ?case using ExtChoiceH2 by auto
  next
    case (2 x y ys)
    then have "x \<le> acceptance(y)"
      using less_eq_fltrace.simps(2) by blast
    then show ?case using 2
       apply (cases x, auto)
        apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"],rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"],rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
       apply (rule exI[where x="\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply (rule exI[where x="\<langle>acceptance(B)\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply auto
      using less_eq_acceptance.elims(2) apply force
      using FL_cons_acceptance apply blast
      using FL_cons_acceptance apply blast
       apply (rule exI[where x="\<langle>acceptance(A)\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply (rule exI[where x="\<langle>acceptance(B)\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply auto
      using less_eq_acceptance.elims(2) apply force
      using FL_cons_acceptance apply blast
      using FL_cons_acceptance by blast
  next
    case (3 x xs y ys)
    have "event A \<in>\<^sub>\<F>\<^sub>\<L> (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B) \<or> acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B = \<bullet>"
      by (cases A, auto, cases B, auto, case_tac a, auto, case_tac aa, auto, case_tac a, auto)
    then have "x = (acceptance A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B,event A)\<^sub>\<F>\<^sub>\<L> \<or> x = (\<bullet>,event A)\<^sub>\<F>\<^sub>\<L>"
      using 3 apply auto
       apply (cases x, auto)      
      apply (metis acceptance_set amember.simps(1) dual_order.antisym less_eq_acceptance.elims(2) less_eq_aevent_def)
      apply (metis Un_iff acceptance.distinct(1) acceptance_event amember.simps(2) aunion.elims event_in_acceptance less_eq_aevent_def)
       apply (cases x, auto)      
      sledgehammer[debug=true]

      then obtain pA pB xA where pAB:
            "xA \<le> xs \<and> pA \<le> (acceptance A,event A)\<^sub>\<F>\<^sub>\<L> \<and> pB \<le> (acceptance B,event A)\<^sub>\<F>\<^sub>\<L>"
      by auto
(*    then have "x = (acceptance pA \<union>\<^sub>\<F>\<^sub>\<L> acceptance pB,event pA)\<^sub>\<F>\<^sub>\<L>"
      using 3 
      apply auto
      apply (cases x, auto, case_tac a, auto, cases A, cases B, auto) *)
    then show ?case using 3
      apply auto
       apply (rule exI[where x="pA #\<^sub>\<F>\<^sub>\<L> xA"])
       apply (rule exI[where x="pB #\<^sub>\<F>\<^sub>\<L> xA"], auto)
      next
    case (4 x xs y)
    then show ?case sorry
  qed
next
  case (3 A B bb X)
  then obtain sA where sA: "sA \<le> A" by auto
  then show ?case using 3
    apply (cases X, auto)
     apply (rule exI[where x="\<langle>sA\<rangle>\<^sub>\<F>\<^sub>\<L>"], cases A, auto, cases sA, auto)
      apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], cases s, auto, case_tac x1, auto)
    apply (cases B, auto)
    apply (cases sA, auto, cases s, auto)

  proof (induct s X rule:less_eq_fltrace.induct)
    case (1 x y)
    then show ?case
      apply auto
      apply (cases x, auto)
       apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      apply (cases A, auto, cases B, auto, case_tac a, auto)
      by (metis "1.prems"(4))
  next
    case (2 x y ys)
    then show ?case 
      apply auto
      apply (cases x, auto)
      apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"])
       apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      apply (cases A, auto, cases B, auto, case_tac a, auto)
      by (metis ExtChoiceH.simps(3) acceptance_set amember.simps(2) aunion.simps(3))
  next
    case (3 x xs y ys)
    then show ?case
      apply auto
      apply (cases "bb = \<langle>A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B\<rangle>\<^sub>\<F>\<^sub>\<L>", auto)
       apply (rule exI[where x="\<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
       apply (rule exI[where x="\<langle>B,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      apply (cases xs, auto, case_tac x1, auto)
      apply (cases x, auto)
       apply (cases A, auto, case_tac a, auto)
        apply (simp add: less_eq_aevent_def)+
      apply (cases B, auto)
  next
    case (4 x xs y)
    then show ?case sorry
  qed
    case (Acceptance x)
    then show ?case
      apply auto
      apply (cases x, auto)
      apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
     apply (cases A, cases B, auto, cases B, auto, case_tac a, auto)
     apply (metis "3.prems"(4))
    apply (cases x, auto)
      apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (cases A, cases B, auto, cases B, auto, case_tac a, auto)
    by (metis ExtChoiceH.simps(3) acceptance_set amember.simps(2) aunion.simps(3))
  next
    case (AEvent x1a s)
    then show ?case 
    proof (cases s)
      case (Acceptance x1)
      then show ?thesis using AEvent
        apply auto
        apply (cases x1a, auto)
        apply (rule exI[where x="\<langle>A \<union>\<^sub>\<F>\<^sub>\<L> acceptance B\<rangle>\<^sub>\<F>\<^sub>\<L>"])
        apply (rule exI[where x="\<langle>B,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
            apply (cases B, auto, cases A, auto, case_tac a, auto)
        apply (case_tac aa, auto)
        apply (simp add: less_eq_aevent_def)
             apply (case_tac aa, auto, case_tac a, auto)
        sledgehammer[debug=true]
             apply (metis Un_iff acceptance_event acceptance_set amember.elims(2) amember.simps(2) less_eq_acceptance.simps(3) less_eq_aevent_def less_eq_fltrace.simps(1) sup.idem sup_left_commute)
        apply (cases A, auto, case_tac a, auto)
             apply (metis Un_commute Un_left_absorb acceptance.distinct(1) acceptance_event acceptance_set amember.elims(2) aunion.simps(3) eq_iff first.simps(2) less_eq_acceptance.elims(2) less_eq_acceptance.simps(2) less_eq_aevent_def unionA_sym)
        apply (case_tac a, auto)
            apply (metis Un_commute Un_left_absorb acceptance.distinct(1) acceptance_event acceptance_set amember.elims(2) aunion.simps(3) eq_iff first.simps(2) less_eq_acceptance.elims(2) less_eq_acceptance.simps(2) less_eq_aevent_def unionA_sym)

    next
      case (AEvent x21 x22)
      then show ?thesis sorry
    qed
      apply auto
      apply (cases x1a, auto, case_tac a, auto, cases A, auto)
        apply (simp_all add: less_eq_aevent_def)
       apply (cases B, auto, case_tac a, auto)
       apply (cases s, auto)
      apply (case_tac x1, auto)
    qed
next
case (4 A aa B X)
  then show ?case sorry
qed
        apply (cases s, auto)

lemma 
  assumes "FL1 P" "FL1 Q"
  shows "FL1 (P \<box>\<^sub>\<F>\<^sub>\<L> Q)"
  using assms unfolding FL1_def ExtChoice_def apply auto
*)
  

subsection \<open> Refinement \<close>

abbreviation Refines :: "'e fltraces \<Rightarrow> 'e fltraces \<Rightarrow> bool" (infixl "\<sqsubseteq>\<^sub>\<F>\<^sub>\<L>" 65) where
"P \<sqsubseteq>\<^sub>\<F>\<^sub>\<L> Q \<equiv> Q \<subseteq> P"

lemma ExtChoice_refines_double:
  "P \<box>\<^sub>\<F>\<^sub>\<L> P \<sqsubseteq>\<^sub>\<F>\<^sub>\<L> P"
  unfolding ExtChoice_def apply auto
  using ExtChoiceH_triple_refl by blast

text \<open>Idempotency does not hold for external choice in FL.\<close>

lemma
  "P \<sqsubseteq>\<^sub>\<F>\<^sub>\<L> (P \<box>\<^sub>\<F>\<^sub>\<L> P)"
  unfolding ExtChoice_def apply auto
  nitpick[expect=genuine]
  oops

lemma ExtChoice_sym:
  "P \<box>\<^sub>\<F>\<^sub>\<L> Q = Q \<box>\<^sub>\<F>\<^sub>\<L> P"
  unfolding ExtChoice_def apply auto
  using ExtChoiceH_sym by blast+

lemma ExtChoice_unit:
  assumes "FL1 P"
  shows "Stop \<box>\<^sub>\<F>\<^sub>\<L> P = P"
  using assms unfolding ExtChoice_def Stop_def apply auto
    apply (simp add: ExtChoiceH_emptyset)
   apply (simp add: ExtChoiceH_bullet)
  using ExtChoiceH_exists
  by blast

lemma ExtChoice_dist:
  shows "P \<box>\<^sub>\<F>\<^sub>\<L> (Q \<sqinter>\<^sub>\<F>\<^sub>\<L> R) = (P \<box>\<^sub>\<F>\<^sub>\<L> Q) \<sqinter>\<^sub>\<F>\<^sub>\<L> (P \<box>\<^sub>\<F>\<^sub>\<L> R)"
  unfolding ExtChoice_def IntChoice_def by auto

text \<open>Following laws do not hold in FL.\<close>

lemma
  assumes "FL0 P" "FL0 Q" "FL0 R"
  shows "((P \<sqinter>\<^sub>\<F>\<^sub>\<L> R) \<box>\<^sub>\<F>\<^sub>\<L> (Q \<sqinter>\<^sub>\<F>\<^sub>\<L> R)) = ((P \<box>\<^sub>\<F>\<^sub>\<L> Q) \<sqinter>\<^sub>\<F>\<^sub>\<L> R)"
  nitpick[expect=genuine]
  oops

lemma
  assumes "FL0 P" "FL0 Q" "FL0 R"
  shows "P \<sqinter>\<^sub>\<F>\<^sub>\<L> (Q \<box>\<^sub>\<F>\<^sub>\<L> R) = (P \<sqinter>\<^sub>\<F>\<^sub>\<L> Q) \<box>\<^sub>\<F>\<^sub>\<L> (P \<sqinter>\<^sub>\<F>\<^sub>\<L> R)"
  nitpick[expect=genuine]
  oops

lemma a_then_Stop:
  "a \<rightarrow>\<^sub>\<F>\<^sub>\<L> Stop = {\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>,
                  \<langle>([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>
                  }"
  unfolding Prefix_def Stop_def by auto

lemma Hiding_Stop:
  "Stop \\\<^sub>\<F>\<^sub>\<L> X = Stop"
  unfolding Stop_def Hiding_def apply auto
   apply (rule exI[where x="\<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

lemma Hiding_a_then_Stop:
  assumes "a \<notin> X"
  shows "(PrefixAlt a Stop) \\\<^sub>\<F>\<^sub>\<L> X = (PrefixAlt a Stop)"
  using assms 
  unfolding PrefixAlt_def Stop_def Hiding_def prefixH_def apply auto
         apply (rule exI[where x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
        apply (rule exI[where x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
       apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
      apply (rule exI[where x="\<langle>([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
     apply (rule exI[where x="\<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
   apply (rule exI[where x="\<langle>([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule exI[where x="\<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

lemma Hiding_a_then_Stop2:
  "(PrefixAlt a Stop) \\\<^sub>\<F>\<^sub>\<L> {a} = Stop"
  unfolding PrefixAlt_def Hiding_def Stop_def prefixH_def apply auto
   apply (rule exI[where x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L>\<langle>[{}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)

lemma Hiding_a_then_P:
  assumes "FL1 P"
  shows "(PrefixAlt a P) \\\<^sub>\<F>\<^sub>\<L> {a} = P \\\<^sub>\<F>\<^sub>\<L> {a}"
  using assms unfolding PrefixAlt_def Hiding_def Stop_def prefixH_def apply auto
   apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s" in exI, auto)

lemma Hiding_a_then_P_event_in_set:
  assumes "FL1 P" "a \<in> X"
  shows "(PrefixAlt a P) \\\<^sub>\<F>\<^sub>\<L> X = P \\\<^sub>\<F>\<^sub>\<L> X"
  using assms unfolding PrefixAlt_def Hiding_def Stop_def prefixH_def apply auto
   apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
  by (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> s" in exI, auto)

lemma Hiding_a_then_P_event_not_in_set:
  assumes "FL1 P" "a \<notin> X"
  shows "(PrefixAlt a P) \\\<^sub>\<F>\<^sub>\<L> X = (PrefixAlt a (P \\\<^sub>\<F>\<^sub>\<L> X))"
  using assms unfolding PrefixAlt_def Hiding_def Stop_def prefixH_def apply auto
  apply (rule exI[where x="\<langle>[{a}]\<^sub>\<F>\<^sub>\<L>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
    apply (rule exI[where x="\<langle>\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"], auto)
   apply (rule_tac x="([{a}]\<^sub>\<F>\<^sub>\<L>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> sa" in exI, auto)
  by (rule_tac x="(\<bullet>,a)\<^sub>\<F>\<^sub>\<L> #\<^sub>\<F>\<^sub>\<L> sa" in exI, auto)

end