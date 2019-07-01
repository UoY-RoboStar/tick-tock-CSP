theory TickTock_FL

imports
  TickTock_Max_FL
  TickTock_Max_TT1
begin

text \<open> This theory defines the overall Galois connection between FL and Tick-Tock, using the
       two Galois connections, defined in TickTock_Max_FL and TickTock_Max_TT1. \<close>

section \<open> Adjoints \<close>

definition "fl2tt(P) = mkTT1(fl2ttm(P))"

definition "tt2fl(P) = ttm2fl(unTT1(P))"

section \<open> Properties \<close>

lemma fl2tt_mono:
  assumes "P \<subseteq> Q"
  shows "fl2tt(P) \<subseteq> fl2tt(Q)"
  using assms 
  by (simp add: fl2tt_def fl2ttm_mono mkTT1_mono)

lemma tt2fl_mono:
  assumes "P \<subseteq> Q"
  shows "tt2fl(P) \<subseteq> tt2fl(Q)"
  using assms
  by (simp add: tt2fl_def ttm2fl_mono unTT1_mono)

lemma TT_fl2tt_closed:
  assumes "FL0 P" "FL1 P" "FL2 P" "FL3 P"
  shows "TTwf(fl2tt(P))"
        "TT0(fl2tt(P))"
        "TT1(fl2tt(P))"
        "TT2(fl2tt(P))"
        "TT3(fl2tt(P))"
        "TT4(fl2tt(P))"
  using assms unfolding fl2tt_def 
  using TTwf_fl2ttm TTwf_mkTT1 apply blast
      apply (simp add: TT0_mkTT1 assms(1) assms(2) assms(3) assms(4) maximal_TT_fl2ttm_closed(1))
     apply (simp add:TT1_mkTT1)
    apply (simp add: TT1w_fl2ttm TT2_mkTT1 assms(1) assms(2) assms(3) assms(4) maximal_TT_fl2ttm_closed(3) maximal_TT_fl2ttm_closed(6) maximal_TT_fl2ttm_closed(7))
   apply (simp add: TT3_fl2ttm TT3_mkTT1)
  by (simp add: TT4_fl2ttm TT4_mkTT1 assms(4))

lemma FL_tt2fl_closed:
  assumes "TT(P)"
  shows "FL0(tt2fl(P))" "FL1(tt2fl(P))" "FL2(tt2fl(P))" "FL3(tt2fl(P))"
  using assms unfolding tt2fl_def
     apply (simp add: FL0_ttm2fl TT0_unTT1 TT1w_unTT1 TT_TT0 TT_TT1)
    apply (simp add: FL1_ttm2fl)
   apply (simp add: FL2_ttm2fl TT1w_unTT1 TTM1_unTT1 TTM2_unTT1)
  by (simp add: FL_ttm2fl_closed(4) TT0_unTT1 TT1w_unTT1 TTM1_unTT1 TTM2_unTT1 TTM3_unTT1 TT_TT0 TT_TT1 assms)

lemma
  shows "ttm2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL0 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
  unfolding ttm2fl_def apply auto
  using FL0_def by blast

(* \<forall>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P" *)
definition mkFL2 :: "'a fltraces \<Rightarrow> 'a fltraces" where
"mkFL2 P \<equiv> P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

lemma mkFL2_disj_univ: "mkFL2 (\<Union> P) = \<Union> ({mkFL2(x)|x. x \<in> P})"
  unfolding mkFL2_def by auto

lemma FL2_fixpoint: "FL2 P \<longleftrightarrow> mkFL2 P = P"
  unfolding FL2_def mkFL2_def by auto

lemma mkFL2_is_FL2: "FL2(mkFL2(P))"
  unfolding mkFL2_def FL2_def apply auto
  by (metis Finite_Linear_Model.last.simps(1) amember.simps(1) concat_FL_last_not_bullet_absorb last_bullet_then_last_cons last_cons_bullet_iff)

definition mkFL120 :: "'a fltraces \<Rightarrow> 'a fltraces" where
"mkFL120 P \<equiv> P \<union> {s. \<exists>\<beta> A a t. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> t \<le> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> s = \<beta> &\<^sub>\<F>\<^sub>\<L> t}"

(*
lemma 
  "{fl. FLTick0 Tick fl \<and> FL2 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}
    =
   {t. \<exists>fl. t = mkFL2(fl) \<and> FLTick0 Tick fl \<and> FL2 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
  using FL2_fixpoint by auto

lemma
  "mkFL2(\<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}) =
  \<Union>{mkFL2(fl)|fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
  using mkFL2_disj_univ by auto

lemma
  "{mkFL2(fl)|fl. FLTick0 Tick fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}
    =
   {fl. FLTick0 Tick fl \<and> FL2 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
  apply auto
  oops
*)

lemma FL2_mkFL1:
  assumes "FL2 X"
  shows "FL2 (mkFL1 X)"
  using assms unfolding mkFL1_def FL2_def
  apply safe
  apply blast
  oops
(*
lemma 
  assumes "FL1 X"
  shows "FL2 (mkFL1 (mkFL2 X))"
  using assms FL2_mkFL1
  by (simp add: FL2_mkFL1 mkFL2_is_FL2)

lemma FL3_mkFL12:
  assumes "FL3 X"
  shows "FL3 (mkFL1 (mkFL2 X))"
  using assms sorry
 
lemma FL1_mkFL1:
  "FL1( mkFL1 X)"
  unfolding FL1_def mkFL1_def by auto

lemma ttm2fl_alt:
  assumes "TTM1 P" "TTM2 P" "TT1w P" "FL2 (ttm2fl P)"
  shows "ttm2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL2 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
  using assms unfolding ttm2fl_def fl2ttm_def apply auto
  apply (rule_tac x="mkFL1(mkFL2(X))" in exI, auto)
  using FL3_mkFL12 apply blast
  using FL2_mkFL1 mkFL2_is_FL2 apply blast
  using FL1_mkFL1 apply auto
  using FL2_def Un_iff mem_Collect_eq mem_simps(9) mkFL2_def subset_eq
  sledgehammer[debug=true]
   apply (smt fl2ttobs_for_FL2_imp)
  using fl2ttobs_for_FL2_imp by blast*)

definition mkFL12 :: "'a fltraces \<Rightarrow> 'a fltraces" where
"mkFL12 P \<equiv> P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}"

lemma mkFL12_eq_mkFL1_mkFL2:
  assumes "FL1 P"
  shows "mkFL12(P) = mkFL1(mkFL2(P))"
  using assms unfolding mkFL1_def mkFL2_def mkFL12_def apply safe
  apply blast+
  using FL1_def by blast+

lemma mkFL12_disj_univ: "mkFL12 (\<Union> P) = \<Union> ({mkFL12(x)|x. x \<in> P})"
  unfolding mkFL12_def by auto

lemma mkFL12_is_FL2: 
  assumes "FL1 P"
  shows "FL1(mkFL12(P))"
  using assms unfolding mkFL12_def FL1_def apply safe
  apply blast
  using order_trans by blast

lemma FL2_disj_imp:
  assumes "FL2 P" "FL2 Q" 
  shows "FL2(P \<union> Q)"
  using assms unfolding FL2_def by auto


(* NOTE: It works.. just the witness chosen was previously wrong :-) *)
lemma ttm2fl_alt:
  assumes "TTM1 P" "TTM2 P" "TT1w P" 
  shows "ttm2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL2 fl \<and> FL1 fl \<and> FL0 fl \<and> (fl2ttm fl) \<subseteq> P}"
  using assms unfolding ttm2fl_def fl2ttm_def apply auto
  (*apply (rule_tac x="\<Union>{fl. FL3 fl \<and> FL1 fl \<and> {fl2ttobs fla |fla. fla \<in> fl} \<subseteq> P}" in exI, auto)
   * The following seems to give me an easy way to generalise this.
  *)
  apply (rule_tac x="\<Union>{fl. FL3 fl \<and> FL1 fl \<and> {fl2ttobs fla |fla. fla \<in> fl} \<subseteq> P}" in exI, auto)
    apply (smt FLTick0_def mem_Collect_eq mem_simps(9)) 
  using  FL2_ttm2fl 
   apply (simp add: fl2ttm_def ttm2fl_def) 
  using FL2_ttm2fl assms(1) assms(2) assms(3) apply blast
   apply (smt FL1_def Union_iff mem_Collect_eq)
  using FL0_def by blast

lemma TT3_unTT1:
  assumes "TT1 P" "TT3 P" 
  shows "TT3(unTT1(P))"
  using assms unfolding TT3_def unTT1_def  apply auto
  using TT1_mkTT1_simp TT3_def TT_TT3 by blast

definition mkTT4 :: "'e ttobs list set \<Rightarrow> 'e ttobs list set" where
"mkTT4 P = P \<union> {add_Tick_refusal_trace \<rho>|\<rho>. \<rho> \<in> P}"

lemma TTickTrace_eq_add_Tick_refusal_trace_fixpoint:
  "TTickTrace t \<longleftrightarrow> add_Tick_refusal_trace t = t"
  by (induct t rule:add_Tick_refusal_trace.induct, auto)

lemma TTM1_mkTT4:
  assumes "TTM1 P" "TTM3 P"
  shows "TTM1 (mkTT4 P)"
  using assms unfolding TTM1_def TTM3_def mkTT4_def apply auto
  by (metis TTickTrace_eq_add_Tick_refusal_trace_fixpoint)

lemma TTM2_mkTT4:
  assumes "TTM2 P" "TTM3 P"
  shows "TTM2 (mkTT4 P)"
  using assms unfolding TTM2_def TTM3_def mkTT4_def apply auto
  by (metis TTickTrace_eq_add_Tick_refusal_trace_fixpoint)

lemma TTM3_mkTT4:
  assumes "TTM3 P"
  shows "TTM3 (mkTT4 P)"
  using assms unfolding TTM3_def mkTT4_def apply auto
  by (metis TTickTrace_eq_add_Tick_refusal_trace_fixpoint)

lemma TT1w_mkTT4:
  assumes "TT1w P"
  shows "TT1w (mkTT4 P)"
  using assms unfolding TT1w_def TTM3_def mkTT4_def apply auto
  by (smt add_Tick_refusal_trace_concat add_Tick_refusal_trace_tt_subset append_eq_append_conv tt_prefix_decompose tt_prefix_tt_subset tt_subset_same_length)

(*
lemma
  assumes "TTM1 x" "TTM2 x" "TTM3 x" "TT1w x" "TT4 P" "x \<subseteq> P" "{y. \<exists>\<sigma>. y \<lesssim>\<^sub>C \<sigma> \<and> \<sigma> \<in> x} \<subseteq> P"
          "xa \<lesssim>\<^sub>C add_Tick_refusal_trace \<rho>" "\<rho> \<in> x"
        shows "xa \<in> P"
  using assms apply (induct \<rho> rule:rev_induct, auto)
   apply (cases xa, auto)
  apply (case_tac xb, auto)
  sledgehammer
  using tt_prefix_subset_antisym apply fastforce+*)



lemma
  "\<rho> \<in> x \<Longrightarrow> add_Tick_refusal_trace \<rho> \<in> mkTT4 x"
  unfolding mkTT4_def by auto

lemma TT4_unTT1:
  assumes "TT1 P" "TT4 P" 
  shows "TT4(unTT1(P))"
  using assms unfolding TT4_def unTT1_def  apply auto
  apply (rule_tac x="mkTT4(x)" in exI, auto)
  using TTM1_mkTT4 apply blast
  using TTM2_mkTT4 apply blast
  using TTM3_mkTT4 apply blast
  using TT1w_mkTT4 apply blast
   apply (smt TT1_fixpoint_mkTT1 TT1_mkTT1_simp UnE mem_Collect_eq mkTT1_mono mkTT4_def subsetI)
  unfolding mkTT4_def by auto

(* We have that: lemma TT2_mkTT1:
  assumes "TT2 P" "TT1w P" "TTM1 P" "TTM2 P"
  shows "TT2(mkTT1(P))" *)

lemma
  assumes "TTM1 x\<^sub>0" "TTM2 x\<^sub>0" "TTM3 x\<^sub>0" "TT1w x\<^sub>0" "TT0 x\<^sub>0" "mkTT1 x\<^sub>0 \<subseteq> P"
          "TTM1 x\<^sub>1" "TTM2 x\<^sub>1" "TTM3 x\<^sub>1" "TT1w x\<^sub>1" "TT0 x\<^sub>1" "mkTT1 x\<^sub>1 \<subseteq> P" "y \<in> x\<^sub>0"
  shows "y \<in> x\<^sub>1"
  using assms apply (induct y rule:rev_induct, auto)
  unfolding mkTT1_def apply auto
  
  using TT0_TT1w_empty apply blast
  apply (case_tac x, auto)
  sledgehammer

lemma
  assumes "TT P" "TT4w P"
          "TTM1 x\<^sub>0" "TTM2 x\<^sub>0" "TTM3 x\<^sub>0" "TT1w x\<^sub>0" "mkTT1 x\<^sub>0 \<subseteq> P"
          "TTM1 x\<^sub>1" "TTM2 x\<^sub>1" "TTM3 x\<^sub>1" "TT1w x\<^sub>1" "mkTT1 x\<^sub>1 \<subseteq> P"
          "TTM1 x" "TTM2 x" "TTM3 x" "TT1w x" "mkTT1 x \<subseteq> P"
          "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> x\<^sub>0 \<or>
                 e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x\<^sub>1} = {}"
         "\<rho> @ [X]\<^sub>R # \<sigma> \<in> x"
      shows "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
proof -
  have "\<forall>e. (e \<noteq> Tock \<and> e \<in> Y) \<longrightarrow> \<rho> @ [[e]\<^sub>E] \<notin> x\<^sub>0"
    using assms(18) by blast
  have "\<forall>e. (e = Tock \<and> e \<in> Y) \<longrightarrow> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<notin> x\<^sub>1"
    using assms(18) by blast

  (* Seems likely to hold.. but not sure *)
  assume A1:"\<forall>e. \<rho> @ [[e]\<^sub>E] \<in> x\<^sub>0 \<longleftrightarrow> \<rho> @ [[e]\<^sub>E] \<in> x"
            "\<forall>e. \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x\<^sub>1 \<longleftrightarrow> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x"
  then have "Y \<inter> {e. e \<noteq> Tock \<and> \<rho> @ [[e]\<^sub>E] \<in> x \<or>
                 e = Tock \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x} = {}"
    using assms(18) by auto
  then have "Y \<subseteq> X"
                                                             
  (* What we need is to show that Y \<subseteq> X *)

lemma
  assumes "TT P" "TT4w P"
        "Y \<inter> {e. e \<noteq> Tock \<and> (\<exists>x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> mkTT1 x \<subseteq> P \<and> \<rho> @ [[e]\<^sub>E] \<in> x) \<or>
                 e = Tock \<and> (\<exists>x. TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> mkTT1 x \<subseteq> P \<and> \<rho> @ [[X]\<^sub>R, [e]\<^sub>E] \<in> x)} = {}"
        "TTM1 x" "TTM2 x" "TTM3 x" "TT1w x" "mkTT1 x \<subseteq> P" "\<rho> @ [X]\<^sub>R # \<sigma> \<in> x"
  shows "\<rho> @ [X \<union> Y]\<^sub>R # \<sigma> \<in> x"
proof -
  have ""


lemma
  assumes "TT P" "TT4w P"
  shows "TT2(unTT1(P))"
  using assms unfolding TT2_def unTT1_def apply auto
  apply (rule_tac x="x" in exI, auto)



lemma
  assumes "TT P" "TT0(unTT1(P))" "TT2(unTT1(P))" "TT3(unTT1(P))" "TT4(unTT1(P))"
  shows "unTT1 P = \<Union>{x. TT0 x \<and> TT2 x \<and> TT3 x \<and> TT4 x \<and> TTM1 x \<and> TTM2 x \<and> TTM3 x \<and> TT1w x \<and> (mkTT1 x) \<subseteq> P}"
  unfolding unTT1_def mkTT1_def apply auto
  using assms apply (rule_tac x="unTT1 P" in exI, auto)
  using TTM1_unTT1 apply blast
  using TTM2_unTT1 apply blast
  using TTM3_unTT1 apply blast
  using TT1w_unTT1 apply blast
  unfolding unTT1_def apply auto
  apply (metis (mono_tags, lifting) UnI1 contra_subsetD mkTT1_def) 
   apply (metis (mono_tags, lifting) contra_subsetD mem_Collect_eq mkTT1_simp)
  apply (rule_tac x="X" in exI, auto)
  by (metis contra_subsetD mkTT1_simp)
          
  
  apply (metis assms(4) unTT1_def)
  apply (smt Union_iff mem_Collect_eq) 
(*  apply (smt TTM2_def Union_iff mem_Collect_eq) 
  
  apply (metis TTM2_def Union_iff mem_Collect_eq)*)
  unfolding TTM2_def apply (smt Union_iff mem_Collect_eq) 
(*
  apply (rule_tac x="mkFL12 X" in exI, auto)
  using FL3_mkFL12 apply blast
  using mkFL12_is_FL2 apply blast
  using FL1_mkFL12 apply blast
  unfolding mkFL12_def apply auto
  using FL2_def Un_iff mem_Collect_eq mem_simps(9) mkFL2_def subset_eq
   apply (smt fl2ttobs_for_FL2_imp)
  using fl2ttobs_for_FL2_imp by blast*)

lemma mkFL12_is_FL2: "FL2(mkFL12(P))"
proof -
 (* have "FL2({s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
    unfolding FL2_def apply auto
    apply (rule_tac x="\<beta>'" in exI, rule_tac x="Aa" in exI, auto)
    apply (rule_tac x="aa" in exI, auto)*)
  have "FL2(mkFL12(P))
        =
        FL2(P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
    unfolding mkFL12_def by auto
  also have "... =
        (\<forall>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})
                \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}))
        "
    unfolding FL2_def by auto
  also have "... =
        (\<forall>\<beta> A a. 
          (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A 
            \<longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>}))
          \<and>
          (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>} 
                  \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})))
        "
    by blast
  also have "... =
        (\<forall>\<beta> A a. 
          (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>} 
                  \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})))
        "
    by blast
  also have "... =
        (\<forall>\<beta> A a. 
          ((\<exists>\<beta>' A' a'. \<beta>' &\<^sub>\<F>\<^sub>\<L> \<langle>A'\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a' \<in>\<^sub>\<F>\<^sub>\<L> A' \<and> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> \<beta>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A',a')\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<longrightarrow> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> (P \<union> {s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})))
        "
    by blast
  also have "... =
        (\<forall>\<beta> A a. 
          ((\<exists>\<beta>' A' a'. \<beta>' &\<^sub>\<F>\<^sub>\<L> \<langle>A'\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a' \<in>\<^sub>\<F>\<^sub>\<L> A' \<and> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> \<beta>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A',a')\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)
                  \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A 
              \<longrightarrow> (\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<or>
                  (\<exists>\<beta>' A' a'. \<beta>' &\<^sub>\<F>\<^sub>\<L> \<langle>A'\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a' \<in>\<^sub>\<F>\<^sub>\<L> A' \<and> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> \<beta>' &\<^sub>\<F>\<^sub>\<L> \<langle>(A',a')\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>))))
        "
    by blast
  unfolding mkFL12_def FL2_def apply auto
  apply (case_tac A, auto, case_tac Aa, auto)
  
  apply (metis Finite_Linear_Model.last.simps(1) amember.simps(1) concat_FL_last_not_bullet_absorb last_bullet_then_last_cons last_cons_bullet_iff)
  by (metis acceptance.exhaust amember.simps(1) concat_FL_last_not_bullet_absorb last_cons_acceptance_not_bullet last_cons_bullet_iff)

lemma
  fixes x ::"'a::order"
  assumes "x \<le> b" "c < b" "\<not>x \<le> c" "x \<noteq> c" "\<not>(\<exists>z. c < z \<and> z < b)"
  shows "b \<le> x"
  using assms nitpick
  
lemma
  assumes "last \<beta> \<noteq> \<bullet>"
  shows "\<not>(\<exists>z. z \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<and> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> z \<and> z \<noteq> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using assms apply auto
  by (simp add: concat_FL_last_not_bullet_absorb)

lemma fltrace_less_imp_not_less:
  assumes "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z"
  shows "\<not> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms  apply (induct z \<beta> rule:less_eq_fltrace.induct, auto)
  apply (metis acceptance.distinct(1) acceptance_set dual_order.strict_iff_order fltrace_concat2.simps(3) less_eq_acceptance.elims(2) less_eq_fltrace.simps(1) less_eq_fltrace.simps(2) plus_acceptance.elims)
  using less_eq_fltrace.simps(4) less_fltrace_def apply blast
   apply (simp add: less_le_not_le)
  by (metis Finite_Linear_Model.last.simps(1) aevent_less_eq_iff_components bullet_left_zero2 concat_FL_last_not_bullet_absorb fltrace_concat2.simps(1) less_eq_acceptance.elims(2) less_eq_aevent_def less_eq_fltrace.simps(2) less_eq_fltrace.simps(3) less_fltrace_def x_le_x_concat2)

lemma fltrace_less_imp_not_less':
  assumes "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z"
  shows "\<not> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms  apply (induct z \<beta> rule:less_eq_fltrace.induct, auto)
apply (metis acceptance.distinct(1) acceptance_set dual_order.strict_iff_order fltrace_concat2.simps(3) less_eq_acceptance.elims(2) less_eq_fltrace.simps(1) less_eq_fltrace.simps(2) plus_acceptance.elims)
  using less_eq_fltrace.simps(4) less_fltrace_def apply blast
   apply (simp add: less_le_not_le)
  by (metis Finite_Linear_Model.last.simps(1) aevent_less_eq_iff_components bullet_left_zero2 concat_FL_last_not_bullet_absorb fltrace_concat2.simps(1) less_eq_acceptance.elims(2) less_eq_aevent_def less_eq_fltrace.simps(2) less_eq_fltrace.simps(3) less_fltrace_def x_le_x_concat2)

lemma
  shows "\<not>(\<exists>z. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z \<and> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  using fltrace_less_imp_not_less
  by (simp add: fltrace_less_imp_not_less)

lemma
  

lemma
  assumes "FL1 P" "x \<notin> P" "x \<le> b" "c \<in> P" "c \<le> b" "\<not>(\<exists>z. c < z \<and> z < b)"
  shows "x = b"
proof -
  have "\<forall>y. y \<le> c \<longrightarrow> y \<in> P"
    using FL1_def assms(1) assms(4) by blast
  then have "\<forall>y. y \<le> c \<longrightarrow> x \<noteq> y"
    using assms(2) by blast
  then have "\<not> x \<le> c" "x \<noteq> c"
    apply blast
    using assms(2) assms(4) by blast
  then have "b \<le> x"
    nitpick
    by (metis assms(3) assms(5) assms(6) eq_iff order.not_eq_order_implies_strict)
    using assms(3) by blast
    using assms(3) by blast

lemma order_no_intermediate_imp_eq:
  fixes x ::"'a::order"
  assumes "\<forall>y. y \<le> c \<longrightarrow> x \<noteq> y" "c \<le> x" "x \<le> b" "\<not>(\<exists>z. c < z \<and> z < b)" 
  shows "b \<le> x"
  using assms apply auto 
  using dual_order.order_iff_strict by blast

lemma
  fixes a :: "'a::{order,plus}"
  assumes "\<forall>a b c. (a \<le> c \<and> b \<le> c) \<longrightarrow> (a \<le> b \<or> b \<le> a)" "\<forall>a c. (\<exists>b. a + b = c) \<longleftrightarrow> a \<le> c"
  shows "a \<le> b + c \<longrightarrow> a \<le> b \<or> b \<le> a"
  using assms oops

lemma
  fixes x :: "'a fltrace"
  assumes "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"
  shows "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  nitpick

lemma
  fixes x :: "'a fltrace"
  assumes "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>" "A \<noteq> \<bullet>" "\<not>(\<exists>z. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z \<and> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
  shows "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  using assms 

lemma fltrace_consFL_less_eq_case:
  assumes "a \<in>\<^sub>\<F>\<^sub>\<L> A \<or> A = \<bullet>"
  shows "x &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms
  apply (induct x, auto)
   apply (case_tac x, auto)
   apply (cases A, auto)
  by (case_tac x, auto)

lemma
  assumes "FL1 P"
  shows "FL1({s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> s \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>})"
  using assms unfolding FL1_def apply safe
   apply (rule_tac x="\<beta>" in exI, rule_tac x="A" in exI, rule_tac x="a" in exI)
   apply safe
  sledgehammer
  using fltrace_trans by blast

lemma FL1_mkFL12:
  assumes "FL1 P"
  shows "FL1(mkFL12(P))"
proof -
  have "FL1({s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> (s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    unfolding mkFL12_def by auto
  also have "... = FL1({s. \<exists>\<beta> A a. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P \<and> a \<in>\<^sub>\<F>\<^sub>\<L> A \<and> (s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> s = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)})"
    using assms sledgehammer
  using assms unfolding mkFL12_def FL1_def 
 
  
  apply safe
  
  using FL1_def apply blast
   apply (rule_tac x="\<beta>" in exI, rule_tac x="A" in exI, rule_tac x="a" in exI)
  sledgehammer
  apply (rule_tac x="a" in exI, auto)

lemma
  assumes "\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> x \<noteq> y" "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P" "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x" nitpick
  using assms apply (induct x , auto)
  apply (induct \<beta>, auto)
   apply (case_tac xa, auto)
  apply (cases \<beta>, auto)
   apply (cases \<beta>, auto)
   apply (cases A, auto, case_tac x1, auto)
  apply (induct \<beta>, auto)
  
  apply (metis Finite_Linear_Model.last.simps(1) bullet_right_zero2 concat_FL_last_not_bullet_absorb fltrace.distinct(1) fltrace_concat2.simps(3) plus_acceptance.elims x_le_x_concat2 xs_less_eq_z_two_only)
  sledgehammer apply (case_tac x1a, auto)
  apply (metis FL1_def Finite_Linear_Model.last.simps(1) assms(4) bullet_left_zero2 concat_FL_last_not_bullet_absorb x_le_x_concat2 xs_less_eq_z_two_only)
    
   apply (metis FL_cons_acceptance acceptance.distinct(1) less_eq_acceptance.elims(2))
sledgehammer
     apply (smt FL_cons_acceptance acceptance.distinct(1) bullet_right_zero2 first.simps(1) fltrace.distinct(1) fltrace.inject(2) fltrace_concat2.simps(2) fltrace_induct fltrace_trans less_eq_acceptance.elims(2) less_eq_fltrace.elims(2) x_le_x_concat2 xs_less_eq_z_two_only)
  apply (smt FL_cons_acceptance acceptance.distinct(1) acceptance_set bullet_right_zero2 first.simps(1) first.simps(2) fltrace.distinct(1) fltrace_concat2.simps(2) fltrace_concat2.simps(3) fltrace_consFL_less_eq_case less_eq_acceptance.elims(2) less_eq_fltrace.elims(2) x_le_concat2_FL1)
proof -
  have "\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> y \<in> P"
    using FL1_def assms(1) assms(4) by blast
  then have a:"\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> x \<noteq> y"
    using assms(2) by blast
  then have b:"\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>" "x \<noteq> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"
    apply blast
    using assms(2) assms(4) by blast
  then have c:"\<not>(\<exists>z. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z \<and> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    apply auto
    by (simp add: fltrace_less_imp_not_less')
  then show ?thesis sledgehammer

  {assume "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  then have "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
    using order_no_intermediate_imp_eq a c assms(3) by }

  assume "\<not> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  then have "\<not> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < x"
    by (simp add: less_le)
  then have "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    
    using a b c 

lemma
  assumes "FL1 P" "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>" "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"  "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "x = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
  using assms apply (case_tac "last \<beta> \<noteq> \<bullet>", auto)
  
   apply (simp add: concat_FL_last_not_bullet_absorb)
  sledgehammer
  using assms apply (induct x arbitrary:\<beta>, auto)
   apply (case_tac xa, auto)
  
    apply (metis bullet_left_zero2 x_le_x_concat2)
   apply (cases A, auto)
   apply (case_tac \<beta>, auto, case_tac x1, auto)
  apply (case_tac x1a, auto, case_tac aa, auto)
apply (case_tac \<beta>, auto, case_tac x1, auto)
   apply (case_tac xa, auto)

  apply (metis Finite_Linear_Model.last.simps(1) acceptance.distinct(1) acceptance.exhaust acceptance_set bullet_left_zero2 concat_FL_last_not_bullet_absorb less_eq_acceptance.simps(2) less_eq_acceptance.simps(3) less_eq_fltrace.simps(1) less_eq_fltrace.simps(2))
   apply (cases A, auto)
  apply (case_tac xa, auto, case_tac y, auto)
  
     apply (metis acceptance_set aevent_less_eq_iff_components amember.simps(1))
    apply (case_tac aa,auto)
  
    apply (simp add: aevent_less_eq_iff_components)
   apply (case_tac y, auto, case_tac aa, auto)
  


lemma
  assumes "FL1 P" "x \<notin> P" "x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>" "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<in> P" "a \<in>\<^sub>\<F>\<^sub>\<L> A"
  shows "x = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<or> x = \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
proof -
  have "\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> y \<in> P"
    using FL1_def assms(1) assms(4) by blast
  then have a:"\<forall>y. y \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<longrightarrow> x \<noteq> y"
    using assms(2) by blast
  then have b:"\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>" "x \<noteq> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L>"
    apply blast
    using assms(2) assms(4) by blast
  then have c:"\<not>(\<exists>z. \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < z \<and> z < \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>)"
    apply auto
    by (simp add: fltrace_less_imp_not_less)
  have "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    by (simp add: fltrace_consFL_less_eq_case assms(5))
  have "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(\<bullet>,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
    sledgehammer
  {assume "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  then have "\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
    using order_no_intermediate_imp_eq a c assms(3) }

  assume "\<not> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x"
  then have "\<not> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> < x"
    by (simp add: less_le)
  then have "\<not> x \<le> \<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>(A,a)\<^sub>\<F>\<^sub>\<L>,\<bullet>\<rangle>\<^sub>\<F>\<^sub>\<L>"
    
    using a b c 
    using \<open>\<beta> &\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<le> x\<close> by blast
  (* x \<le> b \<and> \<not> x \<le> c \<and> c \<le> b \<longrightarrow> x = b*)

(*
lemma FL1_mkFL2:
  assumes "FL1 P"
  shows "FL1(mkFL2(P))"
  using assms unfolding mkFL2_def FL1_def 
 
  
  apply safe
  
  using FL1_def apply blast
  apply (rule_tac x="\<beta>" in exI, rule_tac x="A" in exI, auto)
  apply (rule_tac x="a" in exI, auto)
  *)
lemma FL3_union_imp_dist:
  assumes "FL3 (P \<union> Q)"
  shows "FL3 P"
  using assms unfolding FLTick0_def by auto

lemma FL3_mkFL2:
  assumes "FL3 X"
  shows "FL3 (mkFL2 X)"
  using assms unfolding mkFL2_def  apply auto
  by (smt FLTick0_def Un_iff mem_Collect_eq tickWF_acceptance_imp_tickWF_consFL)

lemma FL3_mkFL12:
  assumes "FL3 X"
  shows "FL3 (mkFL12 X)"
  using assms unfolding mkFL12_def FLTick0_def apply auto
   apply (simp add: tickWF_acceptance_imp_tickWF_consFL)
  by (metis (no_types, lifting) bullet_right_zero2 concat_FL_last_not_bullet_absorb fltrace_concat.simps(3) last_bullet_concatmix tickWF_concatFL_imp tickWF_consFL_notin_prefix tickWF_imp_prefix x_le_x_concat2)


lemma FL1_mkFL2:
  "FL1(mkFL2 X)"
  unfolding mkFL2_def FL1_def apply auto
  sorry

lemma FL1_mkFL12:
  "FL1(mkFL12 X)"
  unfolding mkFL12_def FL1_def apply auto
  sledgehammer
  sorry

lemma ttm2fl_alt:
  assumes "TTM1 P" "TTM2 P" "TT1w P" "FL2 (ttm2fl P)"
  shows "ttm2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL2 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
  using assms unfolding ttm2fl_def fl2ttm_def apply auto
  apply (rule_tac x="mkFL12 X" in exI, auto)
  using FL3_mkFL12 apply blast
  using mkFL12_is_FL2 apply blast
  using FL1_mkFL12 apply blast
  unfolding mkFL12_def apply auto
  using FL2_def Un_iff mem_Collect_eq mem_simps(9) mkFL2_def subset_eq
   apply (smt fl2ttobs_for_FL2_imp)
  using fl2ttobs_for_FL2_imp by blast
 (* by (smt FL2_def Un_iff mem_Collect_eq mem_simps(9) mkFL2_def subset_eq)+*)

lemma ttm2fl_alt':
  assumes "TTM1 P" "TTM2 P" "TT1w P"
  shows "ttm2fl P = \<Union>{fl. FLTick0 Tick fl \<and> FL2 fl \<and> FL1 fl \<and> (fl2ttm fl) \<subseteq> P}"
proof -
  have "FL2 (ttm2fl P)"
    using assms by (simp add:FL2_ttm2fl)
  then show ?thesis
    using assms ttm2fl_alt by blast
qed

end