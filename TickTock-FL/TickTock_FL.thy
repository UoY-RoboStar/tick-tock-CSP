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

end