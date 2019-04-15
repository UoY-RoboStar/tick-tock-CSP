theory TickTock_FL_inverse

imports
  TickTock_FL
begin

lemma "ctt2fl(fl2ctt(P)) = Q"
proof -
  have "ctt2fl(fl2ctt(P))
        =
        \<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> {flt2cttobs fla |fla. fla \<in> fl} \<subseteq> {flt2cttobs fl |fl. fl \<in> P}}"
  unfolding fl2ctt_def ctt2fl_def by simp
  also have "... = 
        \<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> 
          (\<forall>x. (\<exists>fla. x = flt2cttobs fla \<and> fla \<in> fl) \<longrightarrow> (\<exists>fl. x = flt2cttobs fl \<and> fl \<in> P))}"
    by auto
  also have "... = 
        \<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> 
          (\<forall>fla. fla \<in> fl \<longrightarrow> (\<exists>fl. flt2cttobs fla = flt2cttobs fl \<and> fl \<in> P))}"
    by auto
  also have "... = 
        \<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> fl \<subseteq> {fla |fla fl. flt2cttobs fla = flt2cttobs fl \<and> fl \<in> P}}"
    by auto
  
end