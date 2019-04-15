theory TickTock_Additional

imports
  TickTock_FL
  Finite_Linear_Priority
begin

lemma "ctt2fl(fl2ctt(pri p P)) = pri p (ctt2fl(fl2ctt P))"
  unfolding fl2ctt_def ctt2fl_def pri_def apply safe
  oops

(* Maybe can define an equivalent function to ctt2fl(fl2ctt(P)) = cttify(P) *)

fun cttify :: "'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> 'e fltrace \<Rightarrow> 'e fltrace set" where
"cttify \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> \<langle>A\<rangle>\<^sub>\<F>\<^sub>\<L> s P = True" |
"cttify (A #\<^sub>\<F>\<^sub>\<L> aa) (B #\<^sub>\<F>\<^sub>\<L> bb) s P = (event(A) = event(B) \<and> (if event(A) = Tock then (\<exists>C. s &\<^sub>\<F>\<^sub>\<L> (C,Tock)\<^sub>\<F>\<^sub>\<L> \<in> P \<and> C \<noteq> \<bullet>)
                                                            else False) \<and> acceptance(A) \<subseteq> acceptance(B))"
                             
lemma "ctt2fl(fl2ctt(P)) = Q"
proof -
  have "ctt2fl(fl2ctt(P))
        =
        \<Union>{fl. FLTick0 Tick fl \<and> FL1 fl \<and> {flt2cttobs fla |fla. fla \<in> fl} \<subseteq> {flt2cttobs fl |fl. fl \<in> P}}"
    unfolding fl2ctt_def ctt2fl_def by auto
  also have "... =
        {x. \<exists>fl. x \<in> fl \<and> FLTick0 Tick fl \<and> FL1 fl \<and> {flt2cttobs fla |fla. fla \<in> fl} \<subseteq> {flt2cttobs fl |fl. fl \<in> P}}"
    by auto
  also have "... =
        {x. \<exists>fl. x \<in> fl \<and> FLTick0 Tick fl \<and> FL1 fl \<and> (\<forall>x. (\<exists>fla. x = flt2cttobs fla \<and> fla \<in> fl) \<longrightarrow> (\<exists>fla. x = flt2cttobs fla \<and> fla \<in> P))}"
    by auto
  also have "... =
        {x. \<exists>fl. x \<in> fl \<and> FLTick0 Tick fl \<and> FL1 fl \<and> (\<forall>fl\<^sub>0. (fl\<^sub>0 \<in> fl) \<longrightarrow> (\<exists>fla. flt2cttobs fl\<^sub>0 = flt2cttobs fla \<and> fla \<in> P))}"
    by auto
  oops

end