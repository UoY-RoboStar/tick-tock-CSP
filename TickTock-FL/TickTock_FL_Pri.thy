theory TickTock_FL_Pri

imports
  TickTock_Max_TT1_Pri
begin

(*
"prirefTT1 pa S sa Q = 
  {z. ((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b))
        \<and>
       ((z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<longrightarrow>
          ((sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
            \<or>
           (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)))}")*)

lemma "{z. (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}
        =
       {z. (z = Tock \<longrightarrow> (Q \<inter> {sa @ [[S]\<^sub>R, [Tock]\<^sub>E]}) \<subseteq> {x. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})}"
  by auto

lemma "{z. (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}
        =
       {z. z \<noteq> Tock \<or> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<or> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}"
  by auto

lemma prirefTT1_alt:
  assumes "TT3(Q)"
  shows "prirefTT1 pa S sa Q =
      {z. z \<in> S \<or> (sa @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock) \<or> z = Tick
           \<or> 
          (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
          }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}"
proof -
  have
    "prirefTT1 pa S sa Q
      =
      ({z. (z \<noteq> Tock \<or> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
        \<and>
       ((z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<longrightarrow>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock))} \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    unfolding prirefTT1_def by auto
  also have "... =
     ({z. (z \<noteq> Tock \<and> ((z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tick) \<longrightarrow> (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)))
          \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q) \<and> (\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick))} \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    by auto
  also have "... =
     ({z. (z \<noteq> Tock \<and> ((z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<longrightarrow> (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)))}
      \<union> {z. (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q) \<and> (\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick))} 
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    by auto
  also have "... =
     ({z. ((z \<noteq> Tock \<or> (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)) \<and> \<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)) 
          \<or> ( sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<or> (\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)))
             \<and> (z <\<^sup>*pa Tock \<or> (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q) \<and> (\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)))}
      
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    by auto
  also have "... =
     ({z. ((z \<noteq> Tock \<and> \<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick))
          \<or> (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<and> \<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick))) 
          \<or> (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
          \<or> ((\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick)) \<and> z <\<^sup>*pa Tock)}
      
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    by auto
  also have "... =
     ({z. (\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<or> (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock))
           \<and> 
          (z \<noteq> Tock \<or> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q) 
          }
      
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    by auto 
  also have "... =
     ({z. (\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<and> z \<noteq> Tock)
           \<or> 
          (\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
          }
      
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    by auto 
  also have "... =
     ({z. ((z \<in> S \<or> sa @ [[z]\<^sub>E] \<notin> Q \<or> z = Tick) \<and> z \<noteq> Tock)
           \<or> 
          (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
          }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    by auto
  also have "... =
     ({z. ((z \<in> S \<and> z \<noteq> Tock) \<or> (sa @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock) \<or> z = Tick)
           \<or> 
          (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
          }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    by auto 
   also have "... =
     ({z. ((z \<in> S \<and> z \<noteq> Tock) \<or> (sa @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock) \<or> z = Tick)
           \<or> 
          (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
          }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
     by auto 
  also have "... =
     {z. z \<in> S \<or> (sa @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock) \<or> z = Tick
           \<or> 
          (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
      }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}"
    apply auto
    using TT3_any_cons_end_tock assms by blast+
  then show ?thesis 
    using \<open>prirefTT1 pa S sa Q = {z. (z \<noteq> Tock \<or> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q) \<and> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick \<longrightarrow> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)} \<union> {z. \<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b}\<close> by auto
qed

lemma ttWF_dist_notTock_cons:
  assumes "ttWF (xs @ ([[x]\<^sub>E] @ ys))" "x \<noteq> Tock"
  shows "ttWF ([[x]\<^sub>E] @ ys)"
  using assms apply (induct xs rule:ttWF.induct, auto)
  by (cases x, auto)

lemma ttWF_before_Tock_not_Tock:
  assumes "ttWF (xs @ [[x1]\<^sub>E, [Tock]\<^sub>E])"
  shows "x1 \<noteq> Tock"
  using assms by (induct xs rule:ttWF.induct, auto)

lemma TTwf_not_event_before_Tock:
  assumes "TTwf(Q)"
  shows "xs @ [[x1]\<^sub>E, [Tock]\<^sub>E] \<notin> Q"
  using assms
proof -
  have "\<not> ttWF (xs @ [[x1]\<^sub>E, [Tock]\<^sub>E])"
    using assms apply (induct xs rule:ttWF.induct, auto)
    using ttWF.elims(2) by auto
  then have "xs @ [[x1]\<^sub>E, [Tock]\<^sub>E] \<notin> Q"
    using assms TTwf_def by blast
  then show ?thesis .
qed


lemma TTwf_Refusal_imp_no_Tock:
  assumes "sa @ [[S]\<^sub>R] \<in> Q" "TTwf(Q)"
  shows "sa @ [[Tock]\<^sub>E] \<notin> Q"
  using assms apply (induct sa rule:rev_induct, auto)
  using TTwf_def ttWF.simps(6) apply blast
  by (metis TTwf_cons_end_not_refusal_refusal TTwf_not_event_before_Tock ttobs.exhaust)
 
lemma
  assumes "TTwf(Q)" 
  shows "{z. z \<in> S \<or> (sa @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock) \<or> z = Tick
           \<or> 
          (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
      }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}
      =
      S \<union> {z.(sa @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock) \<or> z = Tick
           \<or> 
          (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
      }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}"
proof -
   have "{z. z \<in> S \<or> (sa @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock) \<or> z = Tick
           \<or> 
          (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
      }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}
      =
     (S \<union> {z. (sa @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock) \<or> z = Tick
           \<or> 
          (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q)
           \<or>
          (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
          }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
     using assms by auto
   then show ?thesis .
 qed
  (*also have "... =
     ({z. (\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<and> z \<noteq> Tock)
           \<or> 
          ((\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<or> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q)
           \<and>
          ((\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q) \<or> z <\<^sup>*pa Tock))
          }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
    by auto
  also have "... =
     ({z. (\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<and> z \<noteq> Tock)
           \<or> 
          ((\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<or> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q)
           \<and>
          ((\<not> (z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q) \<or> z <\<^sup>*pa Tock))
          }
      \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"
   apply auto*)

definition prirefTT13 :: "('e ttevent) partialorder \<Rightarrow> ('e ttevent) set \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttevent) set" where
"prirefTT13 pa S sa Q = 
  (S \<union> {z. (sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)} 
     \<union> {z. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})"

fun prirelRef3 :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> bool" where
"prirelRef3 p [] [] s Q = True" |
"prirelRef3 p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (R \<subseteq> prirefTT13 p S s Q)" |
"prirelRef3 p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q =
   ((R \<subseteq> prirefTT13 p S s Q) \<and> Tock \<notin> prirefTT13 p S s Q \<and> prirelRef3 p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"prirelRef3 p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> prirelRef3 p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT13 p Z s Q)))" |
"prirelRef3 p x y s Q = False"

definition priTT3 :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttobs) list set" where
"priTT3 p P = {\<rho>|\<rho> s. prirelRef3 p \<rho> s [] P \<and> s \<in> P}"



(* 
lemma
  fixes s :: "'a ttobs list"
  assumes "x \<lesssim>\<^sub>C t" "TT P" "prirelRef3 p x s i P" "s \<in> P" 
  shows "\<exists>s. prirelRef2 p x s i P \<and> s \<lesssim>\<^sub>C x"
  using assms apply (induct p x s i P rule:prirelRef3.induct, auto)
  
  using prirelRef2.simps(1) apply blast
*)

lemma rev_induct_eq_length:
  assumes "List.length x = List.length y"
          "(P [] [])"
          "(\<And>x y xs ys. P xs ys \<Longrightarrow> List.length xs = List.length ys \<Longrightarrow> P (xs @ [x]) (ys @ [y]))"
        shows "P x y"
  using assms
  apply(simplesubst rev_rev_ident[symmetric])
  apply(subst rev_rev_ident[symmetric])
  by(rule_tac xs = "List.rev x" and ys = "List.rev y" in list_induct2, simp_all)

lemma prirelRef3_same_length [intro]:
  assumes "prirelRef3 p x s i P"
  shows "List.length x = List.length s"
  using assms by (induct p x s i P rule:prirelRef3.induct, auto)

lemma List_length_cons_both_imp [intro]:
  assumes "List.length (xs @ [x]) = List.length (ys @ [y])"
  shows "List.length xs = List.length ys"
  using assms by (induct xs ys rule:rev_induct_eq_length, auto)

lemma prirelRef3_imp_eq_events:
  assumes "prirelRef3 p (xs @ [[x]\<^sub>E]) (ys @ [[y]\<^sub>E]) i P"
  shows "x = y"
  using assms 
  apply (induct p xs ys i P rule:prirelRef3.induct, auto)
  apply (metis prirelRef3.simps(12) prirelRef3.simps(80) prirelRef3.simps(82) prirelRef3.simps(9) ttevent.exhaust)
  using prirelRef3_same_length by fastforce+

lemma prirelRef3_imp_concat_prirelRef3:
  assumes "prirelRef3 p (xs @ [[x1]\<^sub>E]) (ys @ [[x1a]\<^sub>E]) i P"
  shows "prirelRef3 p xs ys i P"
  using assms  
  apply (induct p xs ys i P rule:prirelRef3.induct, auto)
  apply (metis (full_types) prirelRef3.simps(12) prirelRef3.simps(3) prirelRef3.simps(80) prirelRef3_imp_eq_events subsetCE ttevent.exhaust)
  using prirelRef3_same_length by fastforce+

lemma prirefTT13_imp_prirefTT1_aux:
  assumes "R \<subseteq> S \<union> {z. z <\<^sup>*pa Tock} \<union> {z. \<exists>b. b \<notin> S \<and> s @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b}"
          "TT3 Q" "Tock \<in> R" "s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
        shows "\<exists>b. b \<notin> S \<and> s @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> Tock <\<^sup>*pa b"
proof -
  have "Tock \<notin> S"
    using assms TT3_any_cons_end_tock TT_TT3 by blast
  then have "Tock \<in> {z. \<exists>b. b \<notin> S \<and> s @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b}"
    using assms by blast
  then show ?thesis
    by auto
qed

lemma prirefTT13_imp_prirefTT1:
  assumes "R \<subseteq> prirefTT13 pa S s Q" "TT3(Q)"
  shows "R \<subseteq> prirefTT1 pa S s Q"
  using assms unfolding prirefTT13_def prirefTT1_def apply auto
  using prirefTT13_imp_prirefTT1_aux by blast

lemma
  assumes "Tock \<notin> prirefTT13 pa S s Q" "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
  shows "Tock \<notin> prirefTT1 pa S s Q"
  using assms unfolding prirefTT13_def prirefTT1_def by auto

lemma
  assumes "Tock \<in> prirefTT1 pa S s Q" "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
  shows "Tock \<in> prirefTT13 pa S s Q"
  using assms unfolding prirefTT13_def prirefTT1_def by auto

lemma prirefTT13_subset_prirefTT1:
  assumes "TT3(Q)"
  shows "prirefTT13 pa S s Q \<subseteq> prirefTT1 pa S s Q"
  using assms unfolding  prirefTT1_def prirefTT13_def apply auto
  using prirefTT13_imp_prirefTT1_aux by blast

lemma TT2w_union_Ref_imp:
  assumes "s @ [[S]\<^sub>R] \<in> Q" "TT2w(Q)"
  shows "s @ [[S\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R] \<in> Q"
proof -
  obtain Y where Y:"Y = {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q)}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> Q) \<or> (e = Tock \<and> s @ [[S]\<^sub>R, [e]\<^sub>E] \<in> Q) } = {}"
    by auto
  then have "s @ [[S\<union>Y]\<^sub>R] \<in> Q"
    using assms unfolding TT2w_def by auto
  then show ?thesis using Y
    by (metis (no_types, lifting) Collect_cong)
qed

lemma TT2w_union_Ref_Tock_imp:
  assumes "s @ [[S]\<^sub>R] \<in> Q" "TT2w(Q)"
  shows "s @ [[S\<union>{e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}]\<^sub>R] \<in> Q"
proof -
  obtain Y where Y:"Y = {e::'a ttevent. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> Q) \<or> (e = Tock \<and> s @ [[S]\<^sub>R, [e]\<^sub>E] \<in> Q) } = {}"
    by auto
  then have "s @ [[S\<union>Y]\<^sub>R] \<in> Q"
    using assms unfolding TT2w_def by auto
  then show ?thesis using Y
    by (metis (no_types, lifting))
qed

lemma TT2_union_Ref_Tock_imp:
  assumes "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q" "TT2(Q)"
  shows "s @ [[S\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
proof -
  obtain Y where Y:"Y = {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q)}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> Q) \<or> (e = Tock \<and> s @ [[S]\<^sub>R, [e]\<^sub>E] \<in> Q) } = {}"
    by auto
  then have "s @ [[S\<union>Y]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
    using assms unfolding TT2_def by auto
  then show ?thesis using Y
    by (metis (no_types, lifting) Collect_cong)
qed

lemma TT1_Ref_Tock_subset_imp:
  assumes "s @ [[S\<union>Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "TT1(Q)"
  shows "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
  using assms 
  by (meson TT1_def sup_ge1 tt_prefix_common_concat tt_prefix_subset.simps(2) tt_prefix_subset_refl)

lemma TT1_Ref_Tock_subset_imp':
  assumes "s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "TT1(Q)" "Z \<subseteq> S"
  shows "s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
  using assms 
  by (meson TT1_def sup_ge1 tt_prefix_common_concat tt_prefix_subset.simps(2) tt_prefix_subset_refl)

definition "refTickTock S s Q == (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                                     \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"

fun addRefTickTock :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> 'e ttobs list set \<Rightarrow> 'e ttobs list" where
  "addRefTickTock [] s Q = []" |
  "addRefTickTock ([e]\<^sub>E # t) s Q = [e]\<^sub>E # (addRefTickTock t (s @ [[e]\<^sub>E]) Q)" |
  "addRefTickTock ([X]\<^sub>R # t) s Q = [refTickTock X s Q]\<^sub>R # (addRefTickTock t (s @ [[X]\<^sub>R]) Q)"

lemma prirefTT1_imp_prirefTT13:
  assumes "TT(Q)" "TT4(Q)" "s @ [[S]\<^sub>R] \<in> Q" "TT2(Q)"
  shows "prirefTT1 pa S s Q \<subseteq> prirefTT13 pa (refTickTock S s Q) s Q \<and> s @ [[refTickTock S s Q]\<^sub>R] \<in> Q"
proof -
  obtain J where J:"J = S\<union>{Tick}
                         \<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                         \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}"
    by auto
  have prirefTT1_alt:"prirefTT1 pa S s Q =
            S \<union> {z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)} \<union> {Tick}
              \<union> {e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}
              \<union> {z. s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock}
              \<union> {z. (\<exists>b. b \<notin> S \<and> s @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}"
    using assms prirefTT1_alt by (auto simp add:TT_TT3 prirefTT1_alt) 

  have a:"S \<subseteq> prirefTT13 pa S s Q"
    unfolding prirefTT13_def by auto

  have b:"{Tick} \<subseteq> prirefTT13 pa (S\<union>{Tick}) s Q" "s @ [[S\<union>{Tick}]\<^sub>R] \<in> Q"
    unfolding prirefTT13_def apply auto
    using assms TT4_middle_Ref_with_Tick TT_TT1 by fastforce

  have c:  "{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)} \<subseteq> prirefTT13 pa (S\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}) s Q"
       and "s @ [[S\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R] \<in> Q"
       and "s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R] \<in> Q"
    unfolding prirefTT13_def apply auto
    using assms apply (simp add: TT2w_union_Ref_imp TT_TT2w)
    using assms b TT2w_union_Ref_imp TT_TT2w by fastforce

  have d:  "{e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<subseteq> prirefTT13 pa (S\<union>{e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q"
       and "s @ [[S\<union>{e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}]\<^sub>R] \<in> Q"
       and d1:"s @ [[J]\<^sub>R] \<in> Q"
    unfolding prirefTT13_def apply auto
    using assms apply (simp add: TT2w_union_Ref_Tock_imp TT_TT2w)
    using assms c TT2w_union_Ref_Tock_imp TT_TT2w
    using \<open>s @ [[S \<union> {Tick} \<union> {z. s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock}]\<^sub>R] \<in> Q\<close> J by fastforce

  have a1:"S \<subseteq> prirefTT13 pa (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q"
    unfolding prirefTT13_def by auto
  have a2:"{Tick} \<subseteq> prirefTT13 pa (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q"
    unfolding prirefTT13_def by auto
  have a3:"{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)} \<subseteq> prirefTT13 pa (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q"
    unfolding prirefTT13_def by auto
  have a4:"{e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<subseteq> prirefTT13 pa (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q"
    unfolding prirefTT13_def apply auto
    using TT_TTwf TTwf_Refusal_imp_no_Tock assms(1) assms(3) apply blast
    using assms TT_TT1 TT1_Ref_Tock_subset_imp 
    by (metis (no_types, lifting) Un_insert_right)

  have "s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}]\<^sub>R] \<in> Q"
    using TT2w_union_Ref_Tock_imp TT_TT2w \<open>s @ [[S \<union> {Tick} \<union> {z. s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock}]\<^sub>R] \<in> Q\<close> assms(1) by blast
  have a5:"{z. s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock} \<subseteq> {z. s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock}"
  proof (cases "s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q")
    case True
    then have "s @ [[S\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      using TT2_union_Ref_Tock_imp assms(4) by blast
    then have "s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<in> Q"
      using TT4_TT1_add_Tick TT_TT1 assms(1) assms(2) by fastforce
    then show ?thesis
      by blast
  next
    case False
    then show ?thesis
      by blast
  qed

  have a51: "{z. s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock}
        \<subseteq> 
        prirefTT13 pa (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                                  \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q"
    unfolding prirefTT13_def using a5 by auto

  have a6: "{z. (\<exists>b. b \<notin> S \<and> s @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)} 
            \<subseteq> 
            prirefTT13 pa (J) s Q"
    unfolding prirefTT13_def J by auto
(*
  have a5:"{z. s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock} 
            \<subseteq> 
            prirefTT13 pa (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                               \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q"
    unfolding prirefTT13_def apply auto
    using TT1_Ref_Tock_subset_imp' assms d1 apply auto oops*)

  have "S \<union> {z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)} \<union> {Tick}
              \<union> {e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} 
              \<union> {z. s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock}
              \<union> {z. (\<exists>b. b \<notin> S \<and> s @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)} 
        \<subseteq> 
        prirefTT13 pa (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                                  \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q"
    using a1 a2 a3 a4 a51 a6 J by auto
  then have "prirefTT1 pa S s Q 
             \<subseteq> 
             prirefTT13 pa J s Q"
    using prirefTT1_alt J by auto
  then have "prirefTT1 pa S s Q \<subseteq> prirefTT13 pa J s Q \<and> s @ [[J]\<^sub>R] \<in> Q"
    using d1 by blast
  then show ?thesis unfolding refTickTock_def using J by blast
qed

lemma prirefTT1_imp_prirefTT13':
  assumes "TT(Q)" "TT4(Q)" "s @ [[S]\<^sub>R] \<in> Q" "TT2(Q)"
  shows "prirefTT1 pa S s Q \<subseteq> prirefTT13 pa (refTickTock S s Q) s Q"
  using assms prirefTT1_imp_prirefTT13 by blast

lemma prirefTT1_imp_prirefTT13'' [intro]:
  assumes "TT(Q)" "TT4(Q)" "s @ [[S]\<^sub>R] \<in> Q" "TT2(Q)"
  shows "s @ [[refTickTock S s Q]\<^sub>R] \<in> Q"
  using assms prirefTT1_imp_prirefTT13 by blast

lemma TT1_Ref_Tock_imp_Ref [intro]:
  assumes "s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "TT1(Q)"
  shows "s @ [[S]\<^sub>R] \<in> Q"
  using assms
  by (meson TT1_def order_refl tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset_same_front)

lemma prirefTT1_imp_prirefTT13_noassm:
  assumes "TT(Q)" "TT4(Q)" "TT2(Q)"
  shows "prirefTT1 pa S s Q \<subseteq> prirefTT13 pa (refTickTock S s Q) s Q"
proof (cases "s @ [[S]\<^sub>R] \<in> Q")
  case True
  then show ?thesis
    using assms(1) assms(2) assms(3) prirefTT1_imp_prirefTT13 by blast
next
  case False
  then show ?thesis
     unfolding prirefTT1_def prirefTT13_def refTickTock_def apply simp_all
     using TT1_Ref_Tock_subset_imp' TT_TT1 assms(1) by blast
qed

(*
lemma prirefTT1_imp_prirefTT13':
  assumes "R \<subseteq> prirefTT1 pa S s Q" "TT(Q)" "TT4(Q)" "s @ [[S]\<^sub>R] \<in> Q" "TT2(Q)"
  shows "R \<subseteq> prirefTT13 pa (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                                  \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q 
          \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                                  \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}]\<^sub>R] \<in> Q"
  sledgehammer
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) order_trans prirefTT1_imp_prirefTT13)*)

lemma prirelRef3_extend_both_events_eq_size_maximal_ttWF:
  assumes "prirelRef3 p xs ys s P" "ttWF (ys @ [[e\<^sub>1]\<^sub>E])" "maximal(p,e\<^sub>1)" "TT3_trace (ys @ [[e\<^sub>1]\<^sub>E])"
  shows "prirelRef3 p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef3.induct, auto)
     apply (cases e\<^sub>1, auto)
  using TT3_trace_cons_imp_cons 
     apply (smt UnE mem_Collect_eq prirefTT13_def some_higher_not_maximal)
  using TT3_trace_cons_imp_cons ttWF.elims(2) apply auto[1]
  by (metis TT3_trace_cons_imp_cons ttWF.simps(4) ttWF.simps(6) ttevent.exhaust)

lemma prirelRef3_extend_both_Ref:
  assumes "prirelRef3 p xs ys s P" "ttWF (ys @ [[S]\<^sub>R])"  "TT3_trace (ys @ [[S]\<^sub>R])" "R \<subseteq> prirefTT13 p S (s @ ys) P"
  shows "prirelRef3 p (xs @ [[R]\<^sub>R]) (ys @ [[S]\<^sub>R]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef3.induct, auto)
  by (metis TT3_trace_cons_imp_cons append_Nil list.exhaust ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttWF_prefix_is_ttWF ttevent.exhaust)+

lemma prirelRef_extend_both_tock_refusal_ttWF:
  assumes "prirelRef3 p xs ys s P" "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])" "R \<subseteq> prirefTT13 p S (s @ ys) P" "Tock \<notin> prirefTT13 p S (s @ ys) P"
  shows "prirelRef3 p (xs @ [[R]\<^sub>R,[Tock]\<^sub>E]) (ys @ [[S]\<^sub>R,[Tock]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:prirelRef3.induct, auto)
  by (metis append_Nil list.exhaust ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttWF_prefix_is_ttWF ttevent.exhaust)+

lemma prirelRef2_imp_eq_length [intro]:
  assumes "prirelRef2 p xs ys i P"
  shows "List.length xs = List.length ys"
  using assms by (induct p xs ys i P rule:prirelRef2.induct, auto)

lemma
  assumes "prirelRef2 p xs ys i P"
  shows "\<exists>zs. prirelRef3 p xs zs i P \<and> zs \<lesssim>\<^sub>C ys"
  using assms apply (induct p xs ys i P rule:prirelRef2.induct, auto)
  using prirelRef3.simps(1) apply fastforce
  oops

  thm ttWF2.induct

(*
lemma
  assumes "prirelRef2 p xs ys i P" "TT(P)" "TT2(P)" "TT4(P)" "i @ ys \<in> P"
  shows "\<exists>zs. prirelRef3 p xs zs i P"
proof -
  have a:"List.length xs = List.length ys"
    using assms(1) by blast
  then show ?thesis using assms
  proof (induct xs ys rule:ttWF2.induct, auto)*)

lemma prirelRef2_both_imp:
  assumes "prirelRef2 p (xs @ x) (ys @ y) i P" "List.length xs = List.length ys"  "ttWF y"
  shows "prirelRef2 p x y (i @ ys) P"
  using assms apply(induct p xs ys i P rule:prirelRef2.induct, auto)
  apply (cases x, auto, cases y, auto)
  apply (cases y, auto, case_tac a, auto, case_tac aa, auto)
  apply (case_tac x1, auto, case_tac x1a, auto)
  apply (case_tac x1, auto)
   apply (case_tac x1a, auto)
  by (case_tac x1, auto, case_tac x1a, auto)

lemma prirelRef2_concat_both_imp:
  assumes "prirelRef2 p (xs @ x) (ys @ y) i P" "List.length xs = List.length ys"
  shows "prirelRef2 p xs ys i P"
  using assms apply(induct p xs ys i P rule:prirelRef2.induct, auto)
  apply (cases x, auto, cases y, auto, cases y, auto)
  apply (case_tac a, auto, case_tac aa, auto)
  by (case_tac x1, auto, case_tac x1a, auto)

lemma addRefTickTock_dist_concat:
  "addRefTickTock (xs @ ys) i P = (addRefTickTock xs i P) @ (addRefTickTock ys (i @ xs) P)"
  by (induct xs i P rule:addRefTickTock.induct, auto)

lemma addRefTickTock_concat_event:
  "addRefTickTock (xs @ [[x1]\<^sub>E]) i P = (addRefTickTock xs i P) @ [[x1]\<^sub>E]"
  by (induct xs i P rule:addRefTickTock.induct, auto)

lemma Tock_notin_prirefTT1_imp_notin_prirefTT13:
  assumes "Tock \<notin> prirefTT1 pa S s Q" "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "Tock \<notin> prirefTT13 pa (refTickTock S s Q) s Q"
  using assms unfolding prirefTT1_def prirefTT13_def refTickTock_def apply auto
  using TT2_union_Ref_Tock_imp TT4_TT1_add_Tick TT_TT1 apply fastforce
  using TT3_any_cons_end_tock TT_TT3 by blast

lemma TT2w_union_Ref_ext_imp:
  assumes "TT(P)" "TT2(P)" "TT4(P)" "s @ [[X]\<^sub>R] @ t \<in> P"
  shows "s @ [[X\<union>{z. (s @ [[z]\<^sub>E] \<notin> P \<and> z \<noteq> Tock)}]\<^sub>R] @ t \<in> P"
proof -
  obtain Y where Y:"Y = {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> P)}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X\<union>{z. (s @ [[z]\<^sub>E] \<notin> P \<and> z \<noteq> Tock)}]\<^sub>R] @ t \<in> P"
    using assms
    by (simp add: TT2_def inf_set_def)
  then show ?thesis .
qed

lemma TT2w_union_RefTock_ext_imp:
  assumes "TT(P)" "TT2(P)" "TT4(P)" "s @ [[X]\<^sub>R] @ t \<in> P"
  shows "s @ [[X\<union>{e. e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R] @ t \<in> P"
proof -
  obtain Y where Y:"Y = {e::'a ttevent. e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X\<union>{e. e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R] @ t \<in> P"
    using assms
    by (simp add: TT2_def inf_set_def)
  then show ?thesis .
qed

lemma TT2w_union_Ref_ext_imp':
  assumes "TT(P)" "TT2(P)" "TT4(P)" "s @ [[X]\<^sub>R,[Tock]\<^sub>E] @ t \<in> P"
  shows "s @ [[X\<union>{e. e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R,[Tock]\<^sub>E] @ t \<in> P"
proof -
  obtain Y where Y:"Y = {e::'a ttevent. e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}"
    by auto
  then have "Y \<inter> {e. (e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<in> P) \<or> (e = Tock \<and> s @ [[X]\<^sub>R, [e]\<^sub>E] \<in> P) } = {}"
    by auto
  then have "s @ [[X\<union>{e. e = Tock \<and> s @ [[X]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R,[Tock]\<^sub>E] @ t \<in> P"
    using assms
    by (simp add: TT2_def inf_set_def)
  then show ?thesis .
qed

lemma TT2w_union_RefTock_ext_imp':
  assumes "TT(P)" "TT2(P)" "TT4(P)" "s @ [[X]\<^sub>R] @ t \<in> P"
  shows "s @ [[X\<union>{Tick}\<union>{e. e = Tock \<and> s @ [[X\<union>{Tick}]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R] @ t \<in> P"
proof -
  obtain J where J:"J = X\<union>{Tick}" by auto 
  then have "s @ [[J]\<^sub>R] @ t \<in> P"
    using TT4_middle_Ref_with_Tick TT_TT1 assms(1) assms(3) assms(4) by blast
  then have "s @ [[J\<union>{e. e = Tock \<and> s @ [[J]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R] @ t \<in> P"
    using TT2w_union_RefTock_ext_imp assms by auto
  then show ?thesis using J by auto
qed

lemma TT2_addRefTickTock_ext_imp:
  assumes "TT(P)" "TT2(P)" "TT4(P)" "s @ [[X]\<^sub>R] @ t \<in> P"
  shows "s @ [[refTickTock X s P]\<^sub>R] @ t \<in> P"
proof -
  have "s @ [[X\<union>{Tick}]\<^sub>R] @ t \<in> P"
    using TT4_middle_Ref_with_Tick TT_TT1 assms(1) assms(3) assms(4) by blast
  then have "s @ [[X\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> P \<and> z \<noteq> Tock)}]\<^sub>R] @ t \<in> P"
    using TT2w_union_Ref_ext_imp assms by blast
  then have "s @ [[X\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> P \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[X\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> P \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> P}]\<^sub>R] @ t \<in> P"
    using TT2w_union_RefTock_ext_imp assms by blast
  then have "s @ [[refTickTock X s P]\<^sub>R] @ t \<in> P"
    unfolding refTickTock_def by auto
  then show ?thesis .
qed

lemma TT2_addRefTickTock_subset_imp:
  assumes "TT1(P)" "s @ [[refTickTock X s P]\<^sub>R] @ t \<in> P" 
  shows "s @ [[X]\<^sub>R] @ t \<in> P"
proof -
  have "X \<subseteq> refTickTock X s P"
    unfolding refTickTock_def by auto
  then show ?thesis
    by (metis TT1_def append.left_neutral append_Cons assms(1) assms(2) tt_prefix_common_concat tt_prefix_subset.simps(2) tt_prefix_subset_refl)
qed

lemma addRefTickTock_in:
  assumes "TT(P)" "TT2(P)" "TT4(P)" "i @ ys \<in> P"
  shows "i @ (addRefTickTock ys i P) \<in> P"
  using assms proof (induct ys i P rule:addRefTickTock.induct)
  case (1 s Q)
  then show ?case by auto
  next
    case (2 e t s Q)
    then show ?case by auto
  next
    case (3 X t s Q)
    then have "(s @ [[X]\<^sub>R]) @ t \<in> Q"
      by auto
    then have "s @ [[X]\<^sub>R] @ (addRefTickTock t (s @ [[X]\<^sub>R]) Q) \<in> Q"
      using 3 by auto
    then have "s @ [[refTickTock X s Q]\<^sub>R] @ (addRefTickTock t (s @ [[X]\<^sub>R]) Q) \<in> Q" 
      using TT2_addRefTickTock_ext_imp assms 3 by auto
    then have "(s @ addRefTickTock ([X]\<^sub>R # t) s Q) \<in> Q"
      by auto
    then show ?case by auto
  qed
(*
proof (induct ys rule:rev_induct)
  case Nil
  then show ?case 
    by auto
next
  case (snoc x xs)
  then have addRefTickTock_xs_in_P:"i @ addRefTickTock xs i P \<in> P"
    by (metis TT1_def TT_TT1 append.assoc tt_prefix_concat tt_prefix_imp_prefix_subset)
  then show ?case
  proof (cases x)
    case (ObsEvent x1)
    then have "addRefTickTock (xs @ [x]) i P = (addRefTickTock xs i P) @ [x]"
      using addRefTickTock_concat_event snoc by blast
    then show ?thesis using snoc
  next
    case (Ref x2)
    then show ?thesis sorry
  qed
qed
  *)

lemma prirefTT13_imp_prirefTT13_refTickTock:
  assumes "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "prirefTT13 pa Sa (s @ [[Saa]\<^sub>R] @ sa) Q \<subseteq> prirefTT13 pa Sa (s @ [[refTickTock Saa s Q]\<^sub>R] @ sa) Q"
  using assms unfolding prirefTT13_def apply auto
  using TT2_addRefTickTock_ext_imp by fastforce+

lemma prirefTT13_refTickTock_imp_prirefTT13:
  assumes "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "prirefTT13 pa Sa (s @ [[refTickTock Saa s Q]\<^sub>R] @ sa) Q \<subseteq> prirefTT13 pa Sa (s @ [[Saa]\<^sub>R] @ sa) Q "
  using assms unfolding prirefTT13_def apply auto
  using TT2_addRefTickTock_subset_imp TT_TT1 by fastforce+

lemma prirefTT13_eq_prirefTT13_refTickTock:
  assumes "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "prirefTT13 pa Sa (s @ [[Saa]\<^sub>R] @ sa) Q = prirefTT13 pa Sa (s @ [[refTickTock Saa s Q]\<^sub>R] @ sa) Q"
  using assms prirefTT13_imp_prirefTT13_refTickTock prirefTT13_refTickTock_imp_prirefTT13 by blast

lemma Tock_notin_prirefTT1_imp_notin_prirefTT13_refTickTock:
  assumes "Tock \<notin> prirefTT13 pa Sa (s @ [Saa]\<^sub>R # sa) Q" "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "Tock \<notin> prirefTT13 pa Sa (s @ [refTickTock Saa s Q]\<^sub>R # sa) Q"
  using assms prirefTT13_eq_prirefTT13_refTickTock by fastforce

lemma prirelRef3_trace_refTickTock:
  assumes "prirelRef3 p xs ys (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q" "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "prirelRef3 p xs ys (s @ [[refTickTock S s Q]\<^sub>R, [Tock]\<^sub>E]) Q"
  using assms apply (induct p xs ys _ Q arbitrary:S  rule:prirelRef3.induct, auto)
  using prirefTT13_eq_prirefTT13_refTickTock apply fastforce
  using prirefTT13_eq_prirefTT13_refTickTock apply fastforce
  using prirefTT13_eq_prirefTT13_refTickTock apply fastforce
  by (metis TT2_addRefTickTock_ext_imp append_Cons append_Nil prirefTT13_eq_prirefTT13_refTickTock)

lemma prirelRef2_imp_prirelRef3:
  assumes "prirelRef2 p xs ys i P" "TT(P)" "TT2(P)" "TT4(P)"
  shows "prirelRef3 p xs (addRefTickTock ys i P) i P"
  using assms proof (induct p xs ys _ P rule:prirelRef3.induct, auto)
  fix pa S s Q x
  fix R::"'a ttevent set" 
  assume assms: "R \<subseteq> prirefTT1 pa S s Q"
         "TT Q" "TT2 Q" "TT4 Q"
         "x \<in> R"
  show "x \<in> prirefTT13 pa (refTickTock S s Q) s Q"
    using assms prirefTT1_imp_prirefTT13_noassm by blast
next
  fix pa aa S zz s Q x
  fix R::"'a ttevent set" 
  assume assms: "prirelRef3 pa aa (addRefTickTock zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
          "R \<subseteq> prirefTT1 pa S s Q"
          "Tock \<notin> prirefTT1 pa S s Q"
         "TT Q" "TT2 Q" "TT4 Q"
         "x \<in> R"
  show "x \<in> prirefTT13 pa (refTickTock S s Q) s Q"
    using assms prirefTT1_imp_prirefTT13_noassm by blast
next
  fix pa aa S zz s Q
  fix R::"'a ttevent set" 
  assume assms: "prirelRef3 pa aa (addRefTickTock zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
          "R \<subseteq> prirefTT1 pa S s Q"
          "Tock \<notin> prirefTT1 pa S s Q"
         "TT Q" "TT2 Q" "TT4 Q"
          "Tock \<in> prirefTT13 pa (refTickTock S s Q) s Q"
  have "Tock \<notin> prirefTT13 pa (refTickTock S s Q) s Q"
    using assms Tock_notin_prirefTT1_imp_notin_prirefTT13 by blast
  then show "False"
    using assms by auto
next
  fix pa aa S zz s Q
  fix R::"'a ttevent set" 
  assume assms: "prirelRef3 pa aa (addRefTickTock zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
          "R \<subseteq> prirefTT1 pa S s Q"
          "Tock \<notin> prirefTT1 pa S s Q"
         "TT Q" "TT2 Q" "TT4 Q"
  then show "prirelRef3 pa aa (addRefTickTock zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (s @ [[refTickTock S s Q]\<^sub>R, [Tock]\<^sub>E]) Q"
    using prirelRef3_trace_refTickTock
    by blast
next
  fix pa aa e\<^sub>2 zz s Q
  fix Z::"'a ttevent set" 
  assume assms: 
      "prirelRef3 pa aa (addRefTickTock zz (s @ [[e\<^sub>2]\<^sub>E]) Q) (s @ [[e\<^sub>2]\<^sub>E]) Q"
      "TT Q"
      "TT2 Q"
      "TT4 Q"
      "prirelRef2 pa aa zz (s @ [[e\<^sub>2]\<^sub>E]) Q"
      "s @ [[Z]\<^sub>R] \<in> Q"
      "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q"
      "Tick \<in> Z"
      "e\<^sub>2 \<notin> Z" "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b" "Tock \<in> Z" "\<forall>Z. s @ [[Z]\<^sub>R] \<in> Q \<longrightarrow> e\<^sub>2 = Tick \<or> e\<^sub>2 \<in> prirefTT13 pa Z s Q"
  then have "prirelRef2 pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q"
    by auto
  then show "maximal(pa,e\<^sub>2)"
  proof (cases "s @ [[e\<^sub>2]\<^sub>E] \<in> Q")
    case True
    then show ?thesis
      proof (cases "e\<^sub>2 = Tick")
        case True
        then show ?thesis 
          using assms(8) assms(9) by blast
      next
        case False
        then show ?thesis
          by (smt TT3_any_cons_end_tock TT_TT3 True assms(10) assms(11) assms(12) assms(2) assms(6) assms(9) mem_Collect_eq prirefTT13_subset_prirefTT1 prirefTT1_def subsetCE)
      qed
        case True
  next
    case False
    then show ?thesis
      using assms(11) assms(7) assms(9) by blast
  qed
next
  fix pa aa e\<^sub>2 zz s Q
  fix Z::"'a ttevent set" 
  assume assms: 
      "prirelRef3 pa aa (addRefTickTock zz (s @ [[e\<^sub>2]\<^sub>E]) Q) (s @ [[e\<^sub>2]\<^sub>E]) Q"
      "TT Q"
      "TT2 Q"
      "TT4 Q"
      "prirelRef2 pa aa zz (s @ [[e\<^sub>2]\<^sub>E]) Q"
      "s @ [[Z]\<^sub>R] \<in> Q"
      "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q"
      "Tick \<in> Z"
      "e\<^sub>2 \<notin> Z" "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b" "s @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<forall>Z. s @ [[Z]\<^sub>R] \<in> Q \<longrightarrow> e\<^sub>2 = Tick \<or> e\<^sub>2 \<in> prirefTT13 pa Z s Q"
  then show "maximal(pa,e\<^sub>2)"
    by (smt TT3_any_cons_end_tock TT_TT3 Un_iff mem_Collect_eq prirefTT13_def)
qed 

lemma Tock_notin_prirefTT13_imp_notin_prirefTT1:
  assumes "Tock \<notin> prirefTT13 pa S s Q" "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
  shows "Tock \<notin> prirefTT1 pa S s Q"
  using assms unfolding prirefTT1_def prirefTT13_def by auto

lemma xx1:
  assumes
  "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q
      \<and> (\<forall>e. (e \<notin> Z \<and> e \<noteq> Tock) \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q)
      \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z
      \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))" "TT3(Q)"
  shows "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT13 p Z s Q)"
  using assms apply auto
  unfolding prirefTT13_def apply auto
  using TT3_any_cons_end_tock by blast+

lemma prirelRef3_imp_prirelRef2:
  assumes "prirelRef3 p xs ys i P" "TT(P)" "TT2(P)" "TT4(P)" "i @ ys \<in> P"
  shows "prirelRef2 p xs ys i P"
  using assms proof (induct p xs ys i P rule:prirelRef2.induct, auto)
  fix pa S s Q x
  fix R::"'a ttevent set" 
  assume "R \<subseteq> prirefTT13 pa S s Q"
       "TT Q"
       "TT2 Q"
       "TT4 Q" "s @ [[S]\<^sub>R] \<in> Q" "x \<in> R"
  then show "x \<in> prirefTT1 pa S s Q"
    using TT_TT3 prirefTT13_imp_prirefTT1 by blast
next
  fix pa aa S zz s Q x
  fix R::"'a ttevent set" 
  assume "prirelRef2 pa aa zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
       "TT Q"
       "TT2 Q"
       "TT4 Q"
       "s @ [S]\<^sub>R # [Tock]\<^sub>E # zz \<in> Q"
       "R \<subseteq> prirefTT13 pa S s Q" "x \<in> R"
  then show "x \<in> prirefTT1 pa S s Q"
    using TT_TT3 prirefTT13_imp_prirefTT1 by blast
next
  fix pa aa zz s Q
  fix S R::"'a ttevent set" 
  assume assm:"prirelRef2 pa aa zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
       "TT Q"
       "TT2 Q"
       "TT4 Q"
       "s @ [S]\<^sub>R # [Tock]\<^sub>E # zz \<in> Q"
       "Tock \<notin> prirefTT13 pa S s Q"
       "Tock \<in> prirefTT1 pa S s Q"
  then have "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<lesssim>\<^sub>C s @ [S]\<^sub>R # [Tock]\<^sub>E # zz"
    by (metis Cons_eq_appendI append_eq_appendI self_append_conv2 tt_prefix_subset_front tt_prefix_subset_refl)
  then have "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
    using assm TT1_def TT_TT1 by blast
  then have "Tock \<notin> prirefTT1 pa S s Q"
    using assm Tock_notin_prirefTT13_imp_notin_prirefTT1 by blast
  then show "False"
    using assm by auto
next
  fix pa aa zz s Q
  fix e\<^sub>2::"'a ttevent"
  fix Z::"'a ttevent set" 
  assume assms:
    "prirelRef2 pa aa zz (s @ [[e\<^sub>2]\<^sub>E]) Q"
    "TT Q"
    "TT2 Q"
    "TT4 Q"
    "s @ [e\<^sub>2]\<^sub>E # zz \<in> Q"
    "prirelRef3 pa aa zz (s @ [[e\<^sub>2]\<^sub>E]) Q"
    "s @ [[Z]\<^sub>R] \<in> Q"
    "e\<^sub>2 \<noteq> Tick" "e\<^sub>2 \<notin> prirefTT13 pa Z s Q"
    "\<forall>Z. Tick \<in> Z \<longrightarrow> 
      s @ [[Z]\<^sub>R] \<in> Q \<longrightarrow> 
        (\<exists>e. e \<notin> Z \<and> e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q) \<or> Tock \<notin> Z \<and> s @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<or> e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)"
  then have s_e2_in:"s @ [[e\<^sub>2]\<^sub>E] \<in> Q"
    by (meson TT1_def TT_TT1 tt_prefix_common_concat tt_prefix_subset.simps(1) tt_prefix_subset.simps(3))
  then show "maximal(pa,e\<^sub>2)"
  proof (cases e\<^sub>2)
    case (Event x1)
    have a:"s @ [[refTickTock Z s Q]\<^sub>R] \<in> Q"
      by (simp add: assms(2) assms(3) assms(4) assms(7) prirefTT1_imp_prirefTT13'')
    have b:"Tick \<in> refTickTock Z s Q"
      unfolding refTickTock_def by auto
    have c:"\<not>(\<exists>e. e \<notin> refTickTock Z s Q \<and> e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q)"
      using refTickTock_def by fastforce
    have d:"(Tock \<in> refTickTock Z s Q \<or> s @ [[refTickTock Z s Q]\<^sub>R, [Tock]\<^sub>E] \<in> Q)"
      by (simp add: refTickTock_def)
    have e:"Event x1 \<notin> refTickTock Z s Q"
      using s_e2_in assms 
      by (simp add: Event prirefTT13_def refTickTock_def)
    have f:"\<not> (\<exists>b. b \<notin> refTickTock Z s Q \<and> e\<^sub>2 <\<^sup>*pa b)" (* TODO: ugly proof steps, redo *)
      unfolding refTickTock_def apply auto
      using assms apply (smt UnCI mem_Collect_eq prirefTT13_def)
      using assms apply (smt TT_TTwf TTwf_Refusal_imp_no_Tock UnCI mem_Collect_eq prirefTT13_def)
      using assms by (metis (mono_tags, lifting) TT1_Ref_Tock_subset_imp TT_TT1 UnCI Un_insert_right mem_Collect_eq prirefTT13_def)
    then show ?thesis using a b c d e f
      using Event assms(10) by blast
  next
    case Tock
    then show ?thesis 
    using TT_TTwf TTwf_Refusal_imp_no_Tock s_e2_in assms(2) assms(7) by auto
  next
    case Tick
    then show ?thesis using assms(8) by blast
  qed
qed

lemma priTT3_eq_priTT:
  assumes "TT(P)" "TT2(P)" "TT4(P)"
  shows "priTT3 p P = priTT p P"
  using assms unfolding priTT3_def priTT_def apply auto
  using prirelRef3_imp_prirelRef2 apply fastforce
  by (metis addRefTickTock_in append_Nil prirelRef2_imp_prirelRef3)

lemma
  assumes "sa @ [[S]\<^sub>R] \<in> Q" "b \<notin> S" "sa @ [[b]\<^sub>E] \<in> Q" "z <\<^sup>*pa b" "TTwf(Q)" 
  shows "\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b"
  
proof (cases b)
  case (Event x1)
  then show ?thesis
    using assms(2) assms(3) assms(4) by blast
next
  case Tock
  then show ?thesis using assms
    using TTwf_Refusal_imp_no_Tock by blast
next
  case Tick
  then show ?thesis nitpick
qed

lemma
  assumes "\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa b" "sa @ [[X]\<^sub>R] \<in> Q"
  shows "\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b"
  using assms apply auto

lemma
  assumes "s @ [[Z]\<^sub>R] \<in> Q" "TTwf Q" "e\<^sub>2 \<noteq> Tock"
          "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q"
          "Tick \<in> Z" "e\<^sub>2 \<notin> Z" "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*p b" "Tock \<in> Z" 
   shows "\<not> (\<forall>Z. Z = prirefTT13 p Z s Q \<longrightarrow> s @ [[Z]\<^sub>R] \<in> Q \<longrightarrow> e\<^sub>2 \<in> Z)"
  using assms nitpick



lemma not_Tock_notin_refTickTock_imp_possible [elim]:
  assumes "s @ [[Z]\<^sub>R] \<in> Q" "TT2(Q)" "TT4(Q)" "e \<noteq> Tock"
          "e \<notin> refTickTock Z s Q"
    shows "s @ [[e]\<^sub>E] \<in> Q"
  using assms unfolding refTickTock_def by auto

lemma Tock_notin_refTickTock_imp_possible [elim]:
  assumes "s @ [[Z]\<^sub>R] \<in> Q" "TT(Q)" "TT2(Q)" "TT4(Q)"
          "Tock \<notin> refTickTock Z s Q"
    shows "s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
  using assms unfolding refTickTock_def apply auto
  using TT1_Ref_Tock_subset_imp' TT_TT1 by blast

lemma
  assumes "s @ [[Z]\<^sub>R] \<in> Q"
  shows "prirefTT13 p Z s Q \<subseteq> refTickTock Z s Q " nitpick
  using assms unfolding refTickTock_def prirefTT13_def apply auto

lemma
  "e\<^sub>2 \<noteq> Tock \<Longrightarrow>Tick \<in> Z  \<Longrightarrow> s @ [[e\<^sub>2]\<^sub>E] \<in> Q \<Longrightarrow> s @ [[Z]\<^sub>R] \<in> Q \<Longrightarrow> e\<^sub>2 \<notin> Z \<Longrightarrow> e\<^sub>2 \<notin> prirefTT13 p Z s Q \<Longrightarrow> e\<^sub>2 \<in> refTickTock Z s Q \<Longrightarrow> False"
  unfolding refTickTock_def prirefTT13_def by auto

lemma
  "TT(Q)  \<Longrightarrow> Tick \<in> Z  \<Longrightarrow> s @ [[Z]\<^sub>R] \<in> Q  \<Longrightarrow> e\<^sub>2 \<notin> prirefTT13 p Z s Q \<Longrightarrow> b \<notin> refTickTock Z s Q \<Longrightarrow> e\<^sub>2 <\<^sup>*p b \<Longrightarrow> False"
  unfolding refTickTock_def prirefTT13_def apply auto
  
  using TT_TTwf TTwf_Refusal_imp_no_Tock apply blast
  using TT1_Ref_Tock_subset_imp' TT_TT1 by blast

lemma xx2:
  assumes "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT13 p Z s Q)" "TT(Q)" "TT3(Q)" "TT2(Q)" "TT4(Q)" "s @ [[e\<^sub>2]\<^sub>E] \<in> Q" 
  shows   "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q
      \<and> (\<forall>e. (e \<notin> Z \<and> e \<noteq> Tock) \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q)
      \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z
      \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))" 
  using assms apply auto
  apply (rule_tac x="refTickTock Z s Q" in exI, auto)
  
     apply (simp add: refTickTock_def)
    apply (simp add: refTickTock_def)
    unfolding refTickTock_def prirefTT13_def apply auto
    using TT_TTwf TTwf_Refusal_imp_no_Tock apply blast
  using TT_TTwf TTwf_Refusal_imp_no_Tock apply blast
  using TT1_Ref_Tock_subset_imp' TT_TT1 by blast+

lemma
  assumes "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT13 p Z s Q)" "TT(Q)" "TT3(Q)" "TT2(Q)" "TT4(Q)" "s @ [[e\<^sub>2]\<^sub>E] \<in> Q" 
  shows "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> Tick \<in> Z \<and> e\<^sub>2 \<notin> prirefTT13 p Z s Q)"
  using assms apply auto
  apply (rule_tac x="Z \<union> {Tick}" in exI, auto)
  using TT4_TT1_add_Tick TT_TT1 apply fastforce
  unfolding refTickTock_def prirefTT13_def apply auto
  using TT1_Ref_Tock_subset_imp' TT_TT1 by blast

fun prirelRef4 :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> bool" where
"prirelRef4 p [] [] s Q = True" |
"prirelRef4 p [[R]\<^sub>R] [[S]\<^sub>R] s Q = (R \<subseteq> prirefTT13 p S s Q)" |
"prirelRef4 p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) s Q =
   ((R \<subseteq> prirefTT13 p S s Q) \<and> Tock \<notin> prirefTT13 p S s Q \<and> prirelRef4 p aa zz (s @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"prirelRef4 p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> prirelRef4 p aa zz (s @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT13 p Z s Q)))" |
"prirelRef4 p x y s Q = False"

definition priTT4w :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttobs) list set" where
"priTT4w p P = {\<rho>|\<rho> s. prirelRef4 p \<rho> s [] P \<and> s \<in> P}"

lemma prirelRef4_eq_length [intro]:
  assumes "prirelRef4 p xs ys i P"
  shows "List.length xs = List.length ys"
  using assms by (induct p xs ys i P rule:prirelRef4.induct, auto)

lemma prirelRef4_imp_prirelRef3:
  assumes "prirelRef4 p xs ys i P" "TT(P)" "TT2(P)" "TT4(P)" "i @ ys \<in> P"
  shows "prirelRef3 p xs ys i P"
  using assms apply (induct p xs ys i P rule:prirelRef3.induct, auto)
  using xx2 
  by (smt TT1_def TT_TT1 TT_TT3 append.assoc append_Cons append_Nil2 append_eq_append_conv2 append_self_conv2 same_append_eq tt_prefix_concat tt_prefix_imp_prefix_subset xx2)
  by (smt TT1_def TT_TT1 TT_TT3 append.assoc append_Cons append_Nil2 append_eq_append_conv2 append_self_conv2 same_append_eq tt_prefix_concat tt_prefix_imp_prefix_subset xx2)

lemma prirelRef4_imp_prirelRef4:
  assumes "prirelRef3 p xs ys i P" "TT(P)" "TT2(P)" "TT4(P)"
  shows "prirelRef4 p xs ys i P"
  using assms apply (induct p xs ys i P rule:prirelRef3.induct, auto)
  by (metis TT_TT3 xx1)+

lemma priTT4w_eq_priTT3:
  assumes "TT(P)" "TT2(P)" "TT4(P)"
  shows "priTT4w p P = priTT3 p P"
  using assms unfolding priTT4w_def priTT3_def apply auto
  using prirelRef3_imp_prirelRef2 apply fastforce
  by (metis addRefTickTock_in append_Nil prirelRef2_imp_prirelRef3)

lemma
  
  shows
  "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q
      \<and> (\<forall>e. (e \<notin> Z \<and> e \<noteq> Tock) \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q)
      \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z
      \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
  =
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<notin> prirefTT13 p Z s Q)"
 
  apply auto  
    apply (case_tac "s @ [[e\<^sub>2]\<^sub>E] \<in> Q")
  

lemma
  assumes "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows
  "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q
      \<and> (\<forall>e. (e \<notin> Z \<and> e \<noteq> Tock) \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q)
      \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z
      \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))
  =
  (\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q
      
      \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))"
  using assms 
  apply auto
  apply (rule_tac x="refTickTock Z s Q" in exI, auto)
       apply (simp add: prirefTT1_imp_prirefTT13)
      apply (simp add:refTickTock_def)
     apply (simp add:refTickTock_def)
    apply (simp add:refTickTock_def)
 apply (simp add:refTickTock_def)
sledgehammer
  using TT2_addRefTickTock_ext_imp apply fastforce
  using prirefTT1_imp_prirefTT13'' apply fastforce+
  apply (smt Collect_cong TT2w_union_Ref_Tock_imp TT2w_union_Ref_imp TT_TT2w Un_insert_right insert_subset refTickTock_def subset_antisym sup_bot.comm_neutral sup_ge1) 

lemma prirefTT1_subseteq_prirefTT1_refTickTock:
  assumes "TT(P)" "TT2(P)" "TT4(P)"
  shows "prirefTT1 pa X s P \<subseteq> prirefTT1 pa (refTickTock X s P) s P"
  using assms unfolding prirefTT1_def refTickTock_def
  
  apply auto
  apply safe
  
  apply (meson TT1_Ref_Tock_subset_imp TT_TT1)+
  sorry
  (*apply (smt Collect_cong Collect_empty_eq TT2_union_Ref_Tock_imp TT4_TT1_imp_Ref_Tock TT_TT1 Un_assoc Un_commute insert_is_Un)*)
lemma 
  assumes "prirelRef2 p xs (i@ys) i P" "TT(P)" "TT2(P)" "TT4(P)"  "i = []"
  shows "prirelRef2 p xs (addRefTickTock (i@ys) i P) i P"
  using assms apply (induct p xs ys i P rule:prirelRef2.induct, simp_all)
  using prirefTT1_subseteq_prirefTT1_refTickTock apply blast
using prirefTT1_subseteq_prirefTT1_refTickTock
  oops

lemma 
  assumes "prirelRef2 p xs ys [] P" "TT(P)" "TT2(P)" "TT4(P)" "ys \<in> P"
  shows "prirelRef3 p xs (addRefTickTock ys [] P) [] P"
using assms
proof (induct xs ys rule:rev_induct_eq_length)
  case 1
  then show ?case using assms by auto
next
  case 2
  then show ?case using assms 
    by (simp add: TT_empty)
next
  case (3 x y xs ys)
  then show ?case
  proof (induct xs ys rule:rev_induct_eq_length)
    case 1
    then show ?case using 3 by auto
  next
    case 2
    then show ?case using 3
      apply(cases y, auto, cases x, auto, cases x, auto)
      by (metis append_Nil prirefTT1_imp_prirefTT13' subsetCE)
  next
  case (3 z s xs ys)
  then show ?case sorry
qed
    proof (cases y)
      case (ObsEvent x1)
      then show ?thesis using 3 apply(cases x, auto)
    next
      case (Ref x2)
      then show ?thesis sorry
    qed
lemma 
  assumes "prirelRef2 p xs (i@ys) i P" "TT(P)" "TT2(P)" "TT4(P)" "(i@ys) \<in> P" "i = []"
  shows "prirelRef3 p xs (addRefTickTock (i@ys) i P) i P"
  using assms proof (induct p xs ys i P rule:prirelRef2.induct, simp_all)
  fix pa 
  fix R S::"'a ttevent set" 
  fix s::"'a ttobs list"
  fix Q
  assume assm0:"R \<subseteq> prirefTT1 pa S [] Q"
   and    assm1:"TT Q"
   and    assm2:"TT2 Q"
   and    assm3:"TT4 Q"
   and    assm4:"[[S]\<^sub>R] \<in> Q"
   and    assm5:"s = []"
  have "s @ [[S]\<^sub>R] \<in> Q"
    using assm4 assm5 by auto
  then have "prirefTT1 pa S [] Q \<subseteq> prirefTT13 pa (refTickTock S [] Q) [] Q"
    using assm0 assm1 assm2 assm3 assm4 assm5 prirefTT1_imp_prirefTT13' by blast
  then show "R \<subseteq> prirefTT13 pa (refTickTock S [] Q) [] Q"
    using assm0 by auto
next
  oops

lemma
  assumes "prirelRef2 p xs ys i P" "TT(P)" "TT2(P)" "TT4(P)" "i @ ys \<in> P"
  shows "prirelRef3 p xs (addRefTickTock ys i P) i P \<and> (addRefTickTock ys i P) \<in> P"
  using assms
proof (induct xs ys arbitrary:i rule:rev_induct_eq_length)
  case 1
  then show ?case using assms by auto
next
  case 2
  then show ?case using assms 
    by (simp add: TT_empty)
next
  case (3 x y xs ys)
  then show ?case
  proof (induct xs ys rule:rev_induct_eq_length)
    case 1
    then show ?case using 3 by auto
  next
    case 2
    then show ?case using 3
    proof (cases y)
      case (ObsEvent x1)
      then show ?thesis using 3 apply(cases x, auto)
    next
      case (Ref x2)
      then show ?thesis sorry
    qed
      apply (cases x, auto)
         apply (cases y, auto)
        apply (cases y, auto)
    proof (cases y)
      case (ObsEvent x1)
      then show ?thesis using 2 
        apply auto
        by (rule_tac x="[y]" in exI, auto, cases y, auto, cases x, auto simp add:tt_prefix_subset_refl)
    next
      case (Ref x2)
      have x2_less:"i @ [[x2]\<^sub>R] \<lesssim>\<^sub>C i @ [[refTickTock x2 i P]\<^sub>R]"
        by (metis (no_types, lifting) Un_assoc sup_ge1 tt_prefix_common_concat tt_prefix_subset.simps(2) tt_prefix_subset_refl)
      then show ?thesis using Ref 2
      proof (cases y)
        case (ObsEvent y1)
        then show ?thesis using Ref 2 by auto
      next
        case Refy2:(Ref y2)
        then show ?thesis using Ref 2
        proof (cases x)
          case (ObsEvent x1)
          then show ?thesis using Ref 2 by auto
        next
          case Refx2:(Ref z2)
          then have "i @ [[x2]\<^sub>R] \<in> P"
            using "2.prems"(7) Ref by auto
          then have preirel_imp:"prirefTT1 p x2 i P \<subseteq> prirefTT13 p (refTickTock x2 i P) i P \<and> i @ [[refTickTock x2 i P]\<^sub>R] \<in> P"
            using prirefTT1_imp_prirefTT13 assms by blast
          then show ?thesis using Refx2 Ref 2 apply auto
            apply (rule_tac x="[[refTickTock x2 i P]\<^sub>R]" in exI)
            using preirel_imp x2_less by auto
        qed
      qed
    qed
  next
    case (3 z w xs ys)
    then have "ttWF (i @ ys)" "ttWF (i @ (ys @ [w]))"
      by (metis TT_wf append.assoc ttWF_prefix_is_ttWF)+
 (*   then have "prirelRef2 p ([z]@[x]) ([w]@[y]) (i @ ys) P"
      *)
    then show ?case using 3
    proof (cases y)
      case y:(ObsEvent x1)
      then show ?thesis using 3 
      proof (cases x1)
        case (Event e1)
        then have "ttWF [y]"
          by (simp add: y)
        then have "prirelRef2 p (xs @ [z]) (ys @ [w]) i P"
          using 3 prirelRef2_concat_both_imp by blast
        then have "\<exists>zs. prirelRef3 p (xs @ [z]) zs i P \<and> i @ zs \<in> P"
          using 3 TT1_def TT_TT1 tt_prefix_common_concat tt_prefix_concat tt_prefix_imp_prefix_subset by blast
        then show ?thesis using 3 y sorry
      next
        case Tock
        then show ?thesis sorry
      next
        case Tick
        then show ?thesis sorry
      qed
        apply auto
        apply (cases x, auto)
         apply (rule_tac x="ys @ [w, y]" in exI, auto)
        apply (cases w, auto, cases y, auto)
        
    next
      case (Ref x2)
      then show ?thesis sorry
    qed
      apply (cases x, auto, cases z, auto, cases w, auto)
      
qed
  
qed
  
  

lemma
  assumes "prirelRef3 p xs ys i P" "TT(P)" "i @ ys \<in> P"
  shows "prirelRef2 p xs ys i P"
  using assms
proof (induct xs ys arbitrary:i rule:rev_induct_eq_length)
  case 1
  then show ?case using assms by auto
next
  case 2
  then show ?case using assms by auto
next
  case (3 x y xs ys)
  then show ?case
  proof (induct xs ys arbitrary:i rule:rev_induct_eq_length)
    case 1
    then show ?case using 3 assms by auto
  next
    case 2
    then show ?case
      apply (cases x, auto, cases y, auto, cases y, auto)
      using TT_TT3 prirefTT13_imp_prirefTT1 by blast
  next
    case (3 s t ss ts)
    then show ?case
    
    proof (cases x)
      case (ObsEvent x1)
      then show ?thesis sorry
    next
      case (Ref x2)
      then show ?thesis sorry
    qed
      apply (cases x, auto, cases y, auto, cases y, auto)
        apply (cases s, auto, cases t, auto)
      sledgehammer
  qed
qed
  apply (case_tac x, auto, case_tac y, auto)
  sledgehammer
  apply (induct p xs ys i P rule:prirelRef2.induct, auto)
  using prirefTT13_imp_prirefTT1 TT_TT3 apply blast
  using prirefTT13_imp_prirefTT1 TT_TT3 apply blast
  

lemma
  fixes s :: "'a ttobs list"
  assumes "TT P" "prirelRef3 p x s i P" "s \<in> P" 
  shows "\<exists>s. prirelRef2 p x s i P \<and> s \<in> P"
  using assms 
proof (induct x s rule:rev_induct_eq_length)
case 1
  then show ?case 
    using assms(2) by blast  
next
  case 2
  then show ?case using prirelRef2.simps(1) by blast
next
  case (3 x y xs ys)
  then show ?case
  proof (cases x)
    case x1:(ObsEvent x1)
    then show ?thesis 
    proof (cases y)
      case y1:(ObsEvent y1)
      then have "\<exists>s. prirelRef2 p xs s i P \<and> s \<in> P"
        using x1 3 apply auto 
        by (meson TT1_def TT_TT1 prirelRef3_imp_concat_prirelRef3 tt_prefix_concat tt_prefix_imp_prefix_subset)
      
      assume "prirelRef2 p (xs @ [x]) (ys @ [y]) i P"
      then have "\<exists>s. prirelRef2 p (xs @ [x]) s i P \<and> s \<in> P"
        using 3 
        by blast
      then show ?thesis 
    next
      case (Ref y2)
      then show ?thesis sorry
    qed
  next
  case (Ref x2)
    then show ?thesis sorry
  qed
qed
  
  using prirelRef2.simps(1) apply blast

  apply (case_tac xa, case_tac y, auto)
  sledgehammer  
   apply (metis neq_Nil_conv prirelRef2.simps(1) prirelRef3.simps(28))
  apply (case_tac xa, auto)
end