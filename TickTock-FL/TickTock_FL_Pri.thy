theory TickTock_FL_Pri

imports
  TickTock_Max_TT1_Pri
begin

text \<open> This theory defines a simplified version of PriTT1, providing a definitive
       definition for Pri in TickTock. \<close>
(*
"prirefTT1 pa S sa Q = 
  {z. ((z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b))
        \<and>
       ((z \<notin> S \<and> sa @ [[z]\<^sub>E] \<in> Q \<and> z \<noteq> Tock \<and> z \<noteq> Tick) \<longrightarrow>
          ((sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock)
            \<or>
           (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)))}")*)

section \<open> Preliminaries \<close>

text \<open> To understand how the definition can be simplified, we establish some auxiliary results. \<close>

lemma "{z. (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}
        =
       {z. (z = Tock \<longrightarrow> (Q \<inter> {sa @ [[S]\<^sub>R, [Tock]\<^sub>E]}) \<subseteq> {x. (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)})}"
  by auto

lemma "{z. (z = Tock \<and> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q) \<longrightarrow> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}
        =
       {z. z \<noteq> Tock \<or> sa @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<or> (\<exists>b. b \<notin> S \<and> sa @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)}"
  by auto

text \<open> Namely, assuming Q is TT3-healthy allows for a significant simplification of prirefTT1. \<close>

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

(* TODO: Move to TickTock_Core? *)

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

section \<open> PriTT \<close>

definition prirefTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttevent) set \<Rightarrow> ('e ttevent) set" where
"prirefTT p \<sigma> Q S = 
  (S \<union> {e. (\<sigma> @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> e <\<^sup>*p Tock)} 
     \<union> {e. (\<exists>b. b \<notin> S \<and> \<sigma> @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> e <\<^sup>*p b)})"

fun priTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list \<Rightarrow> ('e ttobs) list set \<Rightarrow> bool" where
"priTT p [] [] \<sigma> Q = True" |
"priTT p [[R]\<^sub>R] [[S]\<^sub>R] \<sigma> Q = (R \<subseteq> prirefTT p \<sigma> Q S)" |
"priTT p ([R]\<^sub>R # [Tock]\<^sub>E # aa) ([S]\<^sub>R # [Tock]\<^sub>E # zz) \<sigma> Q =
   ((R \<subseteq> prirefTT p \<sigma> Q S) \<and> Tock \<notin> prirefTT p \<sigma> Q S \<and> priTT p aa zz (\<sigma> @ [[S]\<^sub>R,[Tock]\<^sub>E]) Q)" |
"priTT p ([e\<^sub>1]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) \<sigma> Q
 = 
 (e\<^sub>1 = e\<^sub>2 \<and> priTT p aa zz (\<sigma> @ [[e\<^sub>1]\<^sub>E]) Q \<and>
  (maximal(p,e\<^sub>2) 
   \<or> 
  (\<exists>Z. \<sigma> @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT p \<sigma> Q Z)))" |
"priTT p x y \<sigma> Q = False"

text \<open> Pretty syntax introduced below for convenience. \<close>

syntax 
  "_priTT" :: " ('e ttobs) list \<Rightarrow> 
                ('e ttevent) partialorder \<Rightarrow> 
                ('e ttobs) list \<Rightarrow> 
                ('e ttobs) list set \<Rightarrow>
                ('e ttobs) list \<Rightarrow> bool" ("_ priTT\<^sub>[\<^sub>_\<^sub>,\<^sub>_\<^sub>,\<^sub>_\<^sub>] _" [51,51,51,51,51])

translations
  "x priTT\<^sub>[\<^sub>p\<^sub>,\<^sub>\<sigma>\<^sub>,\<^sub>Q\<^sub>] y" == "CONST priTT p x y \<sigma> Q"

definition PriTT :: "('e ttevent) partialorder \<Rightarrow> ('e ttobs) list set \<Rightarrow> ('e ttobs) list set" where
"PriTT p P = {\<rho>|\<rho> s. priTT p \<rho> s [] P \<and> s \<in> P}"

(* 
lemma
  fixes s :: "'a ttobs list"
  assumes "x \<lesssim>\<^sub>C t" "TT P" "priTT p x s i P" "s \<in> P" 
  shows "\<exists>s. priTT1 p x s i P \<and> s \<lesssim>\<^sub>C x"
  using assms apply (induct p x s i P rule:priTT.induct, auto)
  
  using priTT1.simps(1) apply blast
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

lemma priTT_same_length [intro]:
  assumes "priTT p x s i P"
  shows "List.length x = List.length s"
  using assms by (induct p x s i P rule:priTT.induct, auto)

lemma List_length_cons_both_imp [intro]:
  assumes "List.length (xs @ [x]) = List.length (ys @ [y])"
  shows "List.length xs = List.length ys"
  using assms by (induct xs ys rule:rev_induct_eq_length, auto)

lemma priTT_imp_eq_events:
  assumes "priTT p (xs @ [[x]\<^sub>E]) (ys @ [[y]\<^sub>E]) i P"
  shows "x = y"
  using assms 
  apply (induct p xs ys i P rule:priTT.induct, auto)
  apply (metis priTT.simps(12) priTT.simps(80) priTT.simps(82) priTT.simps(9) ttevent.exhaust)
  using priTT_same_length by fastforce+

lemma priTT_imp_concat_priTT:
  assumes "priTT p (xs @ [[x1]\<^sub>E]) (ys @ [[x1a]\<^sub>E]) i P"
  shows "priTT p xs ys i P"
  using assms  
  apply (induct p xs ys i P rule:priTT.induct, auto)
  apply (metis (full_types) priTT.simps(12) priTT.simps(3) priTT.simps(80) priTT_imp_eq_events subsetCE ttevent.exhaust)
  using priTT_same_length by fastforce+

lemma prirefTT_imp_prirefTT1_aux:
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

lemma prirefTT_imp_prirefTT1:
  assumes "R \<subseteq> prirefTT pa s Q S" "TT3(Q)"
  shows "R \<subseteq> prirefTT1 pa S s Q"
  using assms unfolding prirefTT_def prirefTT1_def apply auto
  using prirefTT_imp_prirefTT1_aux by blast

lemma
  assumes "Tock \<notin> prirefTT pa s Q S" "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
  shows "Tock \<notin> prirefTT1 pa S s Q"
  using assms unfolding prirefTT_def prirefTT1_def by auto

lemma
  assumes "Tock \<in> prirefTT1 pa S s Q" "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
  shows "Tock \<in> prirefTT pa s Q S"
  using assms unfolding prirefTT_def prirefTT1_def by auto

lemma prirefTT_subset_prirefTT1:
  assumes "TT3(Q)"
  shows "prirefTT pa s Q S \<subseteq> prirefTT1 pa S s Q"
  using assms unfolding  prirefTT1_def prirefTT_def apply auto
  using prirefTT_imp_prirefTT1_aux by blast

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

text \<open> We define the following auxiliary definition, and function that inserts Tick in
       refusal sets. \<close>

definition "refTickTock S s Q == (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                                     \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"

fun addRefTickTock :: "'e ttobs list \<Rightarrow> 'e ttobs list \<Rightarrow> 'e ttobs list set \<Rightarrow> 'e ttobs list" where
  "addRefTickTock [] s Q = []" |
  "addRefTickTock ([e]\<^sub>E # t) s Q = [e]\<^sub>E # (addRefTickTock t (s @ [[e]\<^sub>E]) Q)" |
  "addRefTickTock ([X]\<^sub>R # t) s Q = [refTickTock X s Q]\<^sub>R # (addRefTickTock t (s @ [[X]\<^sub>R]) Q)"

text \<open> Crucially, we can then show that prirefTT1 is a subset of prirefTT when Tick
       is added to the refusal set, and furthermore such refusal set is also in Q because
       of TT4. \<close>

lemma prirefTT1_imp_prirefTT:
  assumes "TT(Q)" "TT4(Q)" "s @ [[S]\<^sub>R] \<in> Q" "TT2(Q)"
  shows "prirefTT1 pa S s Q \<subseteq> prirefTT pa s Q (refTickTock S s Q) \<and> s @ [[refTickTock S s Q]\<^sub>R] \<in> Q"
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

  have a:"S \<subseteq> prirefTT pa s Q S"
    unfolding prirefTT_def by auto

  have b:"{Tick} \<subseteq> prirefTT pa s Q (S\<union>{Tick})" "s @ [[S\<union>{Tick}]\<^sub>R] \<in> Q"
    unfolding prirefTT_def apply auto
    using assms TT4_middle_Ref_with_Tick TT_TT1 by fastforce

  have c:  "{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)} \<subseteq> prirefTT pa s Q  (S\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)})"
       and "s @ [[S\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R] \<in> Q"
       and "s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R] \<in> Q"
    unfolding prirefTT_def apply auto
    using assms apply (simp add: TT2w_union_Ref_imp TT_TT2w)
    using assms b TT2w_union_Ref_imp TT_TT2w by fastforce

  have d:  "{e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<subseteq> prirefTT pa s Q (S\<union>{e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
       and "s @ [[S\<union>{e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}]\<^sub>R] \<in> Q"
       and d1:"s @ [[J]\<^sub>R] \<in> Q"
    unfolding prirefTT_def apply auto
    using assms apply (simp add: TT2w_union_Ref_Tock_imp TT_TT2w)
    using assms c TT2w_union_Ref_Tock_imp TT_TT2w
    using \<open>s @ [[S \<union> {Tick} \<union> {z. s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock}]\<^sub>R] \<in> Q\<close> J by fastforce

  have a1:"S \<subseteq> prirefTT pa s Q  (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
    unfolding prirefTT_def by auto
  have a2:"{Tick} \<subseteq> prirefTT pa s Q (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
    unfolding prirefTT_def by auto
  have a3:"{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)} \<subseteq> prirefTT pa s Q (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
    unfolding prirefTT_def by auto
  have a4:"{e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} \<subseteq> prirefTT pa s Q (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}\<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
    unfolding prirefTT_def apply auto
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
        prirefTT pa  s Q (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                                  \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
    unfolding prirefTT_def using a5 by auto

  have a6: "{z. (\<exists>b. b \<notin> S \<and> s @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)} 
            \<subseteq> 
            prirefTT pa s Q J"
    unfolding prirefTT_def J by auto
(*
  have a5:"{z. s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock} 
            \<subseteq> 
            prirefTT pa (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                               \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q}) s Q"
    unfolding prirefTT_def apply auto
    using TT1_Ref_Tock_subset_imp' assms d1 apply auto oops*)

  have "S \<union> {z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)} \<union> {Tick}
              \<union> {e. e = Tock \<and> s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<notin> Q} 
              \<union> {z. s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q \<and> z <\<^sup>*pa Tock}
              \<union> {z. (\<exists>b. b \<notin> S \<and> s @ [[b]\<^sub>E] \<in> Q \<and> b \<noteq> Tock \<and> b \<noteq> Tick \<and> z <\<^sup>*pa b)} 
        \<subseteq> 
        prirefTT pa s Q (S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}
                                  \<union>{e. e = Tock \<and> s @ [[S\<union>{Tick}\<union>{z. (s @ [[z]\<^sub>E] \<notin> Q \<and> z \<noteq> Tock)}]\<^sub>R, [Tock]\<^sub>E] \<notin> Q})"
    using a1 a2 a3 a4 a51 a6 J by auto
  then have "prirefTT1 pa S s Q 
             \<subseteq> 
             prirefTT pa  s Q J"
    using prirefTT1_alt J by auto
  then have "prirefTT1 pa S s Q \<subseteq> prirefTT pa s Q J \<and> s @ [[J]\<^sub>R] \<in> Q"
    using d1 by blast
  then show ?thesis unfolding refTickTock_def using J by blast
qed

lemma prirefTT1_imp_prirefTT':
  assumes "TT(Q)" "TT4(Q)" "s @ [[S]\<^sub>R] \<in> Q" "TT2(Q)"
  shows "prirefTT1 pa S s Q \<subseteq> prirefTT pa s Q (refTickTock S s Q)"
  using assms prirefTT1_imp_prirefTT by blast

lemma prirefTT1_imp_prirefTT'' [intro]:
  assumes "TT(Q)" "TT4(Q)" "s @ [[S]\<^sub>R] \<in> Q" "TT2(Q)"
  shows "s @ [[refTickTock S s Q]\<^sub>R] \<in> Q"
  using assms prirefTT1_imp_prirefTT by blast

lemma TT1_Ref_Tock_imp_Ref [intro]:
  assumes "s @ [[S]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "TT1(Q)"
  shows "s @ [[S]\<^sub>R] \<in> Q"
  using assms
  by (meson TT1_def order_refl tt_prefix_subset.simps(1) tt_prefix_subset.simps(2) tt_prefix_subset_same_front)

lemma prirefTT1_imp_prirefTT_noassm:
  assumes "TT(Q)" "TT4(Q)" "TT2(Q)"
  shows "prirefTT1 pa S s Q \<subseteq> prirefTT pa s Q (refTickTock S s Q)"
proof (cases "s @ [[S]\<^sub>R] \<in> Q")
  case True
  then show ?thesis
    using assms(1) assms(2) assms(3) prirefTT1_imp_prirefTT by blast
next
  case False
  then show ?thesis
     unfolding prirefTT1_def prirefTT_def refTickTock_def apply simp_all
     using TT1_Ref_Tock_subset_imp' TT_TT1 assms(1) by blast
qed

lemma priTT_extend_both_events_eq_size_maximal_ttWF:
  assumes "priTT p xs ys s P" "ttWF (ys @ [[e\<^sub>1]\<^sub>E])" "maximal(p,e\<^sub>1)" "TT3_trace (ys @ [[e\<^sub>1]\<^sub>E])"
  shows "priTT p (xs @ [[e\<^sub>1]\<^sub>E]) (ys @ [[e\<^sub>1]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:priTT.induct, auto)
     apply (cases e\<^sub>1, auto)
  using TT3_trace_cons_imp_cons 
     apply (smt UnE mem_Collect_eq prirefTT_def some_higher_not_maximal)
  using TT3_trace_cons_imp_cons ttWF.elims(2) apply auto[1]
  by (metis TT3_trace_cons_imp_cons ttWF.simps(4) ttWF.simps(6) ttevent.exhaust)

lemma priTT_extend_both_Ref:
  assumes "priTT p xs ys s P" "ttWF (ys @ [[S]\<^sub>R])"  "TT3_trace (ys @ [[S]\<^sub>R])" "R \<subseteq> prirefTT p (s @ ys) P S"
  shows "priTT p (xs @ [[R]\<^sub>R]) (ys @ [[S]\<^sub>R]) s P"
  using assms apply (induct p xs ys s P rule:priTT.induct, auto)
  by (metis TT3_trace_cons_imp_cons append_Nil list.exhaust ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttWF_prefix_is_ttWF ttevent.exhaust)+

lemma prirelRef_extend_both_tock_refusal_ttWF:
  assumes "priTT p xs ys s P" "ttWF (ys @ [[S]\<^sub>R,[Tock]\<^sub>E])" "R \<subseteq> prirefTT p (s @ ys) P S" "Tock \<notin> prirefTT p (s @ ys) P S"
  shows "priTT p (xs @ [[R]\<^sub>R,[Tock]\<^sub>E]) (ys @ [[S]\<^sub>R,[Tock]\<^sub>E]) s P"
  using assms apply (induct p xs ys s P rule:priTT.induct, auto)
  by (metis append_Nil list.exhaust ttWF.simps(4) ttWF.simps(6) ttWF.simps(8) ttWF_prefix_is_ttWF ttevent.exhaust)+

lemma priTT1_imp_eq_length [intro]:
  assumes "priTT1 p xs ys i P"
  shows "List.length xs = List.length ys"
  using assms by (induct p xs ys i P rule:priTT1.induct, auto)

lemma priTT1_both_imp:
  assumes "priTT1 p (xs @ x) (ys @ y) i P" "List.length xs = List.length ys"  "ttWF y"
  shows "priTT1 p x y (i @ ys) P"
  using assms apply(induct p xs ys i P rule:priTT1.induct, auto)
  apply (cases x, auto, cases y, auto)
  apply (cases y, auto, case_tac a, auto, case_tac aa, auto)
  apply (case_tac x1, auto, case_tac x1a, auto)
  apply (case_tac x1, auto)
   apply (case_tac x1a, auto)
  by (case_tac x1, auto, case_tac x1a, auto)

lemma priTT1_concat_both_imp:
  assumes "priTT1 p (xs @ x) (ys @ y) i P" "List.length xs = List.length ys"
  shows "priTT1 p xs ys i P"
  using assms apply(induct p xs ys i P rule:priTT1.induct, auto)
  apply (cases x, auto, cases y, auto, cases y, auto)
  apply (case_tac a, auto, case_tac aa, auto)
  by (case_tac x1, auto, case_tac x1a, auto)

lemma addRefTickTock_dist_concat:
  "addRefTickTock (xs @ ys) i P = (addRefTickTock xs i P) @ (addRefTickTock ys (i @ xs) P)"
  by (induct xs i P rule:addRefTickTock.induct, auto)

lemma addRefTickTock_concat_event:
  "addRefTickTock (xs @ [[x1]\<^sub>E]) i P = (addRefTickTock xs i P) @ [[x1]\<^sub>E]"
  by (induct xs i P rule:addRefTickTock.induct, auto)

lemma Tock_notin_prirefTT1_imp_notin_prirefTT:
  assumes "Tock \<notin> prirefTT1 pa S s Q" "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "Tock \<notin> prirefTT pa s Q (refTickTock S s Q)"
  using assms unfolding prirefTT1_def prirefTT_def refTickTock_def apply auto
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


lemma prirefTT_imp_prirefTT_refTickTock:
  assumes "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "prirefTT pa (s @ [[Saa]\<^sub>R] @ sa) Q Sa \<subseteq> prirefTT pa (s @ [[refTickTock Saa s Q]\<^sub>R] @ sa) Q Sa"
  using assms unfolding prirefTT_def apply auto
  using TT2_addRefTickTock_ext_imp by fastforce+

lemma prirefTT_refTickTock_imp_prirefTT:
  assumes "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "prirefTT pa (s @ [[refTickTock Saa s Q]\<^sub>R] @ sa) Q Sa \<subseteq> prirefTT pa (s @ [[Saa]\<^sub>R] @ sa) Q Sa"
  using assms unfolding prirefTT_def apply auto
  using TT2_addRefTickTock_subset_imp TT_TT1 by fastforce+

lemma prirefTT_eq_prirefTT_refTickTock:
  assumes "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "prirefTT pa (s @ [[Saa]\<^sub>R] @ sa) Q Sa = prirefTT pa (s @ [[refTickTock Saa s Q]\<^sub>R] @ sa) Q Sa"
  using assms prirefTT_imp_prirefTT_refTickTock prirefTT_refTickTock_imp_prirefTT by blast

lemma Tock_notin_prirefTT1_imp_notin_prirefTT_refTickTock:
  assumes "Tock \<notin> prirefTT pa (s @ [Saa]\<^sub>R # sa) Q  Sa" "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "Tock \<notin> prirefTT pa (s @ [refTickTock Saa s Q]\<^sub>R # sa) Q Sa"
  using assms prirefTT_eq_prirefTT_refTickTock by fastforce

lemma priTT_trace_refTickTock:
  assumes "priTT p xs ys (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q" "TT(Q)" "TT2(Q)" "TT4(Q)"
  shows "priTT p xs ys (s @ [[refTickTock S s Q]\<^sub>R, [Tock]\<^sub>E]) Q"
  using assms apply (induct p xs ys _ Q arbitrary:S rule:priTT.induct, auto)
  using prirefTT_eq_prirefTT_refTickTock apply fastforce
  using prirefTT_eq_prirefTT_refTickTock apply fastforce
  using prirefTT_eq_prirefTT_refTickTock apply fastforce
  by (metis TT2_addRefTickTock_ext_imp append_Cons append_Nil prirefTT_eq_prirefTT_refTickTock)

lemma priTT1_imp_priTT:
  assumes "priTT1 p xs ys i P" "TT(P)" "TT2(P)" "TT4(P)"
  shows "priTT p xs (addRefTickTock ys i P) i P"
  using assms proof (induct p xs ys _ P rule:priTT.induct, auto)
  fix pa S s Q x
  fix R::"'a ttevent set" 
  assume assms: "R \<subseteq> prirefTT1 pa S s Q"
         "TT Q" "TT2 Q" "TT4 Q"
         "x \<in> R"
  show "x \<in> prirefTT pa s Q (refTickTock S s Q)"
    using assms prirefTT1_imp_prirefTT_noassm by blast
next
  fix pa aa S zz s Q x
  fix R::"'a ttevent set" 
  assume assms: "priTT pa aa (addRefTickTock zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
          "R \<subseteq> prirefTT1 pa S s Q"
          "Tock \<notin> prirefTT1 pa S s Q"
         "TT Q" "TT2 Q" "TT4 Q"
         "x \<in> R"
  show "x \<in> prirefTT pa s Q (refTickTock S s Q)"
    using assms prirefTT1_imp_prirefTT_noassm by blast
next
  fix pa aa S zz s Q
  fix R::"'a ttevent set" 
  assume assms: "priTT pa aa (addRefTickTock zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
          "R \<subseteq> prirefTT1 pa S s Q"
          "Tock \<notin> prirefTT1 pa S s Q"
         "TT Q" "TT2 Q" "TT4 Q"
          "Tock \<in> prirefTT pa s Q (refTickTock S s Q)"
  have "Tock \<notin> prirefTT pa s Q (refTickTock S s Q)"
    using assms Tock_notin_prirefTT1_imp_notin_prirefTT by blast
  then show "False"
    using assms by auto
next
  fix pa aa S zz s Q
  fix R::"'a ttevent set" 
  assume assms: "priTT pa aa (addRefTickTock zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
          "R \<subseteq> prirefTT1 pa S s Q"
          "Tock \<notin> prirefTT1 pa S s Q"
         "TT Q" "TT2 Q" "TT4 Q"
  then show "priTT pa aa (addRefTickTock zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q) (s @ [[refTickTock S s Q]\<^sub>R, [Tock]\<^sub>E]) Q"
    using priTT_trace_refTickTock
    by blast
next
  fix pa aa e\<^sub>2 zz s Q
  fix Z::"'a ttevent set" 
  assume assms: 
      "priTT pa aa (addRefTickTock zz (s @ [[e\<^sub>2]\<^sub>E]) Q) (s @ [[e\<^sub>2]\<^sub>E]) Q"
      "TT Q"
      "TT2 Q"
      "TT4 Q"
      "priTT1 pa aa zz (s @ [[e\<^sub>2]\<^sub>E]) Q"
      "s @ [[Z]\<^sub>R] \<in> Q"
      "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q"
      "Tick \<in> Z"
      "e\<^sub>2 \<notin> Z" "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b" "Tock \<in> Z" "\<forall>Z. s @ [[Z]\<^sub>R] \<in> Q \<longrightarrow> e\<^sub>2 = Tick \<or> e\<^sub>2 \<in> prirefTT pa s Q Z"
  then have "priTT1 pa ([e\<^sub>2]\<^sub>E # aa) ([e\<^sub>2]\<^sub>E # zz) s Q"
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
          by (smt TT3_any_cons_end_tock TT_TT3 True assms(10) assms(11) assms(12) assms(2) assms(6) assms(9) mem_Collect_eq prirefTT_subset_prirefTT1 prirefTT1_def subsetCE)
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
      "priTT pa aa (addRefTickTock zz (s @ [[e\<^sub>2]\<^sub>E]) Q) (s @ [[e\<^sub>2]\<^sub>E]) Q"
      "TT Q"
      "TT2 Q"
      "TT4 Q"
      "priTT1 pa aa zz (s @ [[e\<^sub>2]\<^sub>E]) Q"
      "s @ [[Z]\<^sub>R] \<in> Q"
      "\<forall>e. e \<notin> Z \<and> e \<noteq> Tock \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q"
      "Tick \<in> Z"
      "e\<^sub>2 \<notin> Z" "\<forall>b. b \<in> Z \<or> \<not> e\<^sub>2 <\<^sup>*pa b" "s @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<in> Q" "\<forall>Z. s @ [[Z]\<^sub>R] \<in> Q \<longrightarrow> e\<^sub>2 = Tick \<or> e\<^sub>2 \<in> prirefTT pa s Q Z"
  then show "maximal(pa,e\<^sub>2)"
    by (smt TT3_any_cons_end_tock TT_TT3 Un_iff mem_Collect_eq prirefTT_def)
qed 

lemma Tock_notin_prirefTT_imp_notin_prirefTT1:
  assumes "Tock \<notin> prirefTT pa s Q S" "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
  shows "Tock \<notin> prirefTT1 pa S s Q"
  using assms unfolding prirefTT1_def prirefTT_def by auto

lemma xx1:
  assumes
  "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q
      \<and> (\<forall>e. (e \<notin> Z \<and> e \<noteq> Tock) \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q)
      \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z
      \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))" "TT3(Q)"
  shows "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT p s Q Z)"
  using assms apply auto
  unfolding prirefTT_def apply auto
  using TT3_any_cons_end_tock by blast+

lemma priTT_imp_priTT1:
  assumes "priTT p xs ys i P" "TT(P)" "TT2(P)" "TT4(P)" "i @ ys \<in> P"
  shows "priTT1 p xs ys i P"
  using assms proof (induct p xs ys i P rule:priTT1.induct, auto)
  fix pa S s Q x
  fix R::"'a ttevent set" 
  assume "R \<subseteq> prirefTT pa s Q S"
       "TT Q"
       "TT2 Q"
       "TT4 Q" "s @ [[S]\<^sub>R] \<in> Q" "x \<in> R"
  then show "x \<in> prirefTT1 pa S s Q"
    using TT_TT3 prirefTT_imp_prirefTT1 by blast
next
  fix pa aa S zz s Q x
  fix R::"'a ttevent set" 
  assume "priTT1 pa aa zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
       "TT Q"
       "TT2 Q"
       "TT4 Q"
       "s @ [S]\<^sub>R # [Tock]\<^sub>E # zz \<in> Q"
       "R \<subseteq> prirefTT pa s Q S" "x \<in> R"
  then show "x \<in> prirefTT1 pa S s Q"
    using TT_TT3 prirefTT_imp_prirefTT1 by blast
next
  fix pa aa zz s Q
  fix S R::"'a ttevent set" 
  assume assm:"priTT1 pa aa zz (s @ [[S]\<^sub>R, [Tock]\<^sub>E]) Q"
       "TT Q"
       "TT2 Q"
       "TT4 Q"
       "s @ [S]\<^sub>R # [Tock]\<^sub>E # zz \<in> Q"
       "Tock \<notin> prirefTT pa s Q S"
       "Tock \<in> prirefTT1 pa S s Q"
  then have "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<lesssim>\<^sub>C s @ [S]\<^sub>R # [Tock]\<^sub>E # zz"
    by (metis Cons_eq_appendI append_eq_appendI self_append_conv2 tt_prefix_subset_front tt_prefix_subset_refl)
  then have "s @ [[S]\<^sub>R,[Tock]\<^sub>E] \<in> Q"
    using assm TT1_def TT_TT1 by blast
  then have "Tock \<notin> prirefTT1 pa S s Q"
    using assm Tock_notin_prirefTT_imp_notin_prirefTT1 by blast
  then show "False"
    using assm by auto
next
  fix pa aa zz s Q
  fix e\<^sub>2::"'a ttevent"
  fix Z::"'a ttevent set" 
  assume assms:
    "priTT1 pa aa zz (s @ [[e\<^sub>2]\<^sub>E]) Q"
    "TT Q"
    "TT2 Q"
    "TT4 Q"
    "s @ [e\<^sub>2]\<^sub>E # zz \<in> Q"
    "priTT pa aa zz (s @ [[e\<^sub>2]\<^sub>E]) Q"
    "s @ [[Z]\<^sub>R] \<in> Q"
    "e\<^sub>2 \<noteq> Tick" "e\<^sub>2 \<notin> prirefTT pa s Q Z"
    "\<forall>Z. Tick \<in> Z \<longrightarrow> 
      s @ [[Z]\<^sub>R] \<in> Q \<longrightarrow> 
        (\<exists>e. e \<notin> Z \<and> e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q) \<or> Tock \<notin> Z \<and> s @ [[Z]\<^sub>R, [Tock]\<^sub>E] \<notin> Q \<or> e\<^sub>2 \<in> Z \<or> (\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*pa b)"
  then have s_e2_in:"s @ [[e\<^sub>2]\<^sub>E] \<in> Q"
    by (meson TT1_def TT_TT1 tt_prefix_common_concat tt_prefix_subset.simps(1) tt_prefix_subset.simps(3))
  then show "maximal(pa,e\<^sub>2)"
  proof (cases e\<^sub>2)
    case (Event x1)
    have a:"s @ [[refTickTock Z s Q]\<^sub>R] \<in> Q"
      by (simp add: assms(2) assms(3) assms(4) assms(7) prirefTT1_imp_prirefTT'')
    have b:"Tick \<in> refTickTock Z s Q"
      unfolding refTickTock_def by auto
    have c:"\<not>(\<exists>e. e \<notin> refTickTock Z s Q \<and> e \<noteq> Tock \<and> s @ [[e]\<^sub>E] \<notin> Q)"
      using refTickTock_def by fastforce
    have d:"(Tock \<in> refTickTock Z s Q \<or> s @ [[refTickTock Z s Q]\<^sub>R, [Tock]\<^sub>E] \<in> Q)"
      by (simp add: refTickTock_def)
    have e:"Event x1 \<notin> refTickTock Z s Q"
      using s_e2_in assms 
      by (simp add: Event prirefTT_def refTickTock_def)
    have f:"\<not> (\<exists>b. b \<notin> refTickTock Z s Q \<and> e\<^sub>2 <\<^sup>*pa b)" (* TODO: ugly proof steps, redo *)
      unfolding refTickTock_def apply auto
      using assms apply (smt UnCI mem_Collect_eq prirefTT_def)
      using assms apply (smt TT_TTwf TTwf_Refusal_imp_no_Tock UnCI mem_Collect_eq prirefTT_def)
      using assms by (metis (mono_tags, lifting) TT1_Ref_Tock_subset_imp TT_TT1 UnCI Un_insert_right mem_Collect_eq prirefTT_def)
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

lemma PriTT_eq_priTT:
  assumes "TT(P)" "TT2(P)" "TT4(P)"
  shows "PriTT p P = PriTT1 p P"
  using assms unfolding PriTT_def PriTT1_def apply auto
  using priTT_imp_priTT1 apply fastforce
  by (metis addRefTickTock_in append_Nil priTT1_imp_priTT)

lemma TT1_PriTT:
  assumes "TT(P)" "TT2(P)" "TT4(P)"
  shows "TT1(PriTT p P)"
  using assms
  by (metis PriTT_eq_priTT TT1_mkTT1 TT4_TT1_imp_TT4w TT_TT1 TT_TT3 mkTT1_PriMax_unTT1_priTT)

lemma TT_priTT1_closure:
  assumes "TT P" "TT2 P" "TT4 P"
  shows "TTwf(PriTT1 p P)"
        "TT0(PriTT1 p P)"
        "TT1(PriTT1 p P)"
        "TT2(PriTT1 p P)"
        "TT3(PriTT1 p P)"
        "TT4(PriTT1 p P)"
proof -
  have TTMax:
       "TT0 (unTT1 P)"
       "TTwf (unTT1 P)"
       "TT1w (unTT1 P)" 
       "TT2 (unTT1 P)" 
       "TT3 (unTT1 P)" 
       "TT4 (unTT1 P)" 
       "TTM1 (unTT1 P)" 
       "TTM2 (unTT1 P)" 
       "TTM3 (unTT1 P)"
    using assms unTT1_TT_closure by blast+

  have PriTT1_eq:"PriTT1 p P = mkTT1 (PriMax p (unTT1 P))"
    by (simp add: TT4_TT1_imp_TT4w TT_TT1 TT_TT3 assms mkTT1_PriMax_unTT1_priTT)

  show "TTwf(PriTT1 p P)"
    using PriTT1_eq TTMax unTT1_TT_closure 
    by (simp add: TTMax_PriMax_closure(1) TTwf_mkTT1)    

  show "TT0(PriTT1 p P)"
    using PriTT1_eq TTMax_PriMax_closure unTT1_TT_closure
    by (metis TT0_mkTT1 assms(1) assms(2) assms(3))

  show "TT1(PriTT1 p P)"
    using PriTT1_eq TTMax unTT1_TT_closure
    by (simp add: TT1_mkTT1)

  show "TT2(PriTT1 p P)"
    using PriTT1_eq TTMax unTT1_TT_closure
    by (simp add: TT2_mkTT1 TTMax_PriMax_closure(3) TTMax_PriMax_closure(4) TTMax_PriMax_closure(7) TTMax_PriMax_closure(8))

  show "TT3(PriTT1 p P)"
    using PriTT1_eq TTMax unTT1_TT_closure
    by (simp add: TT3_mkTT1 TTMax_PriMax_closure(5))

  show "TT4(PriTT1 p P)"
    using PriTT1_eq TTMax unTT1_TT_closure
    by (simp add: TT4_mkTT1 TTMax_PriMax_closure(6))
qed

lemma TT_priTT_closure:
  assumes "TT P" "TT2 P" "TT4 P"
  shows "TTwf(PriTT p P)"
        "TT0(PriTT p P)"
        "TT1(PriTT p P)"
        "TT2(PriTT p P)"
        "TT3(PriTT p P)"
        "TT4(PriTT p P)"
proof -
  have "PriTT p P = PriTT1 p P"
    using assms PriTT_eq_priTT by blast
  then show 
        "TTwf(PriTT p P)"
        "TT0(PriTT p P)"
        "TT1(PriTT p P)"
        "TT2(PriTT p P)"
        "TT3(PriTT p P)"
        "TT4(PriTT p P)"
  using assms TT_priTT1_closure 
  by (simp_all add: TT_priTT1_closure)
qed

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
  assumes "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT p s Q Z)" "TT(Q)" "TT3(Q)" "TT2(Q)" "TT4(Q)" "s @ [[e\<^sub>2]\<^sub>E] \<in> Q" 
  shows   "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q
      \<and> (\<forall>e. (e \<notin> Z \<and> e \<noteq> Tock) \<longrightarrow> s @ [[e]\<^sub>E] \<in> Q)
      \<and> (Tock \<notin> Z \<longrightarrow> s @ [[Z]\<^sub>R,[Tock]\<^sub>E] \<in> Q) \<and> Tick \<in> Z
      \<and> e\<^sub>2 \<notin> Z \<and> \<not>(\<exists>b. b \<notin> Z \<and> e\<^sub>2 <\<^sup>*p b))" 
  using assms apply auto
  apply (rule_tac x="refTickTock Z s Q" in exI, auto)
     apply (simp add: refTickTock_def)
    apply (simp add: refTickTock_def)
    unfolding refTickTock_def prirefTT_def apply auto
    using TT_TTwf TTwf_Refusal_imp_no_Tock apply blast
  using TT_TTwf TTwf_Refusal_imp_no_Tock apply blast
  using TT1_Ref_Tock_subset_imp' TT_TT1 by blast+

lemma
  assumes "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> e\<^sub>2 \<noteq> Tick \<and> e\<^sub>2 \<notin> prirefTT p s Q Z)" "TT(Q)" "TT3(Q)" "TT2(Q)" "TT4(Q)" "s @ [[e\<^sub>2]\<^sub>E] \<in> Q" 
  shows "(\<exists>Z. s @ [[Z]\<^sub>R] \<in> Q \<and> Tick \<in> Z \<and> e\<^sub>2 \<notin> prirefTT p s Q Z)"
  using assms apply auto
  apply (rule_tac x="Z \<union> {Tick}" in exI, auto)
  using TT4_TT1_add_Tick TT_TT1 apply fastforce
  unfolding refTickTock_def prirefTT_def apply auto
  using TT1_Ref_Tock_subset_imp' TT_TT1 by blast

end