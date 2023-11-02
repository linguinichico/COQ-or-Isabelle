section \<open>LTL\<close>
theory ltl
  imports Main "HOL-Library.Omega_Words_Fun"
begin

datatype 'a ltl =
    True_ltl                               ("true\<^sub>L\<^sub>T\<^sub>L")
  | False_ltl                              ("false\<^sub>L\<^sub>T\<^sub>L")
  | Prop_ltl 'a                            ("prop\<^sub>L\<^sub>T\<^sub>L'(_')")
  | Not_ltl "'a ltl"                       ("not\<^sub>L\<^sub>T\<^sub>L _" [85] 85)
  | And_ltl "'a ltl" "'a ltl"              ("_ and\<^sub>L\<^sub>T\<^sub>L _" [82,82] 81)
  | Or_ltl "'a ltl" "'a ltl"               ("_ or\<^sub>L\<^sub>T\<^sub>L _" [81,81] 80)
  | Implies_ltl "'a ltl" "'a ltl"          ("_ implies\<^sub>L\<^sub>T\<^sub>L _" [81,81] 80)
  | Next_ltl "'a ltl"                      ("X\<^sub>L\<^sub>T\<^sub>L _" [88] 87)
  | Final_ltl "'a ltl"                     ("F\<^sub>L\<^sub>T\<^sub>L _" [88] 87)
  | Global_ltl "'a ltl"                    ("G\<^sub>L\<^sub>T\<^sub>L _" [88] 87)
  | Until_ltl "'a ltl" "'a ltl"            ("_ U\<^sub>L\<^sub>T\<^sub>L _" [84,84] 83)

subsubsection \<open>Semantics_LTL\<close>

fun semantics_ltl :: "['a set word, 'a ltl] \<Rightarrow> bool" ("_ \<tturnstile>\<^sub>L\<^sub>T\<^sub>L _" [80,80] 80)
  where
    "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L true\<^sub>L\<^sub>T\<^sub>L = True"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L false\<^sub>L\<^sub>T\<^sub>L = False"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L prop\<^sub>L\<^sub>T\<^sub>L(q) = (q\<in>\<sigma> 0)"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L not\<^sub>L\<^sub>T\<^sub>L \<phi> = (\<not> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>)"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> and\<^sub>L\<^sub>T\<^sub>L \<psi> = (\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> \<and> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi>)"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> or\<^sub>L\<^sub>T\<^sub>L \<psi> = (\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> \<or> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi>)"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> implies\<^sub>L\<^sub>T\<^sub>L \<psi> = (\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> \<longrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi>)"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L X\<^sub>L\<^sub>T\<^sub>L \<phi> = (suffix 1 \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>)"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L \<phi> = (\<exists>i. suffix i \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>)"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L G\<^sub>L\<^sub>T\<^sub>L \<phi> = (\<forall>i. suffix i \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>)"
  | "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi> = (\<exists>i. suffix i \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi> \<and> (\<forall>j<i. suffix j \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>))"

lemma ltl_true_or_con[simp]:
  "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L prop\<^sub>L\<^sub>T\<^sub>L(p) or\<^sub>L\<^sub>T\<^sub>L (not\<^sub>L\<^sub>T\<^sub>L prop\<^sub>L\<^sub>T\<^sub>L(p))"
  by simp

lemma ltl_false_true_con[simp]:
  "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L not\<^sub>L\<^sub>T\<^sub>L true\<^sub>L\<^sub>T\<^sub>L \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L false\<^sub>L\<^sub>T\<^sub>L"
  by simp

lemma ltl_equiv_1 [simp]:
  "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L \<phi> \<longleftrightarrow>  \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (true\<^sub>L\<^sub>T\<^sub>L U\<^sub>L\<^sub>T\<^sub>L \<phi>)"
  by simp

lemma ltl_equiv_2 [simp]:
  "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L X\<^sub>L\<^sub>T\<^sub>L (not\<^sub>L\<^sub>T\<^sub>L \<phi>) \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L not\<^sub>L\<^sub>T\<^sub>L X\<^sub>L\<^sub>T\<^sub>L \<phi>"
  by simp

lemma ltl_equiv_3 [simp]:
   "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L G\<^sub>L\<^sub>T\<^sub>L (not\<^sub>L\<^sub>T\<^sub>L \<phi>) \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L not\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L \<phi>"
  by simp

lemma ltl_equiv_4 [simp]:
   "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L (not\<^sub>L\<^sub>T\<^sub>L \<phi>) \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L not\<^sub>L\<^sub>T\<^sub>L G\<^sub>L\<^sub>T\<^sub>L \<phi>"
  by simp

lemma ltl_equiv_5 [simp]:
   "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L G\<^sub>L\<^sub>T\<^sub>L (G\<^sub>L\<^sub>T\<^sub>L \<phi>) \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L G\<^sub>L\<^sub>T\<^sub>L \<phi>"
  apply simp
  apply (metis suffix_0 suffix_suffix)
  done
  

lemma ltl_equiv_6 [simp]:
   "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L (F\<^sub>L\<^sub>T\<^sub>L \<phi>) \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L \<phi>"
  apply simp
  apply (metis add_0)
  done

lemma ltl_equiv_7 [simp]:
   "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L G\<^sub>L\<^sub>T\<^sub>L \<phi> \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L not\<^sub>L\<^sub>T\<^sub>L ( F\<^sub>L\<^sub>T\<^sub>L ( not\<^sub>L\<^sub>T\<^sub>L \<phi>))"
  by simp

lemma ltl_equiv_8 [simp]:
   "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L G\<^sub>L\<^sub>T\<^sub>L (F\<^sub>L\<^sub>T\<^sub>L (G\<^sub>L\<^sub>T\<^sub>L \<phi>)) \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L (G\<^sub>L\<^sub>T\<^sub>L \<phi>)"
  apply simp  
  apply (metis ab_semigroup_add_class.add_ac(1) add.commute)
  done

lemma ltl_equiv_9 [simp]:
   "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L (G\<^sub>L\<^sub>T\<^sub>L (F\<^sub>L\<^sub>T\<^sub>L \<phi>)) \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L G\<^sub>L\<^sub>T\<^sub>L (F\<^sub>L\<^sub>T\<^sub>L \<phi>)"
  apply simp
  apply (metis ab_semigroup_add_class.add_ac(1) add.commute)
  done

lemma ltl_equiv_10 [simp]: 
   "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L  \<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>  \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi> or\<^sub>L\<^sub>T\<^sub>L ( \<phi> and\<^sub>L\<^sub>T\<^sub>L X\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>))" 
   (is "?fst =  ?snd")
proof
  assume ?fst
  then obtain i where "suffix i \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L  \<psi>" and "\<forall>j<i. suffix j \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>"
    by auto
  thus ?snd
  proof (cases i)
    case 0
    thus ?thesis using \<open>suffix i \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi>\<close> by auto
  next
    case (Suc nat)
    thus ?thesis using \<open>\<forall>j<i. suffix j \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>\<close> and \<open>suffix i \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi>\<close>  by auto
  qed
next
  assume ?snd
  show ?fst
  proof (cases "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi>")
    case True
    thus ?fst
      by force
  next
    case False
    then obtain "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>" and "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L X\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>)" using \<open>?snd\<close> by auto
    thus ?fst
      using less_Suc_eq_0_disj suffix_singleton_suffix by force
  qed
qed

lemma ltl_equiv_11 [simp]:
   "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L \<phi>  \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> or\<^sub>L\<^sub>T\<^sub>L ( X\<^sub>L\<^sub>T\<^sub>L (F\<^sub>L\<^sub>T\<^sub>L \<phi>) )" (is "?fst = ?snd")
proof
  assume ?fst
  then obtain i where "suffix i \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>" by auto
  thus ?snd
  proof (induction i)
    case 0
    thus ?case by force
  next
    case (Suc i)
    thus ?thesis
    proof -
      have "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L true\<^sub>L\<^sub>T\<^sub>L U\<^sub>L\<^sub>T\<^sub>L \<phi>"
        by (metis \<open>\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L F\<^sub>L\<^sub>T\<^sub>L \<phi>\<close> ltl_equiv_1)
      then show ?thesis
        by (metis (no_types) ltl_equiv_1 ltl_equiv_10 semantics_ltl.simps(5) semantics_ltl.simps(6) semantics_ltl.simps(8))
    qed
  qed
next
  assume ?snd
  thus ?fst
  proof (cases "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>")
    case True
    then have "suffix 0 \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>" by simp
    thus ?thesis using semantics_ltl.simps(9) by blast
  next
    case False
    then have "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L X\<^sub>L\<^sub>T\<^sub>L (F\<^sub>L\<^sub>T\<^sub>L \<phi>)"
      using \<open>\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> or\<^sub>L\<^sub>T\<^sub>L X\<^sub>L\<^sub>T\<^sub>L (F\<^sub>L\<^sub>T\<^sub>L \<phi>)\<close> by auto
    thus ?thesis
      using ltl_equiv_6 semantics_ltl.simps(8) semantics_ltl.simps(9) by blast
  qed
qed

lemma until_and_left_distrib: (*instead of doing next and applying auto, the second step can be done by simply doing qed auto*)
  "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 and\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2) U\<^sub>L\<^sub>T\<^sub>L \<psi> \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 U\<^sub>L\<^sub>T\<^sub>L \<psi>) and\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>2 U\<^sub>L\<^sub>T\<^sub>L \<psi>)"
proof
  assume "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 U\<^sub>L\<^sub>T\<^sub>L \<psi>) and\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>2 U\<^sub>L\<^sub>T\<^sub>L \<psi>)"
  then obtain i1 i2 where "suffix i1 \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi> \<and> (\<forall>j<i1. suffix j \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>1)" and "suffix i2 \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi> \<and> (\<forall>j<i2. suffix j \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2)"
    by auto
  then have "suffix (min i1 i2) \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi> \<and> (\<forall>j<min i1 i2. suffix j \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>1 and\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2)"
    by (simp add: min_def)
  then show "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 and\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2) U\<^sub>L\<^sub>T\<^sub>L \<psi>"
    by force
next
  assume "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 and\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2) U\<^sub>L\<^sub>T\<^sub>L \<psi>"
  then show "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 U\<^sub>L\<^sub>T\<^sub>L \<psi>) and\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>2 U\<^sub>L\<^sub>T\<^sub>L \<psi>)"
    by auto
qed

lemma until_or_right_distrib:
  "w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L (\<psi>\<^sub>1 or\<^sub>L\<^sub>T\<^sub>L \<psi>\<^sub>2) \<longleftrightarrow> w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>\<^sub>1) or\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>\<^sub>2)"
  by auto

lemma until_or_right_distrib:
  "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>) \<longleftrightarrow> \<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>"
proof
  assume "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>"
  thus "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>)"
    using \<open>\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>\<close> ltl_equiv_10 semantics_ltl.simps(6) by blast
next
  assume "\<sigma> \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>)"
  oops

end