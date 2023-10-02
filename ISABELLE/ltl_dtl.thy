section \<open>LTL/DTL\<close>
theory ltl_dtl
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
    oops

lemma until_and_left_distrib: (*instead of doing next and applying auto, the second step can be done by simply doing qed auto*)
  "w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 and\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2) U\<^sub>L\<^sub>T\<^sub>L \<psi> \<longleftrightarrow> w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 U\<^sub>L\<^sub>T\<^sub>L \<psi>) and\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>2 U\<^sub>L\<^sub>T\<^sub>L \<psi>)"
proof
  assume "w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>1 U\<^sub>L\<^sub>T\<^sub>L \<psi> and\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2 U\<^sub>L\<^sub>T\<^sub>L \<psi>"
  then obtain i1 i2 where "suffix i1 w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi> \<and> (\<forall>j<i1. suffix j w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>1)" and "suffix i2 w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi> \<and> (\<forall>j<i2. suffix j w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2)"
    by auto
  then have "suffix (min i1 i2) w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<psi> \<and> (\<forall>j<min i1 i2. suffix j w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>1 and\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2)"
    by (simp add: min_def)
  then show "w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 and\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2) U\<^sub>L\<^sub>T\<^sub>L \<psi>"
    by force
next
  assume "w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 and\<^sub>L\<^sub>T\<^sub>L \<phi>\<^sub>2) U\<^sub>L\<^sub>T\<^sub>L \<psi>"
  then show "w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>1 U\<^sub>L\<^sub>T\<^sub>L \<psi>) and\<^sub>L\<^sub>T\<^sub>L (\<phi>\<^sub>2 U\<^sub>L\<^sub>T\<^sub>L \<psi>)"
    by auto
qed

lemma until_or_right_distrib:
  "w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L (\<psi>\<^sub>1 or\<^sub>L\<^sub>T\<^sub>L \<psi>\<^sub>2) \<longleftrightarrow> w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>\<^sub>1) or\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>\<^sub>2)"
  by auto

lemma until_or_right_distrib:
  "w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L (\<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>) \<longleftrightarrow> w \<tturnstile>\<^sub>L\<^sub>T\<^sub>L \<phi> U\<^sub>L\<^sub>T\<^sub>L \<psi>"
  apply simp
  oops

subsection \<open>Syntax DTL\<close>

datatype id = A | B | C

datatype state_proposition  = work | pend | active | got\<^sub>A | got\<^sub>B

fun id_to_state :: "id \<Rightarrow> state_proposition set"
  where
  "id_to_state A = {work, pend}"
| "id_to_state B = {work, pend}"
| "id_to_state C = {active, got\<^sub>A, got\<^sub>B}"

datatype event_state = event | pass 

datatype 'a dtl_l =
    True_dtl_l                           ("true\<^sub>D\<^sub>T\<^sub>L")
  | False_dtl_l                          ("false\<^sub>D\<^sub>T\<^sub>L")
  | Prop_dtl_l 'a                        ("prop\<^sub>D\<^sub>T\<^sub>L '(_')")
  | Not_dtl_l "'a  dtl_l"                ("not\<^sub>D\<^sub>T\<^sub>L _" [85] 84)
  | And_dtl_l "'a dtl_l" "'a  dtl_l"     ("_ and\<^sub>D\<^sub>T\<^sub>L _" [83,83] 82)
  | Or_dtl_l "'a dtl_l" "'a dtl_l"       ("_ or\<^sub>D\<^sub>T\<^sub>L _" [83,83] 82)
  | Implies_dtl_l "'a dtl_l" "'a dtl_l"  ("_ implies\<^sub>D\<^sub>T\<^sub>L _" [83,83] 82)
  | Next_dtl_l "'a dtl_l"                ("X\<^sub>D\<^sub>T\<^sub>L _" [88] 87)
  | Finally_dtl_l "'a dtl_l"             ("F\<^sub>D\<^sub>T\<^sub>L _" [88] 87)
  | Global_dtl_l "'a dtl_l"              ("G\<^sub>k\<^sub>D\<^sub>T\<^sub>L _" [88] 87)
  | Until_dtl_l "'a dtl_l" "'a dtl_l"    ("_ U\<^sub>D\<^sub>T\<^sub>L _" [88,88] 87)
  | Comms_dltc "id" "'a dtl_l"           ("\<copyright>\<^sub>_'[_']" [82,82] 81)

datatype 'a dtl =
  Identifier "id" "'a dtl_l"           ("@\<^sub>_'[_']" [84,84] 83)

fun semantics_dtl_local_k :: " [(event_state \<times> state_proposition) word, nat, id, state_proposition dtl_l] \<Rightarrow> bool" ("_,_ \<tturnstile>\<^sub>D\<^sub>T\<^sub>L'(_')  _" [81,81,81,81] 81)
  where
    "\<xi>,0 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) _ = False"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) true\<^sub>D\<^sub>T\<^sub>L = (let (e,s) = \<xi> 0 in (case e of 
                                                pass \<Rightarrow> (suffix 1 \<xi>),(n-(1::nat)) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) true\<^sub>D\<^sub>T\<^sub>L
                                              |event \<Rightarrow> True))"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) false\<^sub>D\<^sub>T\<^sub>L = (let (e,s) = \<xi> 0 in (case e of 
                                                pass \<Rightarrow> (suffix 1 \<xi>),(n-(1::nat)) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) true\<^sub>D\<^sub>T\<^sub>L
                                              |event \<Rightarrow> False))"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) prop\<^sub>D\<^sub>T\<^sub>L(q) = (let (e,s) = \<xi> 0 in (case e of 
                                                  pass \<Rightarrow> (suffix 1 \<xi>),(n-(1::nat)) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) prop\<^sub>D\<^sub>T\<^sub>L(q)
                                                |event \<Rightarrow> q \<in> id_to_state i))"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (not\<^sub>D\<^sub>T\<^sub>L \<phi>) = (\<not> (\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>))"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<phi> and\<^sub>D\<^sub>T\<^sub>L \<psi>) = ((\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>) \<and> (\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<psi>))"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<phi> or\<^sub>D\<^sub>T\<^sub>L \<psi>) = ((\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>) \<or> (\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<psi>))"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<phi> implies\<^sub>D\<^sub>T\<^sub>L \<psi>) = ((\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>) \<longrightarrow> (\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<psi>))"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (X\<^sub>D\<^sub>T\<^sub>L \<phi>) = (suffix 1 \<xi>),(n-(1::nat)) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L \<phi>) = (\<forall>j<n. (suffix j \<xi>),(n-j) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>)"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (F\<^sub>D\<^sub>T\<^sub>L \<phi>) = (\<exists>j<n. (suffix j \<xi>),(n-j) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>)"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<phi> U\<^sub>D\<^sub>T\<^sub>L \<psi>) = (\<exists>j<n. (suffix j \<xi>),(n-j) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<psi> \<and> (\<forall>k<j.(suffix k \<xi>),(n-k) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>))"
  | "\<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<copyright>\<^sub>j[\<phi>]) = \<xi>,n \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(j) \<phi>"

fun semantics_dtl_1 :: "[(event_state \<times> state_proposition) word,nat, state_proposition dtl] \<Rightarrow> bool "("_,_ \<tturnstile>\<^sub>D\<^sub>T\<^sub>L _" [79,79] 80)
  where
  "(\<xi>,k \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>i[\<phi>]) = (\<xi>,k \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>)"

(*Additional operator to use under protocol proof*)

abbreviation WeakUntil_dtl_l :: "'a dtl_l \<Rightarrow> 'a dtl_l \<Rightarrow> 'a dtl_l"   ("_ W\<^sub>D\<^sub>T\<^sub>L _" [88] 87)
  where 
  "\<phi> W\<^sub>D\<^sub>T\<^sub>L \<psi> \<equiv> (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L \<phi>) or\<^sub>D\<^sub>T\<^sub>L (\<phi> U\<^sub>D\<^sub>T\<^sub>L \<psi>)"

(*Setting up protocol transition states*)
(*Transition states for coordinator, represented as "C"*)

abbreviation idle :: "state_proposition dtl_l"
  where 
  "idle \<equiv> ((not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(active)) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))"

abbreviation wait\<^sub>A\<^sub>B :: "state_proposition dtl_l"
  where 
  "wait\<^sub>A\<^sub>B \<equiv> (prop\<^sub>D\<^sub>T\<^sub>L(active) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))"

abbreviation wait\<^sub>A :: "state_proposition dtl_l"
  where 
  "wait\<^sub>A \<equiv> (prop\<^sub>D\<^sub>T\<^sub>L(active) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))"

abbreviation wait\<^sub>B :: "state_proposition dtl_l"
  where 
  "wait\<^sub>B \<equiv> (prop\<^sub>D\<^sub>T\<^sub>L(active) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))"

abbreviation Done :: "state_proposition dtl_l"
  where 
  "Done \<equiv> (prop\<^sub>D\<^sub>T\<^sub>L(active) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))"

(*Transition states for subordinates, represented as "A" and "B"*)

abbreviation free :: "state_proposition dtl_l"
  where 
  "free \<equiv> prop\<^sub>D\<^sub>T\<^sub>L(work) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(pend))"

abbreviation busy :: "state_proposition dtl_l"
  where 
  "busy \<equiv> prop\<^sub>D\<^sub>T\<^sub>L(work) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(pend))"

abbreviation ready :: "state_proposition dtl_l"
  where 
  "ready \<equiv> not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(work)"

(*Coordinator's actions*)

abbreviation prep :: "state_proposition dtl_l"
  where 
  "prep \<equiv> (idle and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A\<^sub>B)))"

abbreviation reply\<^sub>A :: "state_proposition dtl_l"
  where 
  "reply\<^sub>A \<equiv> (not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A) and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))))"

abbreviation reply\<^sub>B :: "state_proposition dtl_l"
  where 
  "reply\<^sub>B \<equiv> (not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B) and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))))"

(*Subordinattes' actions*)

abbreviation req :: "state_proposition dtl_l"
  where 
  "req \<equiv> (free and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L busy))"

abbreviation reply :: "state_proposition dtl_l"
  where 
  "reply \<equiv> (busy and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L ready))"

(*Proof of property with restrictions*)

lemma coordinator_receives_both_replies:
  assumes bound : "k>1"
  and coordinator_initial_state : "\<xi>,1 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[idle]"
  and subordinator_A_initial_state : "\<xi>,1 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>A[free]"
  and subordinator_B_initial_state : "\<xi>,1 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>B[free]"
  and idle_property : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (idle implies\<^sub>D\<^sub>T\<^sub>L (idle W\<^sub>D\<^sub>T\<^sub>L prep)))"
  and waitAB_property : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A\<^sub>B implies\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A\<^sub>B W\<^sub>D\<^sub>T\<^sub>L (reply\<^sub>A or\<^sub>D\<^sub>T\<^sub>L reply\<^sub>B))))"
  and waitA_property : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A implies\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A W\<^sub>D\<^sub>T\<^sub>L reply\<^sub>A)))"
  and waitB_property : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>B implies\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>B W\<^sub>D\<^sub>T\<^sub>L reply\<^sub>B)))"
  and gotA_property : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A) implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))))"
  and gotB_property : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B) implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))))"
  and free_property_A : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(A) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (free implies\<^sub>D\<^sub>T\<^sub>L (free W\<^sub>D\<^sub>T\<^sub>L req)))"
  and free_property_B : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(B) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (free implies\<^sub>D\<^sub>T\<^sub>L (free W\<^sub>D\<^sub>T\<^sub>L req)))"
  and busy_property_A : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(A) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (busy implies\<^sub>D\<^sub>T\<^sub>L (busy W\<^sub>D\<^sub>T\<^sub>L reply)))"
  and busy_property_B : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(B) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (busy implies\<^sub>D\<^sub>T\<^sub>L (busy W\<^sub>D\<^sub>T\<^sub>L reply)))"
  and ready_property_A : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(A) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (ready implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L ready)))"
  and ready_property_B : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(B) (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (ready implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L ready)))"
  and communication_CA : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[(G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (prep implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (\<copyright>\<^sub>A[req]))))]"
  and communication_CB : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[(G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (prep implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (\<copyright>\<^sub>B[req]))))]"
  and communication_AC : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>A[(G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (reply implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (\<copyright>\<^sub>C[reply\<^sub>A]))))]"
  and communication_BC : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>B[(G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (reply implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>k\<^sub>D\<^sub>T\<^sub>L (\<copyright>\<^sub>C[reply\<^sub>B]))))]"
  and assumption_A : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>A[(req implies\<^sub>D\<^sub>T\<^sub>L (F\<^sub>D\<^sub>T\<^sub>L reply))]"
  and assumption_B : "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>B[(req implies\<^sub>D\<^sub>T\<^sub>L (F\<^sub>D\<^sub>T\<^sub>L reply))]"
  shows "\<xi>,3 \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[(prep implies\<^sub>D\<^sub>T\<^sub>L (F\<^sub>D\<^sub>T\<^sub>L (Done)))]"
  apply simp
  