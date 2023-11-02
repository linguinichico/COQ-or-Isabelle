theory dtl
  imports Main "HOL-Library.Omega_Words_Fun"
begin
datatype id = A | B | C

datatype state_proposition  = work | pend | active | got\<^sub>A | got\<^sub>B

fun id_to_state :: "id \<Rightarrow> state_proposition set"
  where
  "id_to_state A = {work, pend}"
| "id_to_state B = {work, pend}"
| "id_to_state C = {active, got\<^sub>A, got\<^sub>B}"

datatype event_state = event | pass 

section \<open>Syntax DTL\<close>

datatype 'a dtl_l =
    True_dtl_l                           ("true\<^sub>D\<^sub>T\<^sub>L")
  | False_dtl_l                          ("false\<^sub>D\<^sub>T\<^sub>L")
  | Prop_dtl_l 'a                        ("prop\<^sub>D\<^sub>T\<^sub>L '(_')")
  | Not_dtl_l "'a  dtl_l"                ("not\<^sub>D\<^sub>T\<^sub>L _" [88] 87)
  | And_dtl_l "'a dtl_l" "'a  dtl_l"     ("_ and\<^sub>D\<^sub>T\<^sub>L _" [88,88] 87)
  | Or_dtl_l "'a dtl_l" "'a dtl_l"       ("_ or\<^sub>D\<^sub>T\<^sub>L _" [88,88] 87)
  | Implies_dtl_l "'a dtl_l" "'a dtl_l"  ("_ implies\<^sub>D\<^sub>T\<^sub>L _" [88,88] 87)
  | Next_dtl_l "'a dtl_l"                ("X\<^sub>D\<^sub>T\<^sub>L _" [88] 87)
  | Finally_dtl_l "'a dtl_l"             ("F\<^sub>D\<^sub>T\<^sub>L _" [88] 87)
  | Global_dtl_l "'a dtl_l"              ("G\<^sub>D\<^sub>T\<^sub>L _" [88] 87)
  | Until_dtl_l "'a dtl_l" "'a dtl_l"    ("_ U\<^sub>D\<^sub>T\<^sub>L _" [88,88] 87)
  | Comms_dltc "id" "'a dtl_l"           ("\<copyright>\<^sub>_'[_']" [82,82] 81)

datatype 'a dtl =
  Identifier "id" "'a dtl_l"             ("@\<^sub>_'[_']" [84,84] 83)

section \<open>Semantics DTL\<close>

fun is_there_events_in_word :: "[(id \<Rightarrow> (event_state \<times> state_proposition set)) word, id, nat] \<Rightarrow> bool"
  where 
  "is_there_events_in_word word i n = (\<exists>j<n. (fst (word j i) = event))"

fun semantics_dtl_local :: "[(id \<Rightarrow> (event_state \<times> state_proposition set)) word, id, state_proposition dtl_l] \<Rightarrow> bool" ("_ \<tturnstile>\<^sub>D\<^sub>T\<^sub>L'(_')  _" [81,81,81] 81)
  where
    "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) true\<^sub>D\<^sub>T\<^sub>L = (\<exists>j. ((fst (\<xi> j i) = event) \<and> is_there_events_in_word \<xi> i j = False) \<longrightarrow> True)"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) false\<^sub>D\<^sub>T\<^sub>L = (\<exists>j. ((fst (\<xi> j i) = event) \<and> is_there_events_in_word \<xi> i j = False) \<longrightarrow> False)"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) prop\<^sub>D\<^sub>T\<^sub>L(q) =  (\<exists>j. ((fst (\<xi> j i) = event) \<and> is_there_events_in_word \<xi> i j = False) \<and> q \<in> snd (\<xi> j i))"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (not\<^sub>D\<^sub>T\<^sub>L \<phi>) = (\<not> (\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>))"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<phi> and\<^sub>D\<^sub>T\<^sub>L \<psi>) = ((\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>) \<and> (\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<psi>))"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<phi> or\<^sub>D\<^sub>T\<^sub>L \<psi>) = ((\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>) \<or> (\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<psi>))"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<phi> implies\<^sub>D\<^sub>T\<^sub>L \<psi>) = ((\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>) \<longrightarrow> (\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<psi>))"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (X\<^sub>D\<^sub>T\<^sub>L \<phi>) = (\<exists>j>0. ((fst (\<xi> j i) = event) \<and> is_there_events_in_word \<xi> i j = False) \<and> (suffix j \<xi>) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>)"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (F\<^sub>D\<^sub>T\<^sub>L \<phi>) = (\<exists>j. (fst (\<xi> j i) = event) \<and> (suffix j \<xi>) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>)" 
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (G\<^sub>D\<^sub>T\<^sub>L \<phi>) = (\<forall>j. (fst (\<xi> j i) = event) \<longrightarrow> (suffix j \<xi>) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>)"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<phi> U\<^sub>D\<^sub>T\<^sub>L \<psi>) = (\<exists>j. (fst (\<xi> j i) = event) \<longrightarrow> (suffix j \<xi>) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<psi> \<and> (\<forall>k<j. (fst(\<xi> k i) = event) \<longrightarrow>  (suffix k \<xi>) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>))"
  | "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) (\<copyright>\<^sub>j[\<phi>]) = (\<exists>k. ((fst (\<xi> k i) = event) \<and> (fst (\<xi> k j) = event)) \<and> ((suffix k \<xi>) \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(j) \<phi>))"

fun semantics_dtl :: "[(id \<Rightarrow> (event_state \<times> state_proposition set)) word, state_proposition dtl] \<Rightarrow> bool "("_ \<tturnstile>\<^sub>D\<^sub>T\<^sub>L _" [79,79] 80)
  where
  "(\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>i[\<phi>]) = (\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(i) \<phi>)"

(*Additional operator to use under protocol proof*)

definition WeakUntil_dtl_l :: "'a dtl_l \<Rightarrow> 'a dtl_l \<Rightarrow> 'a dtl_l"   ("_ W\<^sub>D\<^sub>T\<^sub>L _" [88] 87)
  where 
  "\<phi> W\<^sub>D\<^sub>T\<^sub>L \<psi> \<equiv> (G\<^sub>D\<^sub>T\<^sub>L \<phi>) or\<^sub>D\<^sub>T\<^sub>L (\<phi> U\<^sub>D\<^sub>T\<^sub>L \<psi>)"

section \<open>Definition of Protocol\<close>

(*Setting up protocol transition states*)
(*Transition states for coordinator, represented as "C"*)

definition idle :: "state_proposition dtl_l"
  where 
  "idle \<equiv> ((not\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(active)) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A)))) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B)))"

definition wait\<^sub>A\<^sub>B :: "state_proposition dtl_l"
  where 
  "wait\<^sub>A\<^sub>B \<equiv> (prop\<^sub>D\<^sub>T\<^sub>L(active) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A)))) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B)))"

definition wait\<^sub>A :: "state_proposition dtl_l"
  where 
  "wait\<^sub>A \<equiv> (prop\<^sub>D\<^sub>T\<^sub>L(active) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A)))) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))"

definition wait\<^sub>B :: "state_proposition dtl_l"
  where 
  "wait\<^sub>B \<equiv> (prop\<^sub>D\<^sub>T\<^sub>L(active) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B)))"

definition Done :: "state_proposition dtl_l"
  where 
  "Done \<equiv> (prop\<^sub>D\<^sub>T\<^sub>L(active) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))"

(*Transition states for subordinates, represented as "A" and "B" *)

definition free :: "state_proposition dtl_l"
  where 
  "free \<equiv> prop\<^sub>D\<^sub>T\<^sub>L(work) and\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(pend)))"

definition busy :: "state_proposition dtl_l"
  where 
  "busy \<equiv> prop\<^sub>D\<^sub>T\<^sub>L(work) and\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(pend))"

definition ready :: "state_proposition dtl_l"
  where 
  "ready \<equiv> not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(work))"

(*Coordinator's actions*)

definition prep :: "state_proposition dtl_l"
  where 
  "prep \<equiv> idle and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A\<^sub>B))"

definition reply\<^sub>A :: "state_proposition dtl_l"
  where 
  "reply\<^sub>A \<equiv> (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))) and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A)))"

definition reply\<^sub>B :: "state_proposition dtl_l"
  where 
  "reply\<^sub>B \<equiv> (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))) and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B)))"

(*Subordinates' actions*)

definition req :: "state_proposition dtl_l"
  where 
  "req \<equiv> free and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L busy)"

definition reply :: "state_proposition dtl_l"
  where 
  "reply \<equiv> busy and\<^sub>D\<^sub>T\<^sub>L (X\<^sub>D\<^sub>T\<^sub>L ready)"

lemma property_dtl[simp]:
  "(\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[prep]) \<longrightarrow> (\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[X\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(active))])"
  apply (simp add: prep_def wait\<^sub>A\<^sub>B_def idle_def)
  apply auto
  done

lemma property_dtl_1[simp]:
  "(\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>i[not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(q))]) \<longrightarrow> \<not> (\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>i[(prop\<^sub>D\<^sub>T\<^sub>L(q))])"
  by simp

lemma property_dtl_2[simp]:
  "(\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[X\<^sub>D\<^sub>T\<^sub>L wait\<^sub>A\<^sub>B]) \<longrightarrow> (\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[X\<^sub>D\<^sub>T\<^sub>L (not\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A)))])"
  apply  (simp add:  wait\<^sub>A\<^sub>B_def)
  by auto 

lemma property_dtl_3[simp]:
  "(\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[F\<^sub>D\<^sub>T\<^sub>L wait\<^sub>A\<^sub>B]) \<longrightarrow> (\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[F\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(active))])"
  apply (simp add:  wait\<^sub>A\<^sub>B_def)
  by auto

lemma property_dtl_4[simp] :
  "(\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>A[(\<copyright>\<^sub>C[\<phi>])]) \<longrightarrow> ((\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[F\<^sub>D\<^sub>T\<^sub>L \<phi>]))"
    (is "?fst \<longrightarrow> ?snd")
proof
  assume ?fst
  then obtain k where "(fst(\<xi> k A) = event \<and> fst(\<xi> k C) = event) \<and> suffix k \<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) \<phi>"
    by auto
  then show ?snd 
  proof (cases "\<exists>j. fst(\<xi> j C) = event")
    case True
    then show ?thesis
      using \<open>\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>A[(\<copyright>\<^sub>C[\<phi>])]\<close> by auto 
  next
    case False
    then show ?thesis
    proof -
      show ?thesis
        using False \<open>\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>A[(\<copyright>\<^sub>C[\<phi>])]\<close> semantics_dtl.simps semantics_dtl_local.simps(12) by blast
    qed
  qed
qed

declare [[ smt_timeout = 100 ]]

(*Proof of property with restrictions*)

lemma coordinator_receives_both_replies:
  assumes coordinator_initial_state : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[idle]"
  and subordinator_A_initial_state : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>A[free]"
  and subordinator_B_initial_state : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>B[free]"
  and idle_property : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>D\<^sub>T\<^sub>L (idle implies\<^sub>D\<^sub>T\<^sub>L (idle W\<^sub>D\<^sub>T\<^sub>L prep)))"
  and waitAB_property : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A\<^sub>B implies\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A\<^sub>B W\<^sub>D\<^sub>T\<^sub>L (reply\<^sub>A or\<^sub>D\<^sub>T\<^sub>L reply\<^sub>B))))"
  and waitA_property : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A implies\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>A W\<^sub>D\<^sub>T\<^sub>L reply\<^sub>A)))"
  and waitB_property : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>B implies\<^sub>D\<^sub>T\<^sub>L (wait\<^sub>B W\<^sub>D\<^sub>T\<^sub>L reply\<^sub>B)))"
  and gotA_property : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A) implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>A))))"
  and gotB_property : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(C) (G\<^sub>D\<^sub>T\<^sub>L (prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B) implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>D\<^sub>T\<^sub>L prop\<^sub>D\<^sub>T\<^sub>L(got\<^sub>B))))"
  and free_property_A : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(A) (G\<^sub>D\<^sub>T\<^sub>L (free implies\<^sub>D\<^sub>T\<^sub>L (free W\<^sub>D\<^sub>T\<^sub>L req)))"
  and free_property_B : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(B) (G\<^sub>D\<^sub>T\<^sub>L (free implies\<^sub>D\<^sub>T\<^sub>L (free W\<^sub>D\<^sub>T\<^sub>L req)))"
  and busy_property_A : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(A) (G\<^sub>D\<^sub>T\<^sub>L (busy implies\<^sub>D\<^sub>T\<^sub>L (busy W\<^sub>D\<^sub>T\<^sub>L reply)))"
  and busy_property_B : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(B) (G\<^sub>D\<^sub>T\<^sub>L (busy implies\<^sub>D\<^sub>T\<^sub>L (busy W\<^sub>D\<^sub>T\<^sub>L reply)))"
  and ready_property_A : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(A) (G\<^sub>D\<^sub>T\<^sub>L (ready implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>D\<^sub>T\<^sub>L ready)))"
  and ready_property_B : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L(B) (G\<^sub>D\<^sub>T\<^sub>L (ready implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>D\<^sub>T\<^sub>L ready)))"
  and communication_CA : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[(G\<^sub>D\<^sub>T\<^sub>L (prep implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>D\<^sub>T\<^sub>L (\<copyright>\<^sub>A[req]))))]"
  and communication_CB : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[(G\<^sub>D\<^sub>T\<^sub>L (prep implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>D\<^sub>T\<^sub>L (\<copyright>\<^sub>B[req]))))]"
  and communication_AC : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>A[(G\<^sub>D\<^sub>T\<^sub>L (reply implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>D\<^sub>T\<^sub>L (\<copyright>\<^sub>C[reply\<^sub>A]))))]"
  and communication_BC : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>B[(G\<^sub>D\<^sub>T\<^sub>L (reply implies\<^sub>D\<^sub>T\<^sub>L (G\<^sub>D\<^sub>T\<^sub>L (\<copyright>\<^sub>C[reply\<^sub>B]))))]"
  and assumption_A : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>A[(req implies\<^sub>D\<^sub>T\<^sub>L (F\<^sub>D\<^sub>T\<^sub>L reply))]"
  and assumption_B : "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>B[(req implies\<^sub>D\<^sub>T\<^sub>L (F\<^sub>D\<^sub>T\<^sub>L reply))]"
shows "\<xi> \<tturnstile>\<^sub>D\<^sub>T\<^sub>L @\<^sub>C[(prep implies\<^sub>D\<^sub>T\<^sub>L (F\<^sub>D\<^sub>T\<^sub>L (Done)))]"
  using assms
  apply (simp add: idle_def free_def wait\<^sub>A\<^sub>B_def wait\<^sub>A_def wait\<^sub>B_def busy_def ready_def prep_def Done_def reply\<^sub>A_def reply\<^sub>B_def reply_def)
  by (metis (no_types, opaque_lifting) add.right_neutral not_gr_zero)
(*
  proof -
  assume a1: "(\<forall>j. fst (\<xi> j C) = event \<longrightarrow> (\<exists>ja<j. fst (\<xi> ja C) = event) \<or> active \<notin> snd (\<xi> j C)) \<and> (\<forall>j. fst (\<xi> j C) = event \<longrightarrow> (\<exists>ja<j. fst (\<xi> ja C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> j C)) \<and> (\<forall>j. fst (\<xi> j C) = event \<longrightarrow> (\<exists>ja<j. fst (\<xi> ja C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> j C))"
  have f2: "\<forall>x0 x1. (fst (\<xi> (x1 + x0) C) = event \<longrightarrow> (\<exists>v2<x0. fst (\<xi> (x1 + v2) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (x1 + x0) C)) = (fst (\<xi> (x1 + x0) C) \<noteq> event \<or> (\<exists>v2<x0. fst (\<xi> (x1 + v2) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (x1 + x0) C))"
    by auto
  have "\<forall>x0 x1. (fst (\<xi> (x1 + x0) C) = event \<longrightarrow> (\<exists>v2<x0. fst (\<xi> (x1 + v2) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (x1 + x0) C)) = (fst (\<xi> (x1 + x0) C) \<noteq> event \<or> (\<exists>v2<x0. fst (\<xi> (x1 + v2) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (x1 + x0) C))"
    by auto
  then have f3: "\<forall>n. ((\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C))) = ((\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C)))"
    using f2
    by blast 
  have f4: "\<forall>x0 x1 x2. (x0 < x1 \<longrightarrow> fst (\<xi> (x2 + x0) C) \<noteq> event) = (\<not> x0 < x1 \<or> fst (\<xi> (x2 + x0) C) \<noteq> event)"
    by auto
  then have f5: "\<forall>n. ((\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C))) = ((\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C)))"
    using f3
    by auto 
  have "\<forall>x0 x1. (x0 < x1 \<longrightarrow> fst (\<xi> x0 C) \<noteq> event) = (\<not> x0 < x1 \<or> fst (\<xi> x0 C) \<noteq> event)"
    by auto
  then have "\<forall>n. ((\<forall>na<n. fst (\<xi> na C) \<noteq> event) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C))) = ((\<forall>na. \<not> na < n \<or> fst (\<xi> na C) \<noteq> event) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C)))"
    using f5
    by presburger 
  then have f6: "((\<exists>n>0. fst (\<xi> n C) = event \<and> (\<forall>na<n. fst (\<xi> na C) \<noteq> event) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C))) \<longrightarrow> (\<exists>n. fst (\<xi> n C) = event \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (n + na) C)))) = ((\<exists>n>0. fst (\<xi> n C) = event \<and> (\<forall>na. \<not> na < n \<or> fst (\<xi> na C) \<noteq> event) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C))) \<longrightarrow> (\<exists>n. fst (\<xi> n C) = event \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (n + na) C))))"
    using f4
    by presburger          
  have "((\<exists>v0>0. fst (\<xi> v0 C) = event \<and> (\<forall>v1. \<not> v1 < v0 \<or> fst (\<xi> v1 C) \<noteq> event) \<and> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> active \<in> snd (\<xi> (v0 + v1) C)) \<and> (\<forall>v1. fst (\<xi> (v0 + v1) C) \<noteq> event \<or> (\<exists>v2<v1. fst (\<xi> (v0 + v2) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (v0 + v1) C)) \<and> (\<forall>v1. fst (\<xi> (v0 + v1) C) \<noteq> event \<or> (\<exists>v2<v1. fst (\<xi> (v0 + v2) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (v0 + v1) C))) \<longrightarrow> (\<exists>v0. fst (\<xi> v0 C) = event \<and> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> active \<in> snd (\<xi> (v0 + v1) C)) \<and> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (v0 + v1) C)) \<and> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (v0 + v1) C)))) = ((\<forall>v0. \<not> 0 < v0 \<or> fst (\<xi> v0 C) \<noteq> event \<or> (\<exists>v1<v0. fst (\<xi> v1 C) = event) \<or> (\<forall>v1. fst (\<xi> (v0 + v1) C) \<noteq> event \<or> (\<exists>v2<v1. fst (\<xi> (v0 + v2) C) = event) \<or> active \<notin> snd (\<xi> (v0 + v1) C)) \<or> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (v0 + v1) C)) \<or> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (v0 + v1) C))) \<or> (\<exists>v0. fst (\<xi> v0 C) = event \<and> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> active \<in> snd (\<xi> (v0 + v1) C)) \<and> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (v0 + v1) C)) \<and> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (v0 + v1) C))))"
    sorry
  then have f7: "((\<exists>n>0. fst (\<xi> n C) = event \<and> (\<forall>na<n. fst (\<xi> na C) \<noteq> event) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C))) \<longrightarrow> (\<exists>n. fst (\<xi> n C) = event \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (n + na) C)))) = ((\<forall>n. \<not> 0 < n \<or> fst (\<xi> n C) \<noteq> event \<or> (\<exists>na<n. fst (\<xi> na C) = event) \<or> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> active \<notin> snd (\<xi> (n + na) C)) \<or> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (n + na) C)) \<or> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (n + na) C))) \<or> (\<exists>n. fst (\<xi> n C) = event \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (n + na) C))))"
    using f6
    by presburger 
  have f8: "\<forall>x0. (\<exists>v2<x0. fst (\<xi> (v0_0 + v2) C) = event) = (v2_2 x0 < x0 \<and> fst (\<xi> (v0_0 + v2_2 x0) C) = event)"
    sorry
  obtain nn :: "nat \<Rightarrow> nat" where
    f9: "\<forall>x0. (\<exists>v2<x0. fst (\<xi> (v0_0 + v2) C) = event) = (nn x0 < x0 \<and> fst (\<xi> (v0_0 + nn x0) C) = event)"
    sorry
  obtain nna :: nat where
    "(\<exists>v1. fst (\<xi> (v0_0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0_0 + v2) C) \<noteq> event) \<and> active \<in> snd (\<xi> (v0_0 + v1) C)) = (fst (\<xi> (v0_0 + nna) C) = event \<and> (\<forall>v2. \<not> v2 < nna \<or> fst (\<xi> (v0_0 + v2) C) \<noteq> event) \<and> active \<in> snd (\<xi> (v0_0 + nna) C))"
    by blast
  then have f10: "(0 < v0_0 \<and> fst (\<xi> v0_0 C) = event \<and> (\<forall>n. \<not> n < v0_0 \<or> fst (\<xi> n C) \<noteq> event) \<and> (\<exists>n. fst (\<xi> (v0_0 + n) C) = event \<and> (\<forall>na. \<not> na < n \<or> fst (\<xi> (v0_0 + na) C) \<noteq> event) \<and> active \<in> snd (\<xi> (v0_0 + n) C)) \<and> (\<forall>n. fst (\<xi> (v0_0 + n) C) \<noteq> event \<or> (\<exists>na<n. fst (\<xi> (v0_0 + na) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (v0_0 + n) C)) \<and> (\<forall>n. fst (\<xi> (v0_0 + n) C) \<noteq> event \<or> (\<exists>na<n. fst (\<xi> (v0_0 + na) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (v0_0 + n) C))) = (0 < v0_0 \<and> fst (\<xi> v0_0 C) = event \<and> (\<forall>n. \<not> n < v0_0 \<or> fst (\<xi> n C) \<noteq> event) \<and> (fst (\<xi> (v0_0 + nna) C) = event \<and> (\<forall>n. \<not> n < nna \<or> fst (\<xi> (v0_0 + n) C) \<noteq> event) \<and> active \<in> snd (\<xi> (v0_0 + nna) C)) \<and> (\<forall>n. fst (\<xi> (v0_0 + n) C) \<noteq> event \<or> nn n < n \<and> fst (\<xi> (v0_0 + nn n) C) = event \<or> got\<^sub>A \<notin> snd (\<xi> (v0_0 + n) C)) \<and> (\<forall>n. fst (\<xi> (v0_0 + n) C) \<noteq> event \<or> nn n < n \<and> fst (\<xi> (v0_0 + nn n) C) = event \<or> got\<^sub>B \<notin> snd (\<xi> (v0_0 + n) C)))"
    using f8 f9
    by simp 
  obtain nnb :: nat where
    "(\<exists>v0>0. fst (\<xi> v0 C) = event \<and> (\<forall>v1. \<not> v1 < v0 \<or> fst (\<xi> v1 C) \<noteq> event) \<and> (\<exists>v1. fst (\<xi> (v0 + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (v0 + v2) C) \<noteq> event) \<and> active \<in> snd (\<xi> (v0 + v1) C)) \<and> (\<forall>v1. fst (\<xi> (v0 + v1) C) \<noteq> event \<or> (\<exists>v2<v1. fst (\<xi> (v0 + v2) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (v0 + v1) C)) \<and> (\<forall>v1. fst (\<xi> (v0 + v1) C) \<noteq> event \<or> (\<exists>v2<v1. fst (\<xi> (v0 + v2) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (v0 + v1) C))) = (0 < nnb \<and> fst (\<xi> nnb C) = event \<and> (\<forall>v1. \<not> v1 < nnb \<or> fst (\<xi> v1 C) \<noteq> event) \<and> (\<exists>v1. fst (\<xi> (nnb + v1) C) = event \<and> (\<forall>v2. \<not> v2 < v1 \<or> fst (\<xi> (nnb + v2) C) \<noteq> event) \<and> active \<in> snd (\<xi> (nnb + v1) C)) \<and> (\<forall>v1. fst (\<xi> (nnb + v1) C) \<noteq> event \<or> (\<exists>v2<v1. fst (\<xi> (nnb + v2) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (nnb + v1) C)) \<and> (\<forall>v1. fst (\<xi> (nnb + v1) C) \<noteq> event \<or> (\<exists>v2<v1. fst (\<xi> (nnb + v2) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (nnb + v1) C)))"
    sorry (* by (smt (z3)) Time out *)
  then have f11: "(\<exists>n>0. fst (\<xi> n C) = event \<and> (\<forall>na. \<not> na < n \<or> fst (\<xi> na C) \<noteq> event) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C))) = (0 < nnb \<and> fst (\<xi> nnb C) = event \<and> (\<forall>n. \<not> n < nnb \<or> fst (\<xi> n C) \<noteq> event) \<and> (fst (\<xi> (nnb + nna) C) = event \<and> (\<forall>n. \<not> n < nna \<or> fst (\<xi> (nnb + n) C) \<noteq> event) \<and> active \<in> snd (\<xi> (nnb + nna) C)) \<and> (\<forall>n. fst (\<xi> (nnb + n) C) \<noteq> event \<or> nn n < n \<and> fst (\<xi> (nnb + nn n) C) = event \<or> got\<^sub>A \<notin> snd (\<xi> (nnb + n) C)) \<and> (\<forall>n. fst (\<xi> (nnb + n) C) \<noteq> event \<or> nn n < n \<and> fst (\<xi> (nnb + nn n) C) = event \<or> got\<^sub>B \<notin> snd (\<xi> (nnb + n) C)))"
    using f10
    sorry
  have "\<not> 0 < nnb \<or> fst (\<xi> nnb C) \<noteq> event \<or> (\<exists>n<nnb. fst (\<xi> n C) = event) \<or> (fst (\<xi> (nnb + nna) C) \<noteq> event \<or> (\<exists>n<nna. fst (\<xi> (nnb + n) C) = event) \<or> active \<notin> snd (\<xi> (nnb + nna) C)) \<or> (\<exists>n. fst (\<xi> (nnb + n) C) = event \<and> (\<not> nn n < n \<or> fst (\<xi> (nnb + nn n) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (nnb + n) C)) \<or> (\<exists>n. fst (\<xi> (nnb + n) C) = event \<and> (\<not> nn n < n \<or> fst (\<xi> (nnb + nn n) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (nnb + n) C))"
    using a1 by (metis add.commute add_cancel_left_left gr0I)
  then have "(\<forall>n. \<not> 0 < n \<or> fst (\<xi> n C) \<noteq> event \<or> (\<exists>na<n. fst (\<xi> na C) = event) \<or> (\<forall>na. fst (\<xi> (n + na) C) \<noteq> event \<or> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> active \<notin> snd (\<xi> (n + na) C)) \<or> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (n + na) C)) \<or> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (n + na) C))) \<or> (\<exists>n. fst (\<xi> n C) = event \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb. \<not> nb < na \<or> fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (n + na) C)))"
    using f11 sorry
  then show "(\<exists>n>0. fst (\<xi> n C) = event \<and> (\<forall>na<n. fst (\<xi> na C) \<noteq> event) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>A \<notin> snd (\<xi> (n + na) C)) \<and> (\<forall>na. fst (\<xi> (n + na) C) = event \<longrightarrow> (\<exists>nb<na. fst (\<xi> (n + nb) C) = event) \<or> got\<^sub>B \<notin> snd (\<xi> (n + na) C))) \<longrightarrow> (\<exists>n. fst (\<xi> n C) = event \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> active \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>A \<in> snd (\<xi> (n + na) C)) \<and> (\<exists>na. fst (\<xi> (n + na) C) = event \<and> (\<forall>nb<na. fst (\<xi> (n + nb) C) \<noteq> event) \<and> got\<^sub>B \<in> snd (\<xi> (n + na) C)))"
    using f7
    by presburger 
qed
*)