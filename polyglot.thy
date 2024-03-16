section\<open>Representing Polyglots\<close>

text\<open> 
  In this theory, we define the basic data type and the notion of validity 
  for polyglot programs. A polyglot program is a program, at the same time, 
  is valid in multiple programming languages. For example, the following 
  polyglot is both a valid Python program and a valid C program:
\begin{verbatim}
#if 0
if __name__ == '__main__':
    print("Hello Python")
#endif
#if 0
""" "
#endif
#include <stdio.h>
int main() {
  printf("Hello in C\n");
  return 0;
}
#if 0
" """
#endif
\end{verbatim}
\<close>

(*<*)
theory
  polyglot
imports
  program
begin 
(*>*)

subsection\<open>Representing Polyglots\<close>

text\<open>
  We model a polyglot as a set of ``regular'' programs that need to fulfill certain 
  requirements. We are currently using a straight-forward modelling approach. In the 
  future it might be advisable to use Isabelle's locale mechanism (conceptually, an extension 
  of type classes) to formally capture the requirements for polyglots). 
\<close>

type_synonym polyglot = "(pl \<times> program) set"

subsubsection\<open>Example\<close>

text\<open>
 We now can model simple polyglot programs. For example, the following program is a simple 
 ``Hello World'' program that is valid in C and Python. 
\<close>

definition 
\<open>hello_world_python_poly = linecomment \<open>#if 0\<close>;
                           rmcomments hello_world_python;
                           linecomment \<open>#endif\<close>;
                           linecomment \<open>#if 0\<close>;
                           blockcomment 
                             \<open>""" "\<close>
                               (linecomment \<open>#endif\<close>; 
                                rmcomments hello_world_c; 
                                linecomment \<open>#if 0\<close>)
                             \<open>" """\<close>;
                           linecomment \<open>#endif\<close>
                         \<close> 

definition
\<open>hello_world_c_poly      = blockcomment 
                             \<open>#if 0\<newline>\<close>
                               (rmcomments hello_world_python)
                             \<open>#endif\<newline>\<close>;
                           blockcomment 
                             \<open>#if 0\<newline>\<close>
                               (block \<open>""" "\<close>)
                             \<open>#endif\<newline>\<close>;
                           rmcomments hello_world_c; 
                           blockcomment 
                             \<open>#if 0\<newline>\<close>
                               (block \<open>" """\<close>)
                             \<open>#endif\<newline>\<close>
                         \<close> 

value "hackish_print_prg hello_world_python_poly"
value "hackish_print_prg hello_world_c_poly"

lemma validP_hello_world_c_poly: "C \<Turnstile> hello_world_c_poly"
  by(code_simp)
          
lemma validP_hello_world_python_poly: "(Python \<Turnstile> hello_world_python_poly)"
  by(code_simp)

lemma string_of_program_c_python: "string_of_program hello_world_c_poly = string_of_program hello_world_python_poly"
  by(code_simp)

definition hello_world_c_python::polyglot  where
\<open>hello_world_c_python = {(C, hello_world_c_poly), (Python, hello_world_python_poly)}\<close>

definition "valid_poly pls P = (
                                 ( \<forall> p \<in> P.((fst p) \<Turnstile> (snd p)) 
                               \<and> (\<forall> p' \<in> P.(string_of_program (snd p) = 
                                 string_of_program (snd p'))))
                               \<and> pls \<subseteq> fst `  P
                               )"

definition compose_python_poly :: "program \<Rightarrow> program \<Rightarrow> program" where
\<open>compose_python_poly python_prog c_prog = linecomment \<open>#if 0\<close>;
                                    rmcomments python_prog;
                                    linecomment \<open>#endif\<close>;
                                    linecomment \<open>#if 0\<close>;
                                    blockcomment 
                                    \<open>""" "\<close>
                                    (linecomment \<open>#endif\<close>; 
                                    rmcomments c_prog;
                                    linecomment \<open>#if 0\<close>)
                                    \<open>" """\<close>;
                                    linecomment \<open>#endif\<close>
                                    \<close> 

definition compose_c_poly :: "program \<Rightarrow> program \<Rightarrow> program" where
\<open>compose_c_poly python_prog c_prog = blockcomment 
                             \<open>#if 0\<newline>\<close>
                               (rmcomments python_prog)
                             \<open>#endif\<newline>\<close>;
                           blockcomment 
                             \<open>#if 0\<newline>\<close>
                               (block \<open>""" "\<close>)
                             \<open>#endif\<newline>\<close>;
                           rmcomments c_prog; 
                           blockcomment 
                             \<open>#if 0\<newline>\<close>
                               (block \<open>" """\<close>)
                             \<open>#endif\<newline>\<close>
                         \<close>

value "compose_python_poly hello_world_python hello_world_c"
value "compose_c_poly hello_world_python hello_world_c"
value "string_of_program (compose_python_poly hello_world_python hello_world_c)"
value "hackish_non_printable_CHRs(string_of_program
       (compose_python_poly hello_world_python hello_world_c))"
value "string_of_program (compose_python_poly hello_world_python hello_world_c) = 
       string_of_program (compose_c_poly hello_world_python hello_world_c)"

definition c_python_poly :: "program \<Rightarrow> program \<Rightarrow> polyglot" where
\<open>c_python_poly python_prog c_prog = {(C, (compose_c_poly python_prog c_prog)),
                                    (Python, (compose_python_poly python_prog c_prog))}\<close>

definition mk_c_python_poly:: "program \<Rightarrow> program \<Rightarrow> polyglot" where
"mk_c_python_poly c_prog python_prog = (if (C \<Turnstile> c_prog) \<and> (Python \<Turnstile> python_prog)
                                       then {
                                             (Python, compose_python_poly python_prog c_prog),
                                             (C, compose_c_poly python_prog c_prog)
                                            }
                                       else {})"

value "mk_c_python_poly hello_world_c hello_world_python"
value "Python \<Turnstile> (compose_python_poly hello_world_python hello_world_c)"
value "C \<Turnstile> (compose_c_poly hello_world_python hello_world_c)"
value "rmcomments (\<B> '''')"
value "rmcomments (linecomment \<open>#endif\<close>)"

lemma set_next: "set x \<noteq> set y \<Longrightarrow> x \<noteq> y"
  by(auto)

(* we need to prove a number of properties of validP and semi *)

lemma validP_p_semi: "P \<Turnstile> (p;q) \<Longrightarrow> P \<Turnstile> p"
  by simp

lemma validP_q_semi: "P \<Turnstile> (p;q) \<Longrightarrow> P \<Turnstile> q"
  by simp

lemma sublist_append_split1: "(\<not> sublist s  (l1@l2)) \<Longrightarrow> ((\<not> sublist s l1) \<and> (\<not>  sublist s l2))"
  using sublist_append by blast

lemma sublist_append_split2: "(\<not> sublist [c::char] l1) \<Longrightarrow> (\<not>  sublist [c] l2) \<Longrightarrow> (\<not> sublist [c] (l1@l2))"
  using Cons_eq_append_conv append_Nil2 append_butlast_last_id last_ConsL 
       last_appendR prefix_order.dual_order.refl same_suffix_nil sublist_altdef sublist_append suffix_append
proof -
  assume a1: "\<not> sublist [c] l1"
  assume a2: "\<not> sublist [c] l2"
  obtain ccs :: "char list \<Rightarrow> char list \<Rightarrow> char list \<Rightarrow> char list" and ccsa :: 
    "char list \<Rightarrow> char list \<Rightarrow> char list \<Rightarrow> char list" where
    "\<forall>x0 x1 x2. (\<exists>v3 v4. x2 = v3 @ v4 \<and> suffix v3 x1 \<and> prefix v4 x0) = 
     (x2 = ccs x0 x1 x2 @ ccsa x0 x1 x2 \<and> suffix (ccs x0 x1 x2) x1 \<and> prefix (ccsa x0 x1 x2) x0)"
    by moura
  then have f3: "\<forall>cs csa csb. (\<not> sublist cs (csa @ csb) \<or> sublist cs csa \<or> sublist cs csb \<or> cs 
    = ccs csb csa cs @ ccsa csb csa cs \<and> suffix (ccs csb csa cs) csa \<and> 
    prefix (ccsa csb csa cs) csb) \<and> (sublist cs (csa @ csb) \<or> \<not> sublist cs csa \<and> 
    \<not> sublist cs csb \<and> (\<forall>csc csd. cs \<noteq> csc @ csd \<or> \<not> suffix csc csa \<or> \<not> prefix csd csb))"
    by(auto,simp_all add: sublist_append, blast)
  obtain ccsb :: "char list \<Rightarrow> char list \<Rightarrow> char list \<Rightarrow> char \<Rightarrow> char list" where
    "\<forall>x0 x1 x2 x3. (\<exists>v4. x3 # v4 = x1 \<and> x2 = v4 @ x0) = (x3 # ccsb x0 x1 x2 x3 = x1 \<and> x2 = 
    ccsb x0 x1 x2 x3 @ x0)"
    by moura
  then have f4: "\<forall>c cs csa csb. (c # cs \<noteq> csa @ csb \<or> csa = [] \<and> c # cs = csb 
    \<or> c # ccsb csb csa cs c = csa \<and> cs = ccsb csb csa cs c @ csb) \<and> (c # cs = csa @ csb 
    \<or> (csa \<noteq> [] \<or> c # cs \<noteq> csb) \<and> (\<forall>csc. c # csc \<noteq> csa \<or> cs \<noteq> csc @ csb))"
    by (meson Cons_eq_append_conv)
  have "(c # ccsb (ccsa l2 l1 [c]) (ccs l2 l1 [c]) [] c \<noteq> ccs l2 l1 [c] \<or> [] \<noteq> 
       ccsb (ccsa l2 l1 [c]) (ccs l2 l1 [c]) [] c @ ccsa l2 l1 [c]) \<or> [c] \<noteq> ccs l2 l1 [c] @ 
        ccsa l2 l1 [c] \<or> \<not> suffix (ccs l2 l1 [c]) l1 \<or> \<not> prefix (ccsa l2 l1 [c]) l2"
    using f3 a1 by (metis (no_types) Nil_is_append_conv append_Nil2 prefix_order.dual_order.refl)
  then show ?thesis
    using same_suffix_nil sublist_altdef a1 a2 f3 f4
    by (smt (z3))
qed

  
lemma validP_c_python_progs: " C \<Turnstile> \<llangle> ''#if 0\<newline>'' (rmcomments python_prog1) ''#endif\<newline>'' \<rrangle> 
  \<Longrightarrow> C \<Turnstile> \<llangle> ''#if 0\<newline>'' (rmcomments python_prog2) ''#endif\<newline>'' \<rrangle> 
  \<Longrightarrow>  C \<Turnstile> \<llangle> ''#if 0\<newline>'' (rmcomments (python_prog1 ; python_prog2)) ''#endif\<newline>'' \<rrangle>"
  apply(simp add: rmcomments_def rm_start_end_comment_def Let_def)
  apply(code_simp, auto)
  using sublist_append_split2
  by simp


lemma rmcomments_p1_p2: "rmcomments p1 \<noteq> SKIP \<Longrightarrow> rmcomments p2 \<noteq> SKIP \<Longrightarrow>
 (rmcomments (p1;p2)) = (rmcomments ((rmcomments p1);(rmcomments p2)))"
proof( induction "p1")
  case SKIP
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  qed
next
  case (block x)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  qed
next
  case (linecomment x)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (smt comments2skip.simps(1) comments2skip.simps(4) comments2skip.simps(5) 
         comp_apply rmcomments_def rmskip.simps(1) rmskip.simps(2))
  qed
next
  case (blockcomment x1 x2a x3a)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case 
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case 
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case 
      by (simp add: rmcomments_def) 
  next
    case (blockcomment x1 p2 x3a)
    then show ?case 
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  qed
next
  case (semi x1 x2a)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (smt comments2skip.simps(1) comments2skip.simps(5) comp_def rmcomments_def rmskip.simps(1) 
         rmskip.simps(2))
  next
    case (block x)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  next
    case (linecomment x)
    then show ?case 
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (smt comments2skip.simps(1) comments2skip.simps(3) comments2skip.simps(5) comp_apply 
          rmcomments_def rmskip.simps(1) rmskip.simps(2))
  next
    case (semi p21 p22)
    then show ?case  by (metis (no_types, lifting) comments2skip.simps(5) comp_apply rmcomments_def 
                     rmcomments_2x rmskip.simps(1))
  qed
qed


lemma rmcomments_SKIP_p2: "rmcomments p2 \<noteq> SKIP \<Longrightarrow>
 (rmcomments (p1;p2)) = (rmcomments ((rmcomments p1);(rmcomments p2)))"
proof( induction "p1")
  case SKIP
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  qed
next
  case (block x)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  qed
next
  case (linecomment x)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      using comments2skip.simps(1) comments2skip.simps(4) comments2skip.simps(5) comp_apply 
            rmcomments_def rmcomments_p1_p2 rmskip.simps(1)
      apply(simp)
      by (metis (no_types, hide_lams) comments2skip.simps(1) comments2skip.simps(4) 
         comments2skip.simps(5) comp_eq_elim comp_id id_apply rmcomments_2x rmcomments_def 
         rmcomments_p1_p2 rmskip_skip_p semi.prems)
  qed
next
  case (blockcomment x1 x2a x3a)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case 
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case 
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case 
      by (simp add: rmcomments_def) 
  next
    case (blockcomment x1 p2 x3a)
    then show ?case 
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  qed
next
  case (semi x1 x2a)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (smt comments2skip.simps(1) comments2skip.simps(5) comp_def rmcomments_def rmskip.simps(1) 
          rmskip.simps(2))
  next
    case (block x)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  next
    case (linecomment x)
    then show ?case 
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (smt comments2skip.simps(1) comments2skip.simps(3) comments2skip.simps(5) comp_apply 
          rmcomments_def rmskip.simps(1) rmskip.simps(2))
  next
    case (semi p21 p22)
    then show ?case  by (metis (no_types, lifting) comments2skip.simps(5) comp_apply rmcomments_def 
                         rmcomments_2x rmskip.simps(1))
  qed
qed

(* Proof sketch by induction *)
lemma rmcomments_p1_p2_general: 
"(rmcomments (p1;p2)) = (rmcomments ((rmcomments p1);(rmcomments p2)))" 
proof(induction "p1")
  case SKIP
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  qed
next
  case (block x)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  qed
next
  case (linecomment x)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case
      by (simp add: rmcomments_def)  
  next
    case (linecomment x)
    then show ?case
      by (simp add: rmcomments_def)  
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (simp add: rmcomments_def)  
  next
    case (semi p21 p22)
    then show ?case
      using comments2skip.simps(1) comments2skip.simps(4) comments2skip.simps(5) comp_apply 
            rmcomments_def rmskip.simps(1) rmskip.simps(2)
      apply (simp)
      by (metis comments2skip.simps(1) comments2skip.simps(4) comments2skip.simps(5) comp_apply 
          rmcomments_SKIP_p2 rmskip_p_skip rmskip_skip_p)
    qed
next
  case (blockcomment x1 x2a x3a)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case 
      by (simp add: rmcomments_def)
  next
    case (block x)
    then show ?case 
      by (simp add: rmcomments_def)
  next
    case (linecomment x)
    then show ?case 
      by (simp add: rmcomments_def) 
  next
    case (blockcomment x1 p2 x3a)
    then show ?case 
      by (simp add: rmcomments_def)
  next
    case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  qed

next
  case (semi x1 x2a)
  then show ?case 
  proof(induction "p2")
    case SKIP
    then show ?case
      by (metis comments2skip.simps(1) comments2skip.simps(5) comp_apply rmcomments_2x 
          rmcomments_SKIP_p2 rmcomments_def rmskip_p_skip)
  next
    case (block x)
    then show ?case
      by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  next
    case (linecomment x)
    then show ?case 
by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x rmskip.simps(1))
  next
    case (blockcomment x1 p2 x3a)
    then show ?case
      by (metis comments2skip.simps(1) comments2skip.simps(3) comments2skip.simps(5) 
          comp_eq_dest_lhs rmcomments_2x rmcomments_SKIP_p2 rmcomments_def rmskip_p_skip)  
  next  case (semi p21 p22)
    then show ?case
      by (metis comments2skip.simps(5) comp_def rmcomments_2x rmcomments_def rmskip.simps(1))  
  qed
qed

(* Proof sketch by cases *)
lemma rmcomments_p1_p2_general_2x: 
"(rmcomments (p1;p2)) = (rmcomments ((rmcomments p1);(rmcomments p2)))" 
proof(cases "rmcomments p1 = SKIP")
  case True 
  then show ?thesis 
  proof(cases "rmcomments p2 = SKIP")
    case True
    from \<open>rmcomments p1 = SKIP\<close> and \<open>rmcomments p2 = SKIP\<close> 
    show ?thesis by (simp add: rmcomments_def)
  next
    case False
    from \<open>rmcomments p1 = SKIP\<close> and \<open>rmcomments p2 \<noteq> SKIP\<close> 
    show ?thesis by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x 
                     rmskip.simps(1))
  qed
next
  case False
  then show ?thesis 
  proof(cases "rmcomments p2 = SKIP")
    case True
    from \<open>rmcomments p1 \<noteq> SKIP\<close> and \<open>rmcomments p2 = SKIP\<close> 
    show ?thesis by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x 
                     rmskip.simps(1))
  next
    case False
    from \<open>rmcomments p1 \<noteq> SKIP\<close> and \<open>rmcomments p2 \<noteq> SKIP\<close> 
    show ?thesis by (metis comments2skip.simps(5) comp_apply rmcomments_def rmcomments_2x 
                     rmskip.simps(1))
  qed
qed

definition "python_valid_ifdef_c p = (C \<Turnstile> (blockcomment 
                             \<open>#if 0\<newline>\<close>
                               (rmcomments p)
                             \<open>#endif\<newline>\<close>))"
(* In our current definition of the C language, this ensures that the Python 
   program p, after removing comments, does not contain any # characters *)


lemma valid_poly_compose_c_poly: assumes "C \<Turnstile> c_prog"
          and "Python \<Turnstile> python_prog"
          and "python_valid_ifdef_c python_prog" 
      shows
     "valid_poly {C} {(C, compose_c_poly python_prog c_prog)}"
using assms proof (induction "c_prog")
  case SKIP
  then show ?case  proof (induction "python_prog")
    case SKIP
    then show ?case by code_simp 
  next 
    case (block x) note * = this 
         have "(\<forall>ps ss. [CHR 0x22, CHR 0x22, CHR 0x22, CHR '' '', CHR 0x22] \<noteq> ps @ CHR ''#'' # ss) 
            \<and> (\<forall>ps ss. [CHR 0x22, CHR '' '', CHR 0x22, CHR 0x22, CHR 0x22] \<noteq> ps @ CHR ''#'' # ss)" 
       by(rule conjI, (rule allI, rule allI, rule set_next, (auto)[1])+)
     then show ?case using * 
      by(simp  add: valid_poly_def compose_c_poly_def rmcomments_def 
                    C_def rm_start_end_comment_def sublist_def Python_def python_valid_ifdef_c_def)
  next
    case (linecomment x)
    then show ?case by(code_simp)
  next
    case (blockcomment x1 python_prog x3a)
    then show ?case by(code_simp)
  next
    case (semi python_prog1 python_prog2) 
    then show ?case  
      apply(code_simp, auto) 
      using sublist_append apply blast 
      using sublist_append by blast
  qed
next
  case (block x)
  then show ?case proof (induction python_prog)
    case SKIP note * = this 
         have "(\<forall>ps ss. [CHR 0x22, CHR 0x22, CHR 0x22, CHR '' '', CHR 0x22] \<noteq> ps @ CHR ''#'' # ss) 
             \<and> (\<forall>ps ss. [CHR 0x22, CHR '' '', CHR 0x22, CHR 0x22, CHR 0x22] \<noteq> ps @ CHR ''#'' # ss)" 
       by(rule conjI, (rule allI, rule allI, rule set_next, (auto)[1])+)
     then show ?case using * 
      by(simp  add: valid_poly_def compose_c_poly_def rmcomments_def 
                    C_def rm_start_end_comment_def sublist_def Python_def python_valid_ifdef_c_def)
    next
    case (block x) note * = this 
         have "(\<forall>ps ss. [CHR 0x22, CHR 0x22, CHR 0x22, CHR '' '', CHR 0x22] \<noteq> ps @ CHR ''#'' # ss) 
             \<and> (\<forall>ps ss. [CHR 0x22, CHR '' '', CHR 0x22, CHR 0x22, CHR 0x22] \<noteq> ps @ CHR ''#'' # ss)" 
       by(rule conjI, (rule allI, rule allI, rule set_next, (auto)[1])+)
     then show ?case using * 
      by(simp  add: valid_poly_def compose_c_poly_def rmcomments_def 
                     C_def rm_start_end_comment_def sublist_def Python_def python_valid_ifdef_c_def)
  next
    case (linecomment x) note * = this 
            have "(\<forall>ps ss. [CHR 0x22, CHR 0x22,CHR 0x22,CHR '' '', CHR 0x22] \<noteq> ps @ CHR ''#'' # ss) 
             \<and> (\<forall>ps ss. [CHR 0x22, CHR '' '', CHR 0x22, CHR 0x22, CHR 0x22] \<noteq> ps @ CHR ''#'' # ss)" 
       by(rule conjI, (rule allI, rule allI, rule set_next, (auto)[1])+)
     then show ?case using *
      by(simp  add: valid_poly_def compose_c_poly_def rmcomments_def 
                    C_def rm_start_end_comment_def sublist_def Python_def python_valid_ifdef_c_def)
  next
    case (blockcomment x1 python_prog x3a)
     note * = this 
            have "(\<forall>ps ss. [CHR 0x22,CHR 0x22,CHR 0x22, CHR '' '', CHR 0x22] \<noteq> ps @ CHR ''#'' # ss) 
             \<and> (\<forall>ps ss. [CHR 0x22, CHR '' '', CHR 0x22, CHR 0x22, CHR 0x22] \<noteq> ps @ CHR ''#'' # ss)" 
       by(rule conjI, (rule allI, rule allI, rule set_next, (auto)[1])+)
     then show ?case using *
      by(simp  add: valid_poly_def compose_c_poly_def rmcomments_def 
                    C_def rm_start_end_comment_def sublist_def Python_def python_valid_ifdef_c_def)
  next
    case (semi python_prog1 python_prog2)
    then show ?case  
      apply(code_simp, auto) 
      using sublist_append apply blast
      using sublist_append by blast
  qed
next
  case (linecomment x)
  then show ?case proof (induction python_prog)
    case SKIP
    then show ?case by (code_simp) 
  next
    case (block x)
     note * = this 
            have "(\<forall>ps ss. [CHR 0x22,CHR 0x22,CHR 0x22, CHR '' '', CHR 0x22] \<noteq> ps @ CHR ''#'' # ss) 
             \<and> (\<forall>ps ss. [CHR 0x22, CHR '' '', CHR 0x22, CHR 0x22, CHR 0x22] \<noteq> ps @ CHR ''#'' # ss)" 
       by(rule conjI, (rule allI, rule allI, rule set_next, (auto)[1])+)
     then show ?case using *
      by(simp  add: valid_poly_def compose_c_poly_def rmcomments_def 
                    C_def rm_start_end_comment_def sublist_def Python_def python_valid_ifdef_c_def)
  next
    case (linecomment x)
    then show ?case by (code_simp) 
  next
    case (blockcomment x1 python_prog x3a)
    then show ?case by (code_simp)
  next
    case (semi python_prog1 python_prog2)
    then show ?case 
      apply(code_simp, auto) 
      using sublist_append apply blast
      using sublist_append by blast
  qed
next
  case (blockcomment x1 c_prog x3a)
  then show ?case  proof (induction python_prog)
    case SKIP
    then show ?case by (code_simp) 
  next
    case (block x)
    note * = this 
            have "(\<forall>ps ss. [CHR 0x22,CHR 0x22,CHR 0x22, CHR '' '', CHR 0x22] \<noteq> ps @ CHR ''#'' # ss) 
             \<and> (\<forall>ps ss. [CHR 0x22, CHR '' '', CHR 0x22, CHR 0x22, CHR 0x22] \<noteq> ps @ CHR ''#'' # ss)" 
       by(rule conjI, (rule allI, rule allI, rule set_next, (auto)[1])+)
     then show ?case using *
      by(simp  add: valid_poly_def compose_c_poly_def rmcomments_def 
                    C_def rm_start_end_comment_def sublist_def Python_def python_valid_ifdef_c_def)
  next
    case (linecomment x)
    then show ?case by (code_simp)
  next
    case (blockcomment x1 python_prog x3a)
    then show ?case by (code_simp)
  next
    case (semi python_prog1 python_prog2)
    then show ?case
      apply(code_simp, simp) 
      using sublist_append by blast
  qed
next
  case (semi c_prog1 c_prog2)
  then show ?case  proof (induction python_prog)
    case SKIP
    then show ?case 
      by(code_simp, simp) 
  next
    case (block x)
    then show ?case by (code_simp, simp)
  next
    case (linecomment x)
    then show ?case by (code_simp, simp)
  next
    case (blockcomment x1 python_prog x3a)
    then show ?case by (code_simp, simp)
  next
    case (semi python_prog1 python_prog2)
    then show ?case by (code_simp, simp)   
  qed
qed


lemma valid_poly_python_SKIP: "valid_poly {Python} {(Python, SKIP)}"
  by(simp add:valid_poly_def)


lemma valid_poly_c_SKIP: "valid_poly {C} {(C, SKIP)}"
  by(simp add:valid_poly_def)

lemma valid_poly_c_python_poly_SKIP_SKIP: "valid_poly {C, Python} (c_python_poly SKIP SKIP)"
  by(code_simp)

value "hackish_non_printable_CHRs (string_of_program  (compose_c_poly SKIP SKIP))" 
value "hackish_non_printable_CHRs (string_of_program  (compose_python_poly SKIP SKIP))"

lemma valid_poly_c_python_poly: "valid_poly {C, Python} (c_python_poly hello_world_python hello_world_c)"
  apply(simp add: c_python_poly_def valid_poly_def)
  apply(safe)
     apply(code_simp)
    apply(code_simp)
   prefer 2
   apply(code_simp)
  apply(code_simp)

value \<open> hackish_non_printable_CHRs (string_of_program (compose_python_poly hello_world_python hello_world_c))\<close>
value "string_of_program (compose_python_poly hello_world_python hello_world_c)"


(*<*)
end
(*>*)
