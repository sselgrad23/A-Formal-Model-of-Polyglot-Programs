section\<open>Formalising Programs\<close>

text \<open>
  In this theory, we present an abstract representation of programs, which focuses
  on the concept required for representing polyglot programs.
\<close>
(*<*)
theory
  program
imports 
  String_Cartouche
  "HOL-Library.Sublist"
begin 
(*>*)
subsection\<open>Basic Structure for Representing Programming Languages and Programmes\<close>
text\<open>
  We start by modeling the core concepts of a programming language that are useful 
  for building polyglots: the comment and string structure.
\<close>
record block_comment =
        start ::string
        "end" ::string
        forbidden :: "string set"

record string_literals = 
        str_start ::string
        str_end ::string
        escape_sequences :: "string set"

record pl = identifier::string
            block_comment:: "block_comment list"
            nested_blockcomments :: bool
            line_comment::"string list" 
            string_literals::"string_literals list"

text\<open>
  As we are abstracting away from most parts of the concrete syntax of the programming language,
  we can represent programs mostly by their comment structure. In particular, we can model  
  program blocks as simple strings:
\<close>
datatype program = SKIP
                 | block string                      ("\<B> _")
                 | linecomment  string               ("\<langle> _ \<rangle>")  
                 | blockcomment string program string ("\<llangle> _ _ _ \<rrangle>" [60, 60] 60) 
                 | semi program program              ("_ ; _"  [59, 60        ] 59)

subsection\<open>String Representation\<close>

text\<open>
  Sometimes, e.g., during code evaluations or debugging, it is useful to turn programs into 
  a simplified string representation that can be printed directly:
\<close>

fun string_of_program where
  "string_of_program  SKIP = \<open>\<close>"
| "string_of_program (block b) = b"
| "string_of_program (blockcomment bcomment prog ecomment) = 
                                                        bcomment@(string_of_program prog)@ecomment"
| "string_of_program (linecomment comment) = comment@\<open>\<newline>\<close>"
| "string_of_program (semi p0 p1) = (string_of_program p0)@(string_of_program p1)"

definition "hackish_non_printable_CHRs = (map (\<lambda> c . if c = CHR 0x22 then CHR ''.'' else c))"

text %todo \<open>
  The function @{const "hackish_non_printable_CHRs"} is a crude hack to prettify the output, i.e., 
  avoiding that ' is printed as @{term "\<open>'\<close>"}.
\<close>

value \<open> hackish_non_printable_CHRs  \<open>tes"t\<close>\<close>

definition "hackish_print_prg = hackish_non_printable_CHRs o string_of_program"

subsection\<open>Validity of Programmes\<close>
text\<open>
  The datatype @{type "program"} for representing programs does not ensure the validity of
  a program. For example, the absence of nested block comments is not enforced by this type. 
  Hence, we need to check additional validity requirements. For this, we define the following
  recursive function:
\<close>

definition 
"rm_start_end_comment bc bcomment content ecomment = ((drop (length (start bc)) bcomment)
                                                     @(string_of_program content)
                                                     @(rev (drop (length (end bc)) (rev ecomment))))"

fun validP ("_ \<Turnstile> _") where
  "validP _  SKIP = True"
| "validP _  (block _) = True"
| "validP pl  (blockcomment bcomment content ecomment) = (\<exists> bc \<in> set(block_comment pl). 
                                                (prefix (start bc) bcomment) 
                                              \<and> (prefix (rev (end bc)) (rev ecomment))
                                              \<and> (\<not> (\<exists> f_str \<in> (forbidden bc). 
                                                    sublist (f_str) 
                                            (rm_start_end_comment bc bcomment content ecomment))))"
| "validP pl (linecomment comment) = (\<exists> c \<in> set(line_comment pl). prefix c comment)"
| "validP pl (semi p0 p1)  =  ((validP pl p0) \<and> (validP pl p1))"

subsection\<open>Program Transformations\<close>

text\<open>
  In this section, we define program transformations, i.e., functions of type 
  @{term "f::program \<Rightarrow> program"}. In particular, we define a function that 
  removes comments from a program by converting them to @{const "SKIP"} operations:
\<close>

fun comments2skip::"program \<Rightarrow> program" where
  "comments2skip  SKIP = SKIP"
| "comments2skip (block b) = block b"
| "comments2skip (blockcomment _ _ _) = SKIP"
| "comments2skip (linecomment _) = SKIP"
| "comments2skip (semi p0 p1 ) = semi (comments2skip p0) (comments2skip p1)"

      
text\<open>
  Next, we define a function that removes unnecessary @{const "SKIP"} operations:
\<close>

fun rmskip::"program \<Rightarrow> program" where 
   "rmskip (semi p0 p1 )   = (let lh = rmskip p0 in 
                              (let rh = rmskip p1 in 
                                  (if lh = SKIP 
                                  then rh 
                                  else (if rh = SKIP 
                                       then lh 
                                       else semi lh rh))))"
 | "rmskip s                = s"

definition rmcomments::"program \<Rightarrow> program" where
  "rmcomments = rmskip o comments2skip"

value "rmskip (block \<open>\<close>)"
value "rmskip (SKIP;SKIP;block \<open>\<close>;SKIP;SKIP;SKIP;SKIP;block \<open>\<close>;SKIP;SKIP)"
value "rmskip (block \<open>\<close>;SKIP;SKIP;block \<open>\<close>;SKIP;SKIP;SKIP;SKIP;block \<open>\<close>;SKIP;SKIP)"
value "rmskip (block \<open>\<close>;SKIP;SKIP;block \<open>\<close>;SKIP;SKIP;(SKIP;SKIP;block \<open>\<close>;block \<open>\<close>;SKIP);SKIP)"
value "rmskip (SKIP)"
value "rmskip (SKIP;SKIP)"
value "rmskip (SKIP;SKIP;SKIP)"
value "rmskip (SKIP;SKIP;(SKIP;SKIP))"

subsubsection\<open>Important Properties of @{const "comments2skip"}, @{const "rmskip"}, and @{const "rmcomments"}\<close>

lemma comments2skip_2x: "comments2skip (comments2skip P) = comments2skip P"
proof (induction "P")
case SKIP
then show ?case by(simp)
next
case (block x)
  then show ?case by(simp)
next
  case (linecomment x)
  then show ?case by(simp)
next
case (blockcomment x1 P x3a)
  then show ?case by(simp)
next
  case (semi P1 P2)
  then show ?case by(simp)
qed

lemma  comments2skip_valid_P: "PL \<Turnstile> P \<Longrightarrow> PL \<Turnstile> (comments2skip P)"
proof (induction "P")
case SKIP
then show ?case by simp
next
  case (block x)
  then show ?case by simp
next
case (linecomment x)
then show ?case by simp
next
  case (blockcomment x1 P x3a)
  then show ?case by simp
next
  case (semi P1 P2)
  then show ?case 
    by(simp add:if_split Let_def) 
qed

lemma rmskip_skip_p1_p2: "rmskip (SKIP; P1 ; P2) = rmskip (P1 ; P2)"
  by(code_simp)

lemma rmskip_p1_p2_skip: "rmskip (P1 ; P2; SKIP) = rmskip (P1 ; P2)" 
  by(code_simp, simp)
  
lemma rmskip_skip_p: "rmskip (SKIP ; P) = rmskip (P)"
  by simp
  
lemma rmskip_p_skip: "rmskip (P; SKIP) = rmskip (P)"
proof (induct "P")
  case SKIP
  then show ?case by simp
next
  case (block x)
  then show ?case by simp
next
  case (linecomment x)
  then show ?case by simp
next
  case (blockcomment x1 P x3a)
  then show ?case by simp
next
  case (semi P1 P2)
  then show ?case
    using rmskip.simps(1) rmskip.simps(2) by presburger
qed

lemma rmskip_2x: "(rmskip (rmskip P) = (rmskip P))"
proof (induct P)
case SKIP
then show ?case by simp
next
case (block x)
  then show ?case by simp
next
  case (linecomment x)
  then show ?case by simp
next
  case (blockcomment x1 P x3a)
  then show ?case by simp
next
  case (semi P1 P2)
  then show ?case by(code_simp,simp)
qed

lemma rmcomments_2x: "rmcomments (rmcomments P) = rmcomments P"
proof (induction "P")
case SKIP
then show ?case by(code_simp) 
next
  case (block x)
  then show ?case by(code_simp)
next
case (linecomment x)
then show ?case by(code_simp)
next
  case (blockcomment x1 P x3a)
  then show ?case by(code_simp)
next
case (semi P1 P2)
  then show ?case
  proof -
    have f1: "\<forall>p pa. if rmskip p = SKIP then rmskip (p ; pa) = 
              rmskip pa else if rmskip pa = SKIP then rmskip (p ; pa) = 
              rmskip p else rmskip (p ; pa) = rmskip p ; rmskip pa"
      using rmskip.simps(1) by presburger
    have f2: "rmskip (comments2skip P1 ; comments2skip P2) = 
              rmskip (comments2skip P2) \<longrightarrow> rmcomments (rmcomments (P1 ; P2)) = 
              rmcomments (P1 ; P2)"
      by (metis (no_types) comments2skip.simps(5) comp_apply rmcomments_def semi.IH(2))
    have f3: "rmskip (comments2skip (rmcomments P2)) = rmcomments P2"
      by (metis comp_apply rmcomments_def semi.IH(2))
    have "rmskip (comments2skip (rmcomments P1)) = rmcomments P1"
      by (metis comp_apply rmcomments_def semi.IH(1))
    then have "(if rmskip (comments2skip P2) = 
               SKIP then rmskip (comments2skip P1 ; comments2skip P2) = 
               rmskip (comments2skip P1) else rmskip (comments2skip P1 ; comments2skip P2) = 
               rmskip (comments2skip P1) ; rmskip (comments2skip P2)) \<longrightarrow> 
               rmcomments (rmcomments (P1 ; P2)) = 
               rmcomments (P1 ; P2) \<or> rmskip (comments2skip P1 ; comments2skip P2) = 
               rmskip (comments2skip P2)"
      using f3 by (simp add: rmcomments_def)
    then show ?thesis
      using f2 f1 by meson
  qed 
qed

lemma rmskip_valid_P: "PL \<Turnstile> P \<Longrightarrow> PL \<Turnstile> (rmskip P)"
proof (induction "P")
case SKIP
then show ?case by simp
next
  case (block x)
  then show ?case by simp
next
case (linecomment x)
then show ?case by simp
next
  case (blockcomment x1 P x3a)
  then show ?case by simp
next
  case (semi P1 P2)
  then show ?case 
    by(simp add:if_split Let_def) 
qed

lemma rmcomments_valid_P: "PL \<Turnstile> P \<Longrightarrow> PL \<Turnstile> (rmcomments P)"
proof (unfold rmcomments_def, induction "P")
case SKIP
then show ?case by simp
next
  case (block x)
  then show ?case by simp
next
case (linecomment x)
then show ?case by simp
next
  case (blockcomment x1 P x3a)
  then show ?case by simp
next
  case (semi P1 P2)
  then show ?case 
    by(simp add:if_split Let_def) 
qed

lemma rmskip_comments2skip_valid_P: "PL \<Turnstile> P \<Longrightarrow> PL \<Turnstile> (rmskip (comments2skip P))"
  using  comments2skip_valid_P rmskip_valid_P by auto

subsection\<open>Examples\<close>
text\<open>
  In this section, we define a few programming languages as examples for our case study as
  well as a few tiny programs to demonstrate our program formalisation. We will use these
  example programs later to build polyglots. 
\<close>
subsubsection\<open>Programming Languages\<close>

definition \<open>C = \<lparr>
         identifier = \<open>C\<close>,
         block_comment= [ 
           \<lparr> start =  \<open>/*\<close>, end=  \<open>*/\<close>, forbidden={} \<rparr>,
           \<lparr> start =  \<open>#if 0\<newline>\<close>, end=  \<open>#endif\<newline>\<close>, forbidden={\<open>#\<close>} \<rparr>
         ], 
         nested_blockcomments = True,
         line_comment = [(\<open>//\<close>)],
         string_literals=[\<lparr> str_start =  \<open>"\<close>, str_end=  \<open>"\<close>, escape_sequences={\<open>\\<close>} \<rparr>]
       \<rparr>\<close>

definition \<open>Python = \<lparr> 
         identifier = \<open>Python\<close>,
         block_comment= [ \<lparr> start =  \<open>""" "\<close>, end=  \<open>" """\<close>, forbidden={\<open>""""\<close>}\<rparr> ], 
         nested_blockcomments = True,
         line_comment = [( \<open>#\<close>)],  
         string_literals=[
            \<lparr> str_start =  \<open>"\<close>, str_end=  \<open>"\<close>, escape_sequences={\<open>\\<close>} \<rparr>,
            \<lparr> str_start =  \<open>'\<close>, str_end=  \<open>'\<close>, escape_sequences={\<open>\\<close>} \<rparr>,
            \<lparr> str_start = \<open>r"\<close>, str_end=  \<open>"\<close>, escape_sequences={} \<rparr>,
            \<lparr> str_start = \<open>r'\<close>, str_end=  \<open>'\<close>, escape_sequences={} \<rparr>
         ]
       \<rparr>\<close>

definition \<open>HTML = \<lparr> 
         identifier = \<open>HTML\<close>,
         block_comment= [ \<lparr> start =  \<open><!--\<close>, end= \<open>-->\<close>, forbidden={}\<rparr> ], 
         nested_blockcomments = False,
         line_comment = [],
         string_literals=[
            \<lparr> str_start =  \<open>"\<close>, str_end=  \<open>"\<close>, escape_sequences={\<open>\\<close>} \<rparr>,
            \<lparr> str_start =  \<open>'\<close>, str_end=  \<open>'\<close>, escape_sequences={\<open>\\<close>} \<rparr>
         ]
       \<rparr>\<close>

definition \<open>Pascal = \<lparr> 
         identifier = \<open>Pascal\<close>,
         block_comment= [ \<lparr> start = \<open>(*\<close>, end= \<open>*)\<close>, forbidden={}\<rparr> ], 
         nested_blockcomments = True,
         line_comment = [],
         string_literals=[\<lparr> str_start =  \<open>"\<close>, str_end=  \<open>"\<close>, escape_sequences={\<open>\\<close>} \<rparr>]
       \<rparr>\<close>

definition \<open>Z3 = \<lparr>
         identifier = \<open>Z3\<close>,
         block_comment= [],
         nested_blockcomments = False,
         line_comment = [\<open>;\<close>],
         string_literals=[\<lparr> str_start =  \<open>"\<close>, str_end=  \<open>"\<close>, escape_sequences={\<open>\\<close>} \<rparr>]
      
       \<rparr>\<close>

definition \<open>SQL = \<lparr>
         identifier = \<open>SQL\<close>,
         block_comment= [\<lparr> start =  \<open>/*\<close>, end=  \<open>*/\<close>, forbidden={} \<rparr>],
         nested_blockcomments = False,
         line_comment = [\<open>--\<close>],
         string_literals=[\<lparr> str_start =  \<open>"\<close>, str_end=  \<open>"\<close>, escape_sequences={\<open>\\<close>} \<rparr>]
       \<rparr>\<close>

subsubsection\<open>A Small Collection of Hello World Programmes\<close>                   

definition hello_world_python where
  \<open>hello_world_python = (\<langle> \<open># Hello World in Python\<close> \<rangle> ; 
                         \<B>  \<open>print("Hello in Python")\<newline>\<close> )\<close>

definition hello_world_c where
  \<open>hello_world_c = (\<langle> \<open>// Hello World in C\<close>\<rangle> ; 
                    \<B> \<open>#include<stdio.h>\<newline>
                        void main () {\<newline>
                          printf("Hello in C");\<newline>  
                        }\<newline>\<close>)\<close>

value "hackish_print_prg hello_world_python"
value "Python \<Turnstile> hello_world_python"
value "C \<Turnstile> hello_world_python"
value "C \<Turnstile> hello_world_c"
value "Python \<Turnstile> hello_world_c"

lemma example_valid_python: "Python \<Turnstile> hello_world_python"
  by code_simp

lemma example_not_valid_python: "\<not> (C \<Turnstile> hello_world_python)"
  by code_simp

lemma example_valid_c: "C \<Turnstile> hello_world_c"
  by code_simp

lemma example_not_valid_c: "\<not> (Python \<Turnstile> hello_world_c)"
  by code_simp

value "comments2skip hello_world_c"
value "rmcomments hello_world_c"

(*<*)
end
(*>*)
