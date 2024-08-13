(* *)

section \<open> Knowing jEdit's interface \<close>

theory Knowing_jEdit_Interface
  imports Complex_Main

begin


subsection \<open> Top tool bar \<close>

text \<open> Hover over the buttons in the toolbar, each one of them states its purpose. \<close>

text \<open> A couple of useful buttons in the toolbar for Isabelle users are the arrows on the 
extreme right. Test this yourself, place the writing cursor (click) on top of the first 
expression below, then place it in the second expression. Use the arrows in the toolbar 
to move back and forth between these expressions. \<close>

term "23 - (3::real)"

term "(1 + 1005) / 2 - (3::real)"

text \<open> Test the usefulness of the arrows even more: make a new file using the toolbar button 
and come back to this file using the arrows. \<close>

text \<open> Below the toolbar, there is a drop-down menu with names of files. Use it to go back 
to your recently created untitled file, and use a button in the toolbar to close the file. \<close>


subsection \<open> Left, bottom and right panels \<close>

text \<open> There are some buttons on the margins of your Isabelle's jEdit interface:
\begin{itemize}
\item Documentation
\item File Browser
\item Output
\item Query
\item Sledgehammer
\item Symbols
\item Search
\item Sidekick
\item State
\item Theories
\end{itemize} 
Let us go through them quickly. \<close>

subsubsection \<open> Documentation \<close>

text \<open> Click the Documentation button and you will see various directories and their files. \<close>

text \<open> The directory ``Examples'' has some Isabelle files (extension .thy for ``theory''). 
You might want to take a look (click) at a definition of Finite sequences in the theory 
Seq.thy or to a proof of the drinker's paradox in Drinker.thy. \<close>

text \<open> A useful file in ``Release Notes'' for experienced users is the ``NEWS'' file. 
It describes the changes to the current and previous Isabelle releases. \<close>

text \<open> Click any of the files in the directories ``Isabelle Tutorials'' or ``Isabelle 
Reference Manuals''. Isabelle should open a .pdf with information about some Isabelle 
features. \<close>


subsubsection \<open> File Browser \<close>

text \<open> As the name suggest, the file browser lets you navigate your directories. 
It works as your operating system's standard visual interface for file management. 
Thus, we will focus on the lower panel that has some Isabelle specific buttons 
like Output, Query, and Symbols.\<close>


subsubsection \<open> Output \<close>

text \<open> Click the ``Output'' button, then click on any of the two mathematical expressions below. \<close>

term "{23 - 3, (1 + 1005) / 2 - (3::real)}"

value "{23 - 3, (1 + 1005) / 2 - (3::real)}"

\<comment> \<open> What is the difference between @{command term} and @{command value}?\<close>
(* you can write your answer inside this comment *)

text \<open> Output is the way Isabelle communicates with you: \<close>

\<comment> \<open> Use Documentation to open the Drinker.thy example. \<close>

\<comment> \<open> Pro-tip: Hold the Ctrl (Windows) or Cmnd (Mac) key and the number 2 (Ctrl+2) to 
split jEdit's window horizontally and see multiple files at once. Go back to seeing one
single file with Ctrl+1. The key-combo Ctrl+3 splits the window vertically. \<close>

\<comment> \<open> At the end of the Drinker.thy file, place the writing cursor (click) between 
 @{term "\<forall>x. drunk x"} and @{text "by"}. \<close>

\<comment> \<open> In Output (in the lower panel), tick and untick the ``Proof state'' box while the 
cursor is in that place. Observe what Isabelle says. \<close>

\<comment> \<open> Now, move the cursor left and right, from the blank space to the ``b'' in @{text "by"}.
 Observe how Isabelle's output changes. \<close>


subsubsection \<open> Query \<close>

text \<open> Click the ``Query'' button. The lower panel now allows you to search for theorems 
and constants in the Isabelle libraries. \<close>

\<comment> \<open> In the search bar shown by Query, search the expression @{term "x + y = y + x"}\<close>
(* only search for "x + y = y + x" including quotations *)

\<comment> \<open> How many theorems does Isabelle find?\<close>
(* you can write your answer here *)

\<comment> \<open> Replace each letter x and y with an underscore in your search. How many theorems 
does Isabelle find?\<close>
(* you can write your answer here *)

text \<open> The result of your search is a bulleted list of names of theorems followed 
by their content. \<close>

\<comment> \<open> Copy the name of a theorem and paste it next to @{command thm}. 
It might not be necessary to copy the whole name. \<close>

thm add.assoc mult.commute

\<comment> \<open> Use Output and the writing cursor to understand the purpose of @{command thm} above. \<close>
(* you can write your explanation here *)


\<comment> \<open>Use the search ``name: pi'' (without quotations) to find a theorem about @{term \<pi>} 
and paste its name next to @{command thm} below. Is the first result about @{term \<pi>}?: \<close>
(* you can write your answer here *)

thm mult.commute

\<comment> \<open>You might want to refine your search using ``@{text "name: pi_"}'' instead. \<close>

text \<open> Pro-tip: alternatively to the Query panel, you can use @{command find_theorems} 
and @{command find_consts}. Use Output to see what they do below. \<close>

find_theorems "_ + _ = _ + _"

find_theorems name: pi_

find_consts real name: pi

find_consts "real \<Rightarrow> real \<Rightarrow> real"


subsubsection \<open> Symbols \<close>

\<comment> \<open> Use @{command term} and the lower panel to write a Greek letter after @{command term} below. \<close>

term replace_this_with_a_Greek_letter

text \<open>WARNING: To write spaces in a @{command term} you need to use quotation marks around
the whole expression. Notice that, withouth these quotes, Isabelle throws an error. \<close>
(* For example: term "\<alpha> \<beta>" *)

term replace_this_with_two_Greek_letters_separated_with_a_space

text \<open>WARNING: Not all symbols in the panel are treated equally. For instance, Greek letters 
can be variables, but the symbols in the ``Unsorted'' tab cannot. Notice the error message
in the @{command term} below. \<close>

term replace_this_with_an_Unsorted_symbol

text \<open>We can use slashes (\textbackslash) as in \LaTeX.\<close>
\<comment> \<open>Write below @{term "\<xi> \<inter> \<Xi>"} by typing a backslash and the words xi, inter, and Xi respectively.\<close>
(* i.e. "\xi \inter \Xi" (with quotation marks) *)

term replace_this_with_your_typing

text \<open>Pro-tip: To increase the autocompletion speed, make smaller the ``completion delay'' in
Preferences > Plugin Options > Isabelle > General > Completion Delay.\<close>

\<comment> \<open>Practice a little bit more, write below a logical expression with at least
two logical operators. An example is provided. \<close>

term "\<forall>x. P x \<longrightarrow> (\<exists>y. Q x y)"


subsubsection \<open> Search \<close>

text \<open> Do an automatic search on this file for the word ``name''. That is:
 Top menu > Search > Find... 
 OR 
 Ctrl + F.

 A new window appears. Tick the HyperSearch box in Settings of this new window.
Type ``name'' and then click ``Find'' or hit Enter.\<close>

\<comment> \<open> The right panel will open. Navigate to somewhere in this file where ``name'' occurs 
by clicking the item found on the right panel and come back to this point. \<close> 


subsubsection \<open> Sidekick \<close>

\<comment> \<open>Just as you did for Search, use the Sidekick panel to navigate to the subsubsection on 
File Browsing in this file, then come back to this point.\<close>


subsubsection \<open> State \<close>

text \<open> Open the State panel and place the red cursor in the blank space between the right 
parenthesis ``)'' and the mathematical expression. Compare what you see there with what 
Isabelle displays in Output. \<close>

lemma (in comm_semiring) "x + y = y + x" 
  using add.commute by blast

\<comment> \<open> Untick the ``Proof state'' box in the Output Panel and observe the changes. \<close>

\<comment> \<open> Choose a configuration that works best for you. \<close>


subsubsection \<open> Theories (and navigation) \<close>

\<comment> \<open>Open the Theories Panel, then open four .thy files from the Documentation Panel while paying
attention to the information displayed in the Theories Panel. Then, come back to this point. \<close>

\<comment> \<open> Double-click any of the rectangles on the right. Then come back to this point.\<close>

\<comment> \<open> Now navigate to one of the .thy files but this time using the drop-down navigation menu 
below the tool bar. Learn the name of the .thy file. Then, close the theory (X in the tool bar).\<close>

text \<open> Did the .thy file disappear from the drop-down menu?\<close>
(* you can write your anwer here *)

text \<open> Did the theory disappear from the Theories Panel?\<close>
(* you can write your anwer here *)


text \<open> You can see the definition of various concepts in Isabelle by Ctrl+clicking 
Isabelle's constructs. For instance, Ctrl+click any of the black things below 
(then, come back to this point): \<close>

term "\<forall>x. P x \<longrightarrow> Q (0::nat)"

\<comment> \<open> Using what you have learned in this file, navigate to the theory that contains the theorem
``add.commute''. Then, paste the contents of the theorem below. 
Isabelle's output should not display any errors: \<close>

\<comment> \<open> Using what you have learned in this file, navigate to the definition of the symbol ``+''. Paste
the name of a theorem you find about ``+'' from the corresponding theory file. 
Isabelle's output should not display any errors:\<close>


end