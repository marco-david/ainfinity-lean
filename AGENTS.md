# Project Context
You are an expert mathematician and Lean 4 developer working on the formalization of $A_\infty$-categories. The ultimate goal of this repository is to contribute this formalization to the `Mathlib` library. All code must be production-ready and adhere to strict community standards.

# Mathematical Foundation
* **Domain:** The core focus is strictly on $A_\infty$-categories, focusing on the sequence of higher composition operations ($m_n$) and the associated Stasheff identities.
* **Implementation Strategy:** Follow the established architectural choices in the repository for representing these infinite sequences of operations and their algebraic relations. Do not introduce alternative foundational models unless explicitly instructed.

# Mathlib4 Coding Conventions
* **Completeness:** The code must be accepted by the Lean kernel. Strictly avoid using `sorry` or `admit` unless instructed to draft a proof skeleton.
* **Naming Standards:** * `camelCase` for definitions, variables, and types.
    * `snake_case` for theorems, lemmas, and proofs.
* **Tactic Discipline:** Prioritize robust, maintainable tactic proofs. Avoid overly broad `simp` calls; default to `simp only [specific_lemmas]` to prevent proofs from breaking during Mathlib updates.
* **Documentation:** Every major definition and theorem MUST include a standard `/-- ... -/` docstring explaining the underlying mathematical intuition before the code block.

# Codex Execution & Exploration Constraints
* **Search First:** Before writing a new helper lemma or definition, use your search tools (`rg`) to aggressively scan the workspace and existing Mathlib imports. Extract and reuse shared helpers instead of duplicating existing infrastructure.
* **Batch Reading:** You must batch-read all relevant files (`multi_tool_use.parallel`), prerequisite lemmas, and type definitions before attempting to write a new proof. Do not guess a theorem's signature; verify the exact types involved first.
* **Type Safety:** Ensure all edits maintain strict type safety. Do not proceed with subsequent logical steps if the tactic state produces an error.

# Mathlib4 Coding Conventions
Some of these guidelines may feel overly strict, but I promise that they will make our lives much, much easier in the medium and long run. Normal software engineering projects become unmaintainable very quickly if programmers don't follow proper guidelines, and the problem is even more extreme in Lean. I have modeled these rules based on my experience with the Mathlib review process, but these are just generally good things to do.
Enable and use the module system - The new module system allows us to speed up compilation and perform basic encapsulation. It is also used by Mathlib, so using it now makes it easier to PR stuff to Mathlib. We need to enable something in the lakefile and then add the word module to the top of every file we make. This provides many benefits, but we need to note that:
Since Lean now distinguishes between public and private imports, we need to public import everything we plan on using in theorem statements. For example, we can do public import Mathlib instead of import Mathlib.
Definitions and theorems are now private by default. We can either individually mark them public, or add public section to the top of the files. Note that all definitions involved in the statement of a public theorem need to have been public imported.
You can no longer unfold a definition in a different file from where it was defined, unless you mark the definition with @[expose].
Make sure the top level file imports all files - Mathlib has a file, Mathlib.lean, which imports every file in mathlib. This is the file that gets run when we run lake build and we need to make sure that it actually builds everything in our repository. There is a lake command that should do this automatically for you; we just need to run it every time we make a new file.
Coding standards
These are hard rules which we should follow as strictly as possible.
In general, we want to follow the mathlib coding conventions, some of which I will repeat here:
General style: https://leanprover-community.github.io/contribute/style.html
No warnings - Code should not produce any warnings or errors (with the exception of "definition uses sorry"). These can be disabled if they cause problems, but please do not ignore them. (Like other conventions in this section, it is fine to disobey this rule temporarily, but "finished" proofs should not produce warnings.)
Naming conventions - Follow the Mathlib naming conventions, https://leanprover-community.github.io/contribute/naming.html#mathlib-naming-conventions, Names are challenging to change later, so let's make sure we really get these right. Mathlib uses a hybrid naming scheme that mixes lowerCamelCase, UpperCamelCase, and snake_case.
File names and folders should be written in UpperCamelCase. For example, Mathlib/Computability/ContextFreeGrammar.lean or Mathlib/Computability/DFA.lean. For example, we should call our folder AInfinity rather than Ainfinity.
When defining a type, type family, proposition, or typeclass, use UpperCamelCase. For example, Nat, Real, String, List, LinearMap, Subsingleton, Nat.Prime, Continuous, IsCompact, etc. This only applies to when you define propositions, not when you prove them.
For any other definition, use lowerCamelCase. For example, Nat.add, LinearMap.adjoint, RingHom.ker, sInf etc.
For proofs of propositions, use a hybrid of lowerCamelCase and snake_case. For example, the theorem isClopen_compl_iff states that IsClopen sᶜ ↔ IsClopen s. They downgraded the case of IsClopen to isClopen and then used underscores to combine the relevant components.
Line length - Keep each line to 100 characters or less.
Tactics that produce multiple goals - If a tactic (such as refine or by_cases) produces multiple goals, indent each subgoal with a · (type this with \.).
Use spaces between infix operators - Write 3 + 4, not 3+4, and write (h : x < y), not (h:x < y). Also use a space before and after :=.
Indentation levels - Do not indent when using the section or namespace keyword. This is to match Mathlib standards.
When to make parameters implicit - Generally speaking, you want to make a parameter implicit if Lean can figure out what it is from the later parameters. For example, there are theorems like
theorem mul_div_cancel (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by ...
In this theorem, Lean can figure out what n is from the type of H, so n becomes an implicit parameter. Lean cannot figure out what m is because it doesn't appear in any further hypotheses, so it is an explicit parameter. This convention might have more exceptions than the others in this section.
Only squeeze non-terminal simps - Simp squeezing is when you write simp? which tells you how to replace a simp call with a simp only call. We should do this to all non-terminal simps, but don't do this to any terminal simp.
No new axioms: Do not define new axioms and only use the standard three axioms: Classical.choice, propext, and Quot.sound. Do not use native_decide or bv_decide .
Heuristics
Requirements that you should follow as often as possible, but which you ultimately have to use your best judgement for.
Names should be meaningful - Names are important, including lemma names. Try to minimize the number of lemmas we have with arbitrary names, like part_1 or existence_theorem. We also want to avoid putting very generic names in the root namespace, like sum or size.
Definitions should be as general as possible - Mathlib tries to make definitions as general as possible. For example, they work with semilinear maps between semimodules rather than linear maps between vector spaces. They work with preorders instead of partial orders whenever possible, and operations on metric spaces are defined for extended metric spaces whenever possible. Unlike Mathlib, we don't have time to jump through hoops to be as general as possible, but we should take advantage of "free" generalizations whenever we get the chance. For example, we should use Type* instead of Type whenever we can, and if definitions work with rings instead of just commutative rings, we should define them for rings.
Note that theorems are allowed to be significantly less general than definitions. For example, we can create a definition for all rings, but have a major theorem about them which only holds for commutative rings.
Definitions should be as incremental as possible - Complex definitions should be broken up into very gradual steps. An algorithm in Lean should be split up into a bunch of smaller functions. In general, if a definition takes up more than a few lines of Lean code, it is probably a bad idea. This is a complicated heuristic, so I'll try to point out violations of this when they appear in our code.
Be economical with definitions - Automation like simp cannot see through definitions (except for abbreviations), so the more definitions we add the harder it gets for automation to navigate our code. Don't define a definition if it is only going to appear in a few theorems (you can make an abbreviation instead if desired). Also try not to create a new definition which is just a special case of another definition. For example, Mathlib doesn't have a definition for the Riemann integral because it is a special case of the Bochner integral (they might add a definition for a function being Riemann integrable, but they won't add a new integral definition).
The most important reason why new definitions are problematic for automation has to do with simp-normal forms. Suppose for instance Mathlib defined a new constant Real.tau = 2 * Real.pi. Now, all theorem statements for Real.pi have to be duplicated for Real.tau. If this were not the case, then using Real.tau would be painful. Additionally, we would like simp to move expressions involving real numbers closer to a canonical form, and having two ways to express the same thing will lead to headaches.
A general rule of thumb is that you should try to have at least 20 lemmas for each new type you define, and 5 lemmas for each new non-type definition. I came up with these numbers on the fly, but this is just a general idea.
It's especially important that we don't define new definitions just for the purpose of saving ourselves some typing. For instance, it might be tempting to define a type like
abbrev Vec (n : ℕ) := Fin n → ℝ

or
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)
but please don't do this.
Don't repeat yourself (DRY) for theorems - In software engineering, the principle of don't repeat yourself (DRY) states that if you find similar code in two functions, you should factor out that common code into two separate functions. For the reasons stated above, this principle only sometimes applies to Lean definitions: even if two definitions contain commonalities, we should only factor out the common part if we believe we can write lemmas about that common part.
But for theorems, the principle of DRY applies: if two proofs contain similar content, they should be factored out into a separate theorem.
Avoid forward reasoning in proofs (factor it into new lemmas instead) - Mathlib proofs tend to contain mostly backward reasoning (e.g. apply, induction, cases, congr), symmetric reasoning (e.g. rw, grw, symm), and goal-closing automation (e.g. simp, aesop, grind). They tend not to use long chains of forward reasoning with have very much. There's nothing wrong with forward reasoning, but if you find yourself using forward reasoning like have a lot, you might want to consider splitting those parts of the proof into new lemmas, so that your lemma consists mostly of backward reasoning.
A rule of thumb is to try to avoid have statements which are over 3 lines long. We especially want to minimize our use of have statements with ∀ quantifiers, as these should almost always be split into their own lemma. We also want to avoid proofs that go past 3 or so levels of indentation. "Flat proofs" tend to be better than "tree proofs".
Another rule of thumb is that a single line of natural language proof should correspond to one or more lemmas, rather than one have statement in the Lean proof.
Proofs should be short and easily replaceable - This might sound strange, but the least valuable part of a Lean file should be its proofs. The most valuable parts are the definitions and theorem statements. Files which contain a single long proof should be avoided. Of course, a single proof can take many hours to make, but part of that time should go towards finding lemmas to factor out.
Proofs should be kept short enough to the point where they could be rewritten from scratch relatively easily. As a heuristic, at least half of all proofs should be at most 5 lines long, and very few proofs should exceed 30 lines (at least for algebra, analysis proofs tend to be a little bit longer on average, but are still almost always <100 lines). I believe that at least a fifth of all proofs in mathlib are just a single line long.
The reasons for this are
Proof fragility: If definitions are moved around in mathlib or our code, it will break our proofs, and the shorter a proof is the easier it is to localize the problem with the proof. In a worst-case scenario, the proof may need to be rewritten from scratch.
Repository of lemmas: Most definitions should be accompanied by a bunch of lemmas. If a proof involves proving a fact about a definition, probably other proofs will need that definition soon anyways, so it might as well become a separate lemma.
Easier collaboration: Collaborating on a single proof is hard. Collaborating on a bunch of smaller lemmas is much easier.
Fix downstream files when refactoring - If renaming or moving definitions around, try to fix all the content in downstream files, or at the very least replace proofs with sorry instead of causing them to fail to compile.
