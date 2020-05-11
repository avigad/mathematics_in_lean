.. _the_natural_numbers:

The Natural Numbers
===================

Mathematically speaking, the natural numbers are characterized up to isomorphism as
a set with a zero element and an injective successor function
such that zero is not a successor and the entire structure
satisfies the *induction principle*:
any property that holds of zero and is maintained
by successors holds of every natural number.
To introduce the natural numbers formally,
Lean's core library makes use of Lean's foundational framework,
which allows us to declare a new type as follows:

.. code-block:: lean

    namespace my_nat

    -- BEGIN
    inductive nat : Type
    | zero : nat
    | succ : nat → nat
    -- END

    end my_nat

This declares a type ``nat`` with constants
``nat.zero : nat`` and ``nat.succ : nat → nat``,
and provides the associated principles of induction and recursion.

In this chapter, we will explain how the Lean library
establishes the familiar properties of arithmetic on this foundation,
and then we will show you how to use the natural numbers
to prove some interesting theorems.


Defining Arithmetic
-------------------

The principle of recursive definition means that,
once we introduce notation ``ℕ`` for ``nat`` and ``0`` for ``nat.zero``,
and once we open the ``nat`` namespace so that we can write ``succ``
instead of ``nat.succ``,
we can define addition recursively as follows:

.. code-block:: lean

    open nat

    namespace my_nat

    -- BEGIN
    def add : ℕ → ℕ → ℕ
    | m 0 := m
    | m (succ n) := succ (add m n)
    -- END

    end my_nat

Assuming we introduce the usual notation for addition,
the definition means that we can use the associated
defining equations:

.. code-block:: lean

    open nat

    variables m n : ℕ

    -- BEGIN
    #check (add_zero m   : m + 0 = m)
    #check (add_succ m n : m + (succ n) = succ (m + n))
    -- END

But the computational nature of Lean's foundation gives us more,
namely, that Lean will carry out these reductions
internally in order to make expressions match.
As a result, the equations hold by the reflexivity axiom:

.. code-block:: lean

    open nat

    variables m n : ℕ

    -- BEGIN
    example : m + 0 = m := rfl
    example : m + (succ n) = succ (m + n) := rfl
    -- END

Here, ``rfl`` is a proof term that corresponds to the ``refl`` tactic.
Numerals are also defined in a clever way in Lean so that,
for example, ``1`` reduces to ``succ 0``.
This means in many contexts we can use ``n + 1`` and ``succ n``
interchangeably:

.. code-block:: lean

    open nat

    variable n : ℕ

    -- BEGIN
    example : succ n = n + 1 := rfl
    -- END

Suppose we want to prove the commutativity of addition, ``m + n = n + m``.
We don't have much to work with: we have the defining equations for
addition, but no other facts about it.
But we do have the principle of induction,
which we can invoke with the ``induction`` tactic:

.. code-block:: lean

    variables m n : ℕ

    namespace my_nat

    -- BEGIN
    theorem add_comm : m + n = n + m :=
    begin
      induction n,
      { sorry },
      sorry
    end
    -- END

    end my_nat

In this section, we will continue the strategy of
stating theorems with the same names that are used in the library
but hiding them in a namespace to avoid a naming conflict.
If you move your cursor through the proof,
you will see that the induction tactic leaves two goals:
in the base case, we need to prove ``m + 0 = 0 + m``,
and in the induction step,
we need to prove ``m + succ n = succ n + m``
using the inductive hypothesis ``m + n = n + m``.
You will also see that Lean chose names automatically
for the inductive hypothesis and the variable in the induction step.
We can tell Lean to use ``n`` for the variable name and ``ih``
for the name of the inductive hypothesis by appending ``with n ih``
to the induction command.

How can we prove the base case?
It turns out that this requires another instance of induction.
We could call the induction tactic again in that subproof,
but since the fact that we need, ``0 + m = m``,
is independently useful, we may as well make it a separate theorem.
Similarly, in the inductive hypothesis, we need ``succ m + n = succ (m + n)``,
so we break that out as a separate theorem as well.

.. code-block:: lean

    open nat

    variables m n : ℕ

    namespace my_nat

    -- BEGIN
    theorem zero_add : 0 + m = m :=
    begin
      induction m with m ih,
      { refl },
      rw [add_succ, ih]
    end

    theorem succ_add : succ m + n = succ (m + n) :=
    begin
      induction n with n ih,
      { refl },
      rw [add_succ, ih]
    end

    theorem add_comm : m + n = n + m :=
    begin
      induction n with n ih,
      { rw zero_add, refl },
      rw [succ_add, ←ih]
    end
    -- END

    end my_nat

We can similarly make quick work of associativity:

.. code-block:: lean

    open nat

    variables m n k : ℕ

    namespace my_nat

    -- BEGIN
    theorem add_assoc : m + n + k = m + (n + k) :=
    begin
      induction k with k ih,
      { refl },
      rw [add_succ, ih],
      refl
    end
    -- END

    end my_nat

Because addition is defined by recursion on the second argument,
doing induction on ``k`` will allow us to use the defining equations
for addition in the base case and induction step.
This is a good heuristic when it comes to deciding which variable to use.
We can do on to define multiplication in the expected way:

.. code-block:: lean

    namespace my_nat

    -- BEGIN
    def mul : ℕ → ℕ → ℕ
    | m 0     := 0
    | m (n+1) := mul m n + m
    -- END

    end my_nat

This gives us the defining equations for multiplication:

.. code-block:: lean

    open nat

    variables m n : ℕ

    -- BEGIN
    #check (mul_zero m   : m * 0 = 0)
    #check (mul_succ m n : m * (succ n) = m * n + m)

    example : m * 0 = 0 := rfl
    example : m * (n + 1) = m * n + m := rfl
    -- END

We now challenge you to use nothing more than these defining equations
and the properties of addition we have already established
to prove all of the following:

.. code-block:: lean

    open nat

    variables m n k : ℕ

    namespace my_nat

    -- BEGIN
    theorem mul_add : m * (n + k) = m * n + m * k := sorry

    theorem zero_mul : 0 * n = 0 := sorry

    theorem one_mul : 1 * n = n := sorry

    theorem mul_assoc : m * n * k = m * (n * k) := sorry

    theorem mul_comm : m * n= n * m := sorry
    -- END

    end my_nat

The library also defines a function for exponentiation, ``nat.pow``.

.. code-block:: lean

    open nat

    namespace my_nat

    -- BEGIN
    def pow (b : ℕ) : ℕ → ℕ
    | 0        := 1
    | (succ n) := pow n * b
    -- END

    end my_nat

Note that because the argument ``b`` in this definition is presented
before the colon,
it is taken to be fixed in the recursive definition,
and so the recursive call refers to ``pow n`` instead of ``pow b n``.
We challenge you to state and prove some basic theorems about ``nat.pow``
from the associated defining equations, ``nat.pow_zero`` and ``nat.pow_succ``.
Beware: the *Lean* library also defines a version of ``pow``
that works for more general structures,
and it uses ``b * pow n`` instead of ``pow n * b`` in the recursive call.
Hopefully, someone will take the initiative to eventually merge the two,
but in the meanwhile,
we are in the unfortunate situation that we are using different parts of the
library depending on whether we are raising a ``nat`` or an element
of some other structure to a power.

In a moment, we will show formally that ``succ`` is injective.
We can use this to prove the cancellation law for addition,
namely, if ``m + n = k + n`` then ``m = k``.
The natural way to prove this is by induction on ``n``.
But now something strange is happening: we are doing
induction on a variable that occurs only in a hypothesis.
Step through the proof below and see how Lean handles it.

.. code-block:: lean

    open nat

    variables m n k : ℕ

    namespace my_nat

    -- BEGIN
    theorem add_right_cancel (h : m + n = k + n) : m = k :=
    begin
      induction n with n ih,
      { apply h },
      apply ih,
      apply succ.inj h
    end
    -- END

    end my_nat

As expected, there is a zero case and an induction step,
but the inductive hypothesis is now an *implication*:
``m + n = k + n → m = k``.
In other words, the induction tactic uses the
principle of induction to prove the general statement
"for every ``n``, if ``m + n = k + n`` then ``m = k``"
by induction on ``n``.
It does this by *reverting* the hypothesis, ``h``,
applying the induction principle,
and *reintroducing* it in the induction step.
In the next chapter, you will learn how to do
this manually, and also how to carry out induction
on other compound statements.
At this point, we only ask you to notice that
induction is doing something interesting under the hood.
As with all tactics, you can learn more about the
induction step by reading the description that appears
when you hover over it or looking it up in the
`mathlib documentation <https://leanprover-community.github.io/mathlib_docs/>`_.
You can also learn more about the way Lean supports
reasoning about inductively defined
structures in `Theorem Proving in Lean`_.

We can avoid the need for a compound induction hypothesis
by defining other functions first.
The *predecessor* function on the natural numbers subtracts one,
but clips at zero,
so we have ``pred 0 = 0``.
Similarly, *truncated subtraction* on the natural numbers,
denoted ``m - n`` in the library,
subtracts ``n`` from ``m`` but returns zero
if ``n`` is bigger.
They are defined recursively as follows:

.. code-block:: lean

    namespace my_nat

    -- BEGIN
    def pred : ℕ → ℕ
    | 0     := 0
    | (n+1) := n

    def sub (m : ℕ) : ℕ → ℕ
    | 0     := m
    | (n+1) := pred (sub n)
    -- END

    end my_nat

The predecessor function can be used to prove the injectivity of ``succ``.
Here we use the ``show`` command to change
the goal to one the is definitionally equal to the original one.
Using ``show`` forces Lean to recognize that fact
by unfolding the computational rule for ``pred``.

.. code-block:: lean

    open nat

    variables m n : ℕ

    -- BEGIN
    example (h : succ m = succ n) : m = n :=
    begin
      show pred (succ m) = pred (succ n),
      rw h
    end
    -- END

We challenge you to use the definitions of ``pred`` and ``succ``
to prove ``m + n - n = m``,
a fact known as ``add_sub_cancel`` in the library.
The proof is easy if you find just the right
auxiliary fact to prove first.
Can you figure out what it is?
If you succeed, you can go on to use ``add_sub_cancel``
to prove ``add_right_cancel`` if you wish.

.. the answer: ``succ m - succ n = m - n``.

.. code-block:: lean

    open nat

    variables m n : ℕ

    -- BEGIN
    example : m + n - n = n :=
    sorry
    -- END

There are a number of ways to define the less-than-or-equal relation
on the natural numbers.
Given the behavior of truncated subtraction,
we could define ``m ≤ n`` to be ``m - n = 0``.
Or we can say that ``m ≤ n`` if and only if there is a ``k``
such that ``m + k = n``,
which is expressed as ``∃ k, m + k = n`` in Lean.
In fact, the core library uses an inductive definition to define ``≤``,
but the details aren't important.
The equivalence of ``m`` with ``m - n = 0`` is given by
the theorem ``nat.sub_eq_zero_iff_le`` in the library,
and you will easily be able to establish the second
equivalence once we show you how to use the existential quantifier.


Carrying out Computations
-------------------------

Defining the operations of arithmetic on the natural numbers
and establishing their fundamental properties is interesting,
but it does not feel like *real* mathematics.
we have taken facts about the natural numbers for granted
since we were schoolchildren,
and we should expect any good formal library to make them readily available.
What we really need to know is how to use the
natural numbers to prove more interesting theorems.
We will turn to that in the next section.
First, we will say a bit more about proving statements
that are "obvious" or "just calculation."

The computational side of Lean's foundation means that
we can not only reason about the natural numbers,
but compute with them.
The ``#eval`` command will evaluate any closed expression
that Lean is capable of evaluating.

.. code-block:: lean

    #eval 12345 * 6789

It is appealing that, in Lean, we can define the factorial
function, prove theorems above it, and then calculate:

.. code-block:: lean

    def factorial : ℕ → ℕ
    | 0     := 1
    | (n+1) := (n+1) * factorial n

    theorem factorial_pos (n : ℕ) : 0 < factorial n :=
    begin
      induction n with n ih,
      { apply zero_lt_one },
      exact mul_pos (nat.succ_pos _) ih
    end

    #eval factorial 100

The ``#eval`` command is also sometimes helpful
for giving us a sense of what a function does.
Of course, in mathematics we can define functions
that cannot be computed.
But Lean does a good job of keeping track of which ones
are computable
and evaluating them when it can.

But the ``#eval`` command cannot be used to prove theorems.
For evaluation, Lean extracts bytecode from the definitions and
executes it efficiently,
without justifying the computation axiomatically.
If we insist on having formal proofs of all our claims,
we cannot trust ``#eval``.

So how do we establish a simple computational claim like
``2 + 2 = 4``?
This is where definitional equality,
which *is* part of Lean's trusted kernel,
is helpful. In this case, Lean can unfold definitions and
apply computational reductions to determine that
both sides come out the same:

.. code-block:: lean

    example : 2 + 2 = 4 :=
    rfl

Be careful: unfolding definitions and computing is o.k. for
small calculations, but it is inefficient.
Unfolding the definitions of addition and multiplication
amount to calculating with numbers in unary notation.
For more substantial calculations, use ``norm_num``:

.. code-block:: lean

    import tactic

    example : 12345 * 6789 = 83810205 :=
    by norm_num

Like ``ring``, ``norm_num`` is a more substantial piece
of automation. It constructs efficient proofs using
binary representation.
It works for equally well for the real numbers,
and other structures that support numerals.

.. code-block:: lean

    import tactic
    import data.real.basic

    example : (12345 : ℝ) * 6789 = 83810205 :=
    by norm_num

The ``norm_num`` tactic is designed specifically
for numeric calculation.
In contrast, definitional reduction is more general. For example, it can be used to confirm the result of concatenating two lists of numbers:

.. code-block:: lean

    example : [1, 2, 3] ++ [4, 5] = [1, 2, 3, 4, 5] :=
    rfl

What about proving facts like ``2 + 2 < 5``?
For statements like this one
that are built up from computable relations,
the proof term ``dec_trivial``
finds the means to construct a proof:

.. code-block:: lean

    example : 2 + 2 < 5 :=
    dec_trivial

It also relies on definitional reduction,
and so is fairly general.
For example, in the next section,
we will learn that ``range 10`` denotes
the finite set of natural numbers less than ``10``,
where the ``range`` function is in the
``finset`` namespace. The term ``dec_trivial``
show that ``3`` is in that set:

.. code-block:: lean

    import data.finset

    open finset

    example : 3 ∈ range 10 :=
    dec_trivial

It can even do bounded iteration to show that
23 is not a product of two numbers that
are less than or equal to 5.

.. code-block:: lean

    import data.nat.basic

    example : ∀ x ≤ 5, ∀ y ≤ 5, x * y ≠ 23 :=
    dec_trivial

But once again, be careful: ``dec_trivial``
is inefficient, and not designed for long calculations.
When it can be used, the ``norm_num`` tactic
is more efficient:

.. code-block:: lean

    import tactic

    example : 12345 * 6789 < 83810206 :=
    by norm_num

The tactic can also show that numbers are prime:

.. code-block:: lean

    import tactic

    open nat

    example : prime 257 :=
    by norm_num

If you are running this tutorial in VS Code,
try replacing ``257`` with ``65537``.
The tactic should still succeed in a few seconds.

The general question as to how to efficiently verify
computational results and use them in proofs in trusted ways
falls under the heading *computational reflection*.
This is a very important topic,
and not one that we can fully address here.
But tools like ``ring`` and ``norm_num``
cover some of the most basic instances.

Another useful tool for carrying calculations is Lean's
term rewriting tactic, known as ``simp``.
The ``simp`` tactic tries to simplify a goal using
a collection of facts that have been marked as
simplification rules, typically facts like ``x + 0 = x``
and ``x * 1 = x``.

.. code-block:: lean

    example (m n : ℕ) (f : ℕ → ℕ) : f (m * 1 + 0 + n) = f (m + n) :=
    by simp

This can save you the trouble of looking for facts in the library
and applying them manually.
It can also provide a learning experience.
Mathlib offers a variant of ``simp`` called ``squeeze_simp``
which calls ``simp``,
determines the list of simplification rules that were used,
and suggests calling ``simp`` more efficiently with this smaller list.
If you ``import tactic`` and replace ``simp`` by ``squeeze_simp``
in the previous example,
the output in the Lean Goal window will suggest using the following:

.. code-block:: lean

    example (m n : ℕ) (f : ℕ → ℕ) : f (m * 1 + 0 + n) = f (m + n) :=
    by simp only [add_zero, mul_one]

The simplifier can also prove theorems by simplifying them to ``true``:

.. code-block:: lean

    example (m : ℕ) : 1 ∣ m :=
    by simp

It will perform *conditional rewriting*, which is to say,
it will try to rewrite using an identity with hypotheses
by rewriting the hypotheses themselves to ``true``.
In the next example, the line that beings ``local attribute`` tells
the simplifier that in the current section or file,
it should use the rule ``abs_of_nonneg``,
which says ``abs a = a`` when ``a ≥ 0``.
The command ``simp *`` tells the simplifier to use the
facts in the local context as well as its battery of
simplification rules.

.. code-block:: lean

    import data.real.basic

    local attribute [simp] abs_of_nonneg

    example (a : ℝ) (f : ℝ → ℝ) (h: a ≥ 0) : f (abs a) = f a :=
    by simp *

The simplifier can also use *permutative conversions* like
``a + b = b + a``.
To avoid looping,
the simplifier only applies the rule if it makes the
term smaller under some arbitrary but fixed ordering of terms.
This provides a useful trick for proving identities
with expressions involving an operation that is associative
and commutative. Simplifying using those two properties
and a funny combination of the two,
*left commutativity*, has the net effect of moving
all parentheses to the left and
put the terms in the canonical order.

.. code-block:: lean

    example (a b c d e f : ℕ) : a + b + (c + d) + (e + f) =
      f + (d + (c + b)) + e + a :=
    by simp [add_assoc, add_comm, add_left_comm]

    example (a b c d e f : ℕ) : min (min (min a b) (min c d)) (min e f) =
      min (min (min f (min d (min c b))) e) a :=
    by simp [min_assoc, min_comm, min_left_comm]

As usual, you can learn more about the simplifier
and the various options in the mathlib documentation
`mathlib documentation <https://leanprover-community.github.io/mathlib_docs/>`_
or `Theorem Proving in Lean`_.
We recommend using ``simp`` sparingly,
since it can slow down complication of proofs and it is
not a substitute for learning how to do things by hand.
But with judicious use, it can be quite helpful.

We close this section with a few small tricks
that are often useful for reasoning about the natural numbers.
First, it is convenient that ``m < n`` and ``m + 1 ≤ n``
are definitionally the same:

.. code-block:: lean

    variables m n : ℕ

    -- BEGIN
    example (h : m < n) : m + 1 ≤ n := h

    example (h : 0 < n)  : 1 ≤ n := h
    -- END

The hypotheses ``n ≠ 0`` are equivalent ``0 < n``,
but mathlib favors the second.
Fortunately it is easy to convert between the two:

.. code-block:: lean

    variable n : ℕ

    -- BEGIN
    example (h : n ≠ 0) : 0 < n :=
    nat.pos_of_ne_zero h

    example (h : 0 < n) : n ≠ 0 :=
    ne_of_gt h
    -- END

Reasoning with truncated subtraction is inconvenient,
because most of the facts in the library that support calculation
with subtraction have side conditions on the size of the arguments.
To prove ``m - n + k``, it is often easier to prove ``m + n = k``.

.. code-block:: lean

    import data.nat.basic

    variables m n k : ℕ

    -- BEGIN
    example (h : m = k + n) : m - n = k :=
    by simp [h]
    -- END

In fact, it is often more useful to state theorems in terms of
addition rather than subtraction.
The same holds for multiplication and division.
When ``m`` and ``n`` are natural numbers,
``m / n`` denotes the natural number part of the quotient, and
``m % n`` denotes the remainder.
Often the best way to prove ``m = k / n``
is to prove ``m * n = k``.

.. code-block:: lean

    variables m n k : ℕ

    -- BEGIN
    example (h : m * n = k) (h' : n > 0) : m = k / n :=
    begin
      symmetry,
      apply nat.div_eq_of_eq_mul_left h' h.symm,
    end
    -- END

This snippet illustrates two ways of turning an equation ``a = b``
to the equation ``b = a``.
The ``symmetry`` tactic reverses the equation in the goal,
and in this case that allows us to apply a theorem in which the identity
goes the other way.
Given ``h : a = b``, the expression ``eq.symm h`` is a proof of ``b = a``.
Since ``a = b`` is an abbreviation for ``eq a b``,
Lean's *anonymous projection* notation allows us to write ``h.symm``
for ``eq.symm h``.
So the proof above reverses the direction of ``h`` so we can
apply ``nat.div_eq_of_eq_mul_left h'``,
and then reverses the direction of the result to prove the goal.

The example above gives us an opportunity to introduce another
useful syntactic gadget that is available to us in Lean.
If ``e₁`` and ``e₂`` are expressions,
then ``e₁ $ e₂`` abbreviates ``e₁ (e₂)``.
This allows us to apply an expression ``e₁`` to
another complex expression ``e₂``
without having to remember to close a parenthesis at the end.
With this notation,
we can replace the tactic proof above with a one-line proof term:

.. code-block:: lean

    variables m n k : ℕ

    -- BEGIN
    example (h : m * n = k) (h' : n > 0) : m = k / n :=
    eq.symm $ nat.div_eq_of_eq_mul_left h' h.symm
    -- END

Sums and Products
-----------------

.. reference to sets, functions, and relations chapter

For every type ``α``,
Lean offers us a datatype, ``finset α``,
that consists of finite sets of elements of ``α``.
In a later chapter, we will learn more about ``finset α``
and how to use it.
What is of interest to us here is that Lean
will also allow us to write down finite sums and products
indexed by elements of any such set.
Two particular constructions of finite sets are
especially useful in this respect.
For every natural number ``n``,
``finset.range n`` is the finite set of numbers less than ``n``,
and for every pair of natural numbers ``m`` and ``n``,
``finset.Ico m n`` is the finite set of natural numbers that are greater
than or equal to ``m`` and less than ``n``.

.. code-block:: lean

    import data.finset

    open finset

    #eval range 5
    #eval Ico 3 7

    example : range 5 = {0, 1, 2, 3, 4} :=
    dec_trivial

    example : range 5 = {4, 1, 2, 0, 0, 3} :=
    dec_trivial

    example : Ico 3 7 = {3, 4, 5, 6} :=
    dec_trivial

    example : Ico 3 7 = {6, 3, 3, 5, 4} :=
    dec_trivial

In ``Ico``, the letter ``I`` suggests an interval, ``c`` stands for "closed", and ``o`` stands for "open."

In Lean, the expression ``λ x, x^2`` denotes the function which maps
any ``x`` to ``x^2``.
This is known as *lambda notation*,
and the Greek letter lambda can be entered with ``\lam`` in VS Code.
Often the type of ``x`` can be inferred from context,
but you can also write, for example,
``λ x : ℕ, x^2`` to mean the squaring function on the natural numbers.
The two expressions below therefore represent the sum of the
square function over the sets ``{0, 1, 2, 3, 4}`` and ``{3, 4, 5, 6}``
respectively.
Compute these yourself before checking Lean's answer.

.. code-block:: lean

    import algebra.big_operators

    open finset

    #eval finset.sum (range 5) (λ x, x^2)
    #eval finset.sum (Ico 3 7) (λ x, x^2)

In the ``import`` line, the phrase "big operators" refers to the extension of binary operations like
sums, product, min, and max to finite sets.
We have opened the ``finset`` namespace to use the names ``range`` and ``Ico``,
but we still have to qualify the name ``sum``.
Lean's anonymous projection notation provides a slight improvement:

.. code-block:: lean

    import algebra.big_operators

    open finset

    -- BEGIN
    #eval (range 5).sum (λ x, x^2)
    #eval (Ico 3 7).sum (λ x, x^2)
    -- END

In the next snippet, the command ``open_locale big_operators``
tells Lean that we want to use notation
defined for big operators.

.. code-block:: lean

    import algebra.big_operators

    -- BEGIN
    open finset
    open_locale big_operators

    #eval ∑ x in range 5, x^2
    #eval ∑ x in Ico 3 7, x^2
    -- END

The summation symbol is entered as ``\sum``.
Try using this notation to calculate the sum of the natural numbers from
1 to 100. The summation operation is quite general;
it can be used to sum values in any structure that has a
commutative, associative addition operation and a zero.
The two theorems indicated below make summation with
the ``range`` function a prime candidate for proof by induction.

.. code-block:: lean

    import algebra.big_operators

    open finset
    open_locale big_operators

    -- BEGIN
    variables {α : Type*} [add_comm_monoid α]
    variables (n : ℕ) (f : ℕ → α)

    #check (sum_range_zero f : ∑ x in range 0, f x = 0)
    #check (sum_range_succ f n :
      ∑ i in range (n + 1), f i = f n + (∑ i in range n, f i))
    -- END

We can use these, for example, to derive the usual formula
for the sum of the natural numbers from 1 to ``n``:

.. code-block:: lean

    import algebra.big_operators

    open finset
    open_locale big_operators

    variable n : ℕ

    -- BEGIN
    example : 2 * ∑ i in range (n + 1), i = n * (n + 1) :=
    begin
      induction n with n ih,
      { simp },
      rw [sum_range_succ, mul_add, ih],
      simp only [nat.succ_eq_add_one],
      ring
    end
    -- END

If you step through this proof,
there should be nothing surprising.
In the inductive step, we use ``sum_range_succ`` to
expand the sum, and then we use the inductive hypothesis.
We use the simplifier to rewrite ``succ n`` everywhere to ``n + 1``,
at which point,
the ``ring`` tactic finishes off the calculation.

See if you can use the methods introduced in the last section
to express this result in its more familiar form:

.. code-block:: lean

    import algebra.big_operators

    open finset
    open_locale big_operators

    variable n : ℕ

    -- BEGIN
    example : ∑ i in range (n + 1), i = n * (n + 1) / 2 :=
    sorry
    -- END

Also show that almost exactly the same proof works for sums of squares.
The only difference is that at one point you need to use
the theorem ``nat.pow_two`` to expand ``n^2`` into a product.

.. code-block:: lean

    import algebra.big_operators

    open finset
    open_locale big_operators

    variable n : ℕ

    -- BEGIN
    example : 6 * ∑ i in range (n + 1), i^2 = n * (n + 1) * (2*n + 1) :=
    sorry
    -- END

It also works for sums of cubes.

.. code-block:: lean

    import algebra.big_operators

    open finset
    open_locale big_operators

    variable n : ℕ

    -- BEGIN
    example : 4 * ∑ i in range (n + 1), i^3 = n^2 * (n + 1)^2 :=
    begin
      have pow_three : ∀ n : nat, n^3 = n * n * n,
      { intro n, simp [nat.pow_succ] },
      sorry
    end
    -- END

The same approach can be used to derive the formula
for geometric sums.
At an opportune moment,
you can use ``pow_succ`` to replace ``r^(n+1)`` by ``r * r^n``.

.. code-block:: lean

    import algebra.big_operators
    import data.real.basic

    open finset
    open_locale big_operators

    -- BEGIN
    variables (n : ℕ) (r : ℝ)

    example : (r - 1) * (∑ i in range n, r^i) = r^n - 1 :=
    sorry
    -- END

In fact, the same proof should work if you replace the real numbers
by any commutative ring.

.. code-block:: lean

    import algebra.big_operators
    import data.real.basic

    open finset
    open_locale big_operators

    -- BEGIN
    variables {R : Type*} [comm_ring R] (n : ℕ) (r : R)

    example : (r - 1) * (∑ i in range n, r^i) = r^n - 1 :=
    sorry
    -- END

In Lean, finite products work much the same way as finite sums.
To illustrate, let's relate the factorial function with the
corresponding product.
In Lean, the factorial function on the natural numbers
is called ``nat.fact``,
and the two expected computation rules are
``nat.fact_zero`` and ``nat.fact_succ``.
The following snippet declares convenient notation:

.. code-block:: lean

    import data.nat.basic

    local postfix !:90 := nat.fact

Here is a useful fact: when you call the ``rw`` tactic
with the name of a recursively defined function instead of
a theorem,
it uses the associated defining equations. So you can
use ``rw [nat.fact]`` instead of ``rw [nat.fact_zero]`` and ``rw [nat.fact_succ]``.

.. code-block:: lean

    import data.nat.basic

    local postfix !:90 := nat.fact

    -- BEGIN
    example : 0! = 1 :=
    by rw [nat.fact]

    example (n : ℕ) : (n+1)! = (n+1) * n! :=
    by rw [nat.fact]
    -- END

The same trick works with ``simp``: use ``simp [nat.fact]``
when you want to simply ``nat.fact 0`` and ``nat.fact (n + 1)``
everywhere in an expression.

Use induction to show that the factorial function
is equal to the corresponding product:

.. code-block:: lean

    import algebra.big_operators

    open finset
    open_locale big_operators

    local postfix !:90 := nat.fact

    -- BEGIN
    example (n : ℕ) : n! = ∏ i in range n, (i + 1) :=
    sorry
    -- END

The next example illustrates three things:
first, the use of ``rw [nat.fact]``.
second, the fact that ``1 ≤ n!``
is definitionally equal to ``0 < n!``.
and, third, the use of ``show`` to
express the goal in a more convenient form.

.. code-block:: lean

    import algebra.big_operators

    open finset
    open_locale big_operators

    local postfix !:90 := nat.fact

    -- BEGIN
    example (n : ℕ) : 1 ≤ n! :=
    begin
      induction n with n ih,
      { rw [nat.fact] },
      rw nat.fact,
      show 0 < (n + 1) * n!,
      apply mul_pos,
      apply nat.succ_pos,
      apply ih
    end
    -- END

Finally, let us end this section with an example
that uses the ``cases`` and ``contradiction`` tactics,
which will be introduced properly in the next  chapter.

.. code-block:: lean

    import algebra.big_operators

    open finset
    open_locale big_operators

    local postfix !:90 := nat.fact

    -- BEGIN
    example (n i : ℕ) (h : i ≠ 0) (h' : i ≤ n) : i ∣ n! :=
    begin
    induction n with n ih,
    { intros, simp at h', contradiction  },
    cases h' with _ h',
    { apply dvd_mul_right },
    apply dvd_mul_of_dvd_right,
    apply ih h',
    end
    -- END

Because the inductive hypothesis, ``h'``, depends on ``n`,
the ``induction`` tactic includes it in the inductive hypothesis.
In the base case, we have ``i ≠ 0`` and ``i ≤ 0``,
and we use the simplifier and the ``contradiction`` tactic
to show that these are contradictory.
In the induction step, we have ``i ≤ n + 1``,
which is equivalent to saying that either ``i = n + 1`` or ``i ≤ n``.
We use the ``cases`` tactic,
to split on these two cases,
and in the second case we use the inductive hypothesis.


Fibonacci Numbers
-----------------

[Watch this space.]


The AM-GM Inequality
--------------------

[Watch this space.]


.. _`Theorem Proving in Lean`: https://leanprover.github.io/theorem_proving_in_lean/