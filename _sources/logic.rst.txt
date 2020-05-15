.. _logic:

Logic
=====

In the last chapter, we dealt with equations, inequalities,
and basic mathematical statements like
":math:`x` divides :math:`y`."
Complex mathematical statements are built up from
simple ones like these
using logical terms like "and," "or," "not," and
"if ... then," "every," and "some."
In this chapter, we show you how to work with statements
that are built up in this way.


.. _using_implication_and_the_universal_quantifier:

Implication and the Universal Quantifier
----------------------------------------

Consider the statement after the ``#check``:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    #check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε
    -- END

In words, we would say "for every ``x``, ``y``, and ``ε``,
if ``0 < ε ≤ 1``, the absolute value of ``x`` is less than ``ε``,
and the absolute value of ``y`` is less than ``ε``,
then the absolute value of ``x * y`` is less than ``ε``."
In Lean, the implication arrows associate to the right,
making it easy to chain implications in this way.

You have already seen that even though the universal quantifier
in this statement
ranges over objects and the implication arrows introduce hypotheses,
Lean treats the two in very similar ways.
In particular, if you have proved a theorem of that form,
you can apply it to objects and hypotheses in the same way:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    lemma my_lemma :
      ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
    sorry

    section
      variables a b δ : ℝ
      variables (h₀ : 0 < δ) (h₁ : δ ≤ 1) (ha : abs a < δ) (hb : abs b < δ)

      #check my_lemma a b δ
      #check my_lemma a b δ h₀ h₁
      #check my_lemma a b δ h₀ h₁ ha hb
    end
    -- END

You have also already seen that it is common in Lean
to use curly brackets to make quantified variables implicit
when they can be inferred from subsequent hypotheses.
When we do that, we can just apply a lemma to the hypotheses without
mentioning the objects.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    lemma my_lemma :
      ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
    sorry

    section
      variables a b δ : ℝ
      variables (h₀ : 0 < δ) (h₁ : δ ≤ 1) (ha : abs a < δ) (hb : abs b < δ)

      #check my_lemma h₀ h₁ ha hb
    end
    -- END

At this stage, you also know that if you use
the ``apply`` tactic to apply ``my_lemma``
to a goal of the form ``abs (a * b) < δ``,
you are left with new goals that require you to  prove
each of the hypotheses.

To prove a statement like this, use the ``intros`` tactic.
Take a look at what it does in this example:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    lemma my_lemma :
      ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
    begin
      intros x y ε epos ele1 xlt ylt,
      sorry
    end
    -- END

We can use any names we want for the universally quantified variables;
they do not have to be ``x``, ``y``, and ``ε``.
(If there is only one variable, you can use the singular ``intro``
instead of ``intros``.)
After the ``intros`` command,
the goal is what it would have been at the start if we
listed all the variables and hypotheses *before* the colon,
as we did in the last section.
In a moment, we will see why it is sometimes necessary to
introduce variables and hypotheses after the proof begins.

To help you prove the lemma, we will start you off:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    lemma my_lemma :
      ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
    begin
      intros x y ε epos ele1 xlt ylt,
      suffices h : abs x * abs y < 1 * ε,
      { rw [←abs_mul, one_mul] at h,
        apply h },
      calc
        abs x * abs y ≤ abs x * ε : sorry
        ... < 1 * ε               : sorry
    end
    -- END

We have introduced another new tactic here:
``suffices`` works like ``have`` in reverse,
asking you to prove the goal using the
stated fact,
and then leaving you the new goal of proving that fact.
Finish the proof using the theorems ``mul_le_mul``,
``abs_nonneg``, and ``mul_lt_mul_right``.
Remember that you can find theorems like these using
tab completion.
Remember also that you can use ``.mp`` and ``.mpr``
or ``.1`` and ``.2`` to extract the two directions
of an if-and-only-if statement.

Universal quantifiers are often hidden in definitions,
and Lean will unfold definitions to expose them when necessary.
For example, let's define two predicates,
``fn_ub f a`` and ``fn_lb f a``,
where ``f`` is a function from the real numbers to the real
numbers and ``a`` is a real number.
The first says that ``a`` is an upper bound on the
values of ``f``,
and the second says that ``a`` is a lower bound
on the values of ``f``.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x
    -- END

In the next example, remember that ``λ x, f x + g x`` is the
function that maps ``x`` to ``f x + g x``.

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    -- BEGIN
    example {f g : ℝ → ℝ} {a b : ℝ} (hfa : fn_ub f a) (hgb : fn_ub g b) :
      fn_ub (λ x, f x + g x) (a + b) :=
    begin
      intro x,
      dsimp,
      apply add_le_add,
      apply hfa,
      apply hgb
    end
    -- END

Applying ``intro`` to the predicate ``fn_ub (λ x, f x + g x) (a + b)``
forces Lean to unfold the definition of ``fn_ub``
and introduce ``x`` for the universal quantifier.
The goal is then ``(λ (x : ℝ), f x + g x) x ≤ a + b``.
But applying ``(λ x, f x + g x)`` to ``x`` should result in ``f x + g x``,
and the ``dsimp`` command performs that simplification.
(The "d" stands for "definitional.")
You can delete that command and the proof still works;
Lean would have to perform that contraction anyhow to make
sense of the next ``apply``.
The ``dsimp`` command simply makes the goal more readable
and helps us figure out what to do next.
The rest of the proof is routine.
The last two ``apply`` commands force Lean to unfold the definitions
of ``fn_ub`` in the hypotheses.
Try carrying out similar proofs of these:

.. code-block:: lean

    import data.real.basic

    def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
    def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

    variables (f g : ℝ → ℝ) (a b : ℝ)

    -- BEGIN
    example (hfa : fn_lb f a) (hgb : fn_lb g b) : fn_lb (λ x, f x + g x) (a + b) :=
    sorry

    example (nnf : fn_lb f 0) (nng : fn_lb g 0) : fn_lb (λ x, f x * g x) 0 :=
    sorry

    example (hfa : fn_ub f a) (hfb : fn_ub g b) (nng : fn_lb g 0) (nna : 0 ≤ a) :
      fn_ub (λ x, f x * g x) (a * b) :=
    sorry
    -- END

Even though we have defined ``fn_lb`` and ``gn_lb`` for functions
from the reals to the reals,
you should recognize that the definitions and proofs are much
more general.
The definitions make sense for functions between any two types
for which there is a notion of order on the codomain.
Checking the type of the theorem ``add_le_add`` shows that it holds
of any structure that is an "ordered additive commutative monoid";
the details of what that means don't matter now,
but it is worth knowing that the natural numbers, integers, rationals,
and real numbers are all instances.
So if we prove the theorem ``fn_ub_add`` at that level of generality,
it will apply in all these instances.

.. code-block:: lean

    variables {α : Type*} {R : Type*} [ordered_cancel_add_comm_monoid R]

    #check @add_le_add

    def fn_ub (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

    theorem fn_ub_add (f g : α → R) (a b : R) (hfa : fn_ub f a) (hgb : fn_ub g b) :
      fn_ub (λ x, f x + g x) (a + b) :=
    λ x, add_le_add (hfa x) (hgb x)

For concreteness, we will stick to the real numbers
for most of our examples,
but it is worth knowing that mathlib contains definitions and theorems
that work at a high level of generality.

For another example of a hidden universal quantifier,
mathlib defines a predicate ``monotone``,
which says that a function is nondecreasing in its arguments:

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    example (f : ℝ → ℝ) (h : monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b := h
    -- END

Proving statements about monotonicity
involves using ``intros`` to introduce two variables,
say, ``a`` and ``b``, and the hypothesis ``a ≤ b``.
To *use* a monotonicity hypothesis,
you can apply it to suitable arguments and hypotheses,
and then apply the resulting expression to the goal.
Or you can apply it to the goal and let Lean help you
work backwards by displaying the remaining hypotheses
as new subgoals.

.. code-block:: lean

    import data.real.basic

    variables (f g : ℝ → ℝ)

    -- BEGIN
    example (mf : monotone f) (mg : monotone g) : monotone (λ x, f x + g x) :=
    begin
      intros a b aleb,
      apply add_le_add,
      apply mf aleb,
      apply mg aleb
    end
    -- END

When a proof is this short, it is often convenient
to give a proof term instead.
The ``intros`` command corresponds to a lambda,
and the remaining term consists of applications.

.. code-block:: lean

    import data.real.basic

    variables (f g : ℝ → ℝ)

    -- BEGIN
    example (mf : monotone f) (mg : monotone g) : monotone (λ x, f x + g x) :=
    λ a b aleb, add_le_add (mf aleb) (mg aleb)
    -- END

Here is a useful trick: if you start writing
the proof term ``λ a b aleb, _`` using
an underscore where the rest of the
expression should go,
Lean will flag an error,
indicating that it can't guess the value of that expression.
If you check the Lean Goal window in VS Code or
hover over the squiggly error marker,
Lean will show you the goal that the remaining
expression has to solve.

Try proving these, with either tactics or proof terms:

.. code-block:: lean

    import data.real.basic

    variables (f g : ℝ → ℝ)

    -- BEGIN
    example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) : monotone (λ x, c * f x) :=
    sorry

    example (mf : monotone f) (mg : monotone g) : monotone (λ x, f (g x)) :=
    sorry
    -- END

Here are some more examples.
A function :math:`f` from :math:`\Bbb R` to
:math:`\Bbb R` is said to be *even* if
:math:`f(-x) = f(x)` for every :math:`x`,
and *odd* if :math:`f(-x) = -f(x)` for every :math:`x`.
The following example defines these two notions formally
and establishes one fact about them.
You can complete the proofs of the others.

.. code-block:: lean

    import data.real.basic

    variables (f g : ℝ → ℝ)

    -- BEGIN
    def even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
    def odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

    example (ef : even f) (eg : even g) : even (λ x, f x + g x) :=
    by { intro x, dsimp, rw [ef, eg] }

    example (of : odd f) (og : odd g) : even (λ x, f x * g x) :=
    sorry

    example (ef : even f) (og : odd g) : odd (λ x, f x * g x) :=
    sorry

    example (ef : even f) (og : odd g) : even (λ x, f (g x)) :=
    sorry
    -- END

You can find implicit universal quantifiers are all over the place,
once you know how to spot them.
Mathlib includes a good library for rudimentary set theory.
Lean's logical foundation imposes the restriction that when
we talk about sets, we are always talking about sets of
elements of some type. If ``x`` has type ``α`` and ``s`` has
type ``set α``, then ``x ∈ s`` is a proposition that
asserts that ``x`` is an element of ``s``.
If ``s`` and ``t`` are of type ``set α``,
then the subset relation ``s ⊆ t`` is defined to mean
``∀ {x : α}, x ∈ s → x ∈ t``.
The variable in the quantifier is marked implicit so that
given ``h : s ⊆ t`` and ``h' : x ∈ s``,
we can write ``h h'`` as justification for ``x ∈ t``.
The following example provides a tactic proof and a proof term
justifying the reflexivity of the subset relation,
and asks you to do the same for transitivity.

.. code-block:: lean

    variables {α : Type*} (r s t : set α)

    example : s ⊆ s :=
    by { intros x xs, exact xs }

    example : s ⊆ s := λ x xs, xs

    example : r ⊆ s → s ⊆ t → r ⊆ t :=
    begin
      sorry
    end

    example : r ⊆ s → s ⊆ t → r ⊆ t :=
    sorry

Just as we defined ``fn_ub`` for functions,
we can define ``set_ub s a`` to mean that ``a``
is an upper bound on the set ``s``,
assuming ``s`` is a set of elements of some type that
has an order associated with it.
In the next example, we ask you to prove that
if ``a`` is a bound on ``s`` and ``a ≤ b``,
then ``b`` is a bound on ``s`` as well.

.. code-block:: lean

    variables {α : Type*} [partial_order α]
    variables (s : set α) (a b : α)

    def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

    example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
    sorry

We close this section with one last important example.
A function :math:`f` is said to be *injective* if for
every :math:`x_1` and :math:`x_2`,
if :math:`f(x_1) = f(x_2)` then :math:`x_1 = x_2`.
Mathlib defines ``function.injective f`` with
``x₁`` and ``x₂`` implicit.
The next example shows that, on the real numbers,
any function that adds a constant is injective.
We then ask you to show that multiplication by a nonzero
constant is also injective.

.. code-block:: lean

    import data.real.basic

    -- BEGIN
    open function

    example (c : ℝ) : injective (λ x, x + c) :=
    begin
      intros x₁ x₂ h',
      apply eq_of_add_eq_add_right h',
    end

    example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
    sorry
    -- END

Finally, show that the composition of two injective functions is injective:

.. code-block:: lean

    open function

    variables {α : Type*} {β : Type*} {γ : Type*}
    variables {g : β → γ} {f : α → β}

    example (injg : injective g) (injf : injective f) : injective (λ x, g (f x)) :=
    begin
      intros x₁ x₂ h,
      apply injf,
      apply injg,
      apply h
    end
