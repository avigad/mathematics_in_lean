import tactic

def gaussian_integer := ℤ × ℤ

notation `ℤ[i]` := gaussian_integer

namespace gaussian_integer

def zero : ℤ[i] := ⟨0, 0⟩
def one : ℤ[i]  := ⟨1, 0⟩
def ii : ℤ[i]   := ⟨0, 1⟩

def add : ℤ[i] → ℤ[i] → ℤ[i] := λ ⟨a, b⟩ ⟨c, d⟩, ⟨a + c, b + d⟩
def mul : ℤ[i] → ℤ[i] → ℤ[i] := λ ⟨a, b⟩ ⟨c, d⟩, ⟨a*c - b*d, a*d + b*c⟩
def neg : ℤ[i] → ℤ[i]        := λ ⟨a, b⟩, ⟨-a, -b⟩

instance : has_zero ℤ[i] := ⟨zero⟩
instance : has_one  ℤ[i] := ⟨one⟩
instance : has_add  ℤ[i] := ⟨add⟩
instance : has_mul  ℤ[i] := ⟨mul⟩
instance : has_neg  ℤ[i] := ⟨neg⟩

def mk (x y : ℤ) : ℤ[i] := (x, y)
def re (w : ℤ[i]) : ℤ := w.1
def im (w : ℤ[i]) : ℤ := w.2

theorem re_mk (x y : ℤ) : re (mk x y) = x := rfl

theorem im_mk (x y : ℤ) : im (mk x y) = y := rfl

theorem mk_re_im (z : ℤ[i]): mk (re z) (im z) = z :=
by { cases z, refl }

theorem re_add (w z : ℤ[i]) : re (w + z) = re w + re z :=
by { cases w, cases z, refl }

theorem im_add (w z : ℤ[i]) : im (w + z) = im w + im z :=
by { cases w, cases z, refl }

theorem re_mul (w z : ℤ[i]) : re (w * z) = re w * re z - im w * im z :=
by { cases w, cases z, refl }

theorem im_mul (w z : ℤ[i]) : im (w * z) = re w * im z + im w * re z :=
by { cases w, cases z, refl }

theorem re_neg (w : ℤ[i]) : re (-w) = - re w :=
by { cases w, refl }

theorem im_neg (w : ℤ[i]) : im (-w) = - im w :=
by { cases w, refl }

theorem re_ii : re ii = 0 := rfl

theorem im_ii : im ii = 1 := rfl

-- BEGIN
attribute [simp] re_add im_add re_mul im_mul re_neg im_neg
  re_ii im_ii re_ii im_ii

@[ext] theorem ext {z w : ℤ[i]} (h1 : re z = re w) (h2 : im z = im w) :
  z = w :=
begin
  cases z with z1 z2,
  cases w with w1 w2,
  simp [re, im, *] at *
end
-- END

end gaussian_integer