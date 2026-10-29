/-
IMO 2012 N1 (Number Theory, Problem 1)

Let R be a commutative ring.
A set A ⊆ R is called *admissible* if for any x, y ∈ A and r ∈ R,
  x² + rxy + y² ∈ A.
Determine all pairs (x, y) ∈ R² such that the only
  admissible set containing x and y is R.

Answer: Any pair (x, y) such that x and y are coprime.

Solution follows the official IMO 2012 Shortlist solution,
formalized by Gian Cordana Sanjaya (IMOSLLean4).
Adapted to standalone project for benchmarking.
-/
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Span

namespace IMO2012N1

/-- Definition of *admissible* subset of `R`. -/
def admissible [Semiring R] (A : Set R) :=
  ∀ x y : R, x ∈ A → y ∈ A → ∀ r : R, x ^ 2 + r * x * y + y ^ 2 ∈ A

/-- An ideal of `R` is always admissible as a set. -/
theorem admissible_ideal [CommSemiring R] (I : Ideal R) : admissible (I : Set R) := by
  intro u v h h0 r
  rw [sq, sq, add_assoc, ← add_mul]
  exact I.add_mem (I.mul_mem_left u h) (I.mul_mem_left _ h0)

namespace admissible

variable [CommRing R] {A : Set R} (hA : admissible A)
include hA

/-- If `A ⊆ R` is admissible and `z ∈ A`, then `rz² ∈ A` for any `r ∈ A`. -/
theorem mul_sq_mem (hz : z ∈ A) (r : R) : r * z ^ 2 ∈ A := by
  convert hA z z hz hz (r - 2) using 1
  rw [add_right_comm, ← two_mul, mul_assoc, ← sq, ← add_mul, add_sub_cancel]

/-- If `A ⊆ R` is admissible and `x, y ∈ A`, then `(x + y)² ∈ A`. -/
theorem add_sq_mem (hx : x ∈ A) (hy : y ∈ A) : (x + y) ^ 2 ∈ A :=
  add_sq x y ▸ hA x y hx hy 2

/-- If `A ⊆ R` is admissible and `1 ∈ A`, then `A` contains every element of `R`. -/
theorem one_mem_imp (hA0 : 1 ∈ A) (z : R) : z ∈ A := by
  simpa only [one_pow, mul_one] using hA.mul_sq_mem hA0 z

end admissible

/-- Final solution: the only admissible set containing x and y is R iff x and y are coprime. -/
theorem final_solution [CommRing R] {x y : R} :
    (∀ A : Set R, admissible A → x ∈ A → y ∈ A → ∀ z : R, z ∈ A) ↔ IsCoprime x y := by
  refine ⟨fun hxy => ?_, fun hxy A hA hx hy => ?_⟩
  · rw [IsCoprime, ← Ideal.mem_span_pair]
    exact hxy (Ideal.span {x, y}) (admissible_ideal _)
      (Ideal.subset_span (Set.mem_insert x _))
      (Ideal.subset_span (Set.mem_insert_of_mem x rfl)) 1
  · apply hA.one_mem_imp
    obtain ⟨a, b, h⟩ : IsCoprime (x ^ 2) (y ^ 2) := IsCoprime.pow hxy
    simpa only [h, one_pow] using hA.add_sq_mem (hA.mul_sq_mem hx a) (hA.mul_sq_mem hy b)

end IMO2012N1
