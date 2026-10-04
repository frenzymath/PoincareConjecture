import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Convex interpolation on the real line

Smale, *Diffeomorphisms of the 2-sphere* (1959), Theorem 4, p. 624,
uses convex interpolation to contract increasing interval diffeomorphisms.
We implement its real-line version for maps equal to the identity outside
an interval, including actual smooth inverses and a smooth time parameter
constant near both endpoints. This is the one-dimensional input to the
axis correction in Munkres (1960), Lemma 1.2, p. 194.
-/

set_option autoImplicit false

open Set Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

/-- Smale (1959), Theorem 4, p. 624: convex interpolation from the identity. -/
def lineInterpolation (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  (1 - t) * x + t * f x

/-- The initial endpoint of Smale's interpolation, Theorem 4, p. 624. -/
@[simp] theorem lineInterpolation_zero (f : ℝ → ℝ) (x : ℝ) :
    lineInterpolation f 0 x = x := by
  simp [lineInterpolation]

/-- The final endpoint of Smale's interpolation, Theorem 4, p. 624. -/
@[simp] theorem lineInterpolation_one (f : ℝ → ℝ) (x : ℝ) :
    lineInterpolation f 1 x = f x := by
  simp [lineInterpolation]

/-- Smale's interpolation preserves fixed points for all real parameters;
Theorem 4, p. 624. -/
theorem lineInterpolation_eq_self {f : ℝ → ℝ} {x : ℝ} (hx : f x = x) (t : ℝ) :
    lineInterpolation f t x = x := by
  rw [lineInterpolation, hx]
  ring

/-- Joint smoothness of Smale's interpolation, Theorem 4, p. 624. -/
theorem contDiff_lineInterpolation {f : ℝ → ℝ} {n : ℕ∞ω} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun p : ℝ × ℝ => lineInterpolation f p.1 p.2) := by
  exact ((contDiff_const.sub contDiff_fst).mul contDiff_snd).add
    (contDiff_fst.mul (hf.comp contDiff_snd))

/-- Smoothness of a fixed slice of Smale's interpolation, Theorem 4, p. 624. -/
theorem contDiff_lineInterpolation_slice {f : ℝ → ℝ} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) (t : ℝ) : ContDiff ℝ n (lineInterpolation f t) := by
  exact ((contDiff_const.mul contDiff_id).add (contDiff_const.mul hf))

/-- Spatial derivative in Smale's interval interpolation, Theorem 4, p. 624. -/
theorem hasDerivAt_lineInterpolation {f : ℝ → ℝ} {x d : ℝ}
    (hf : HasDerivAt f d x) (t : ℝ) :
    HasDerivAt (lineInterpolation f t) ((1 - t) + t * d) x := by
  convert! ((hasDerivAt_id x).const_mul (1 - t)).add (hf.const_mul t) using 1
  simp

/-- Positive derivatives remain positive throughout Smale's closed parameter
interval, Theorem 4, p. 624. -/
theorem lineInterpolation_derivative_pos {d t : ℝ} (hd : 0 < d)
    (ht : t ∈ Icc (0 : ℝ) 1) : 0 < (1 - t) + t * d := by
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst t
    norm_num
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht.2) (mul_pos h hd)

/-- Strict monotonicity of Smale's interpolation, Theorem 4, p. 624. -/
theorem strictMono_lineInterpolation {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hpos : ∀ x, 0 < deriv f x)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : StrictMono (lineInterpolation f t) := by
  apply strictMono_of_hasDerivAt_pos
    (fun x => hasDerivAt_lineInterpolation (hf x).hasDerivAt t)
  exact fun x => lineInterpolation_derivative_pos (hpos x) ht

/-- A continuous map fixed outside an interval is surjective. This is the
intermediate value step in the real-line form of Smale's Theorem 4, p. 624.
No order assumption on the two bounds is needed. -/
theorem surjective_of_eq_self_outside_interval {f : ℝ → ℝ}
    (hf : Continuous f) (a b : ℝ)
    (hfix : ∀ x, x ≤ a ∨ b ≤ x → f x = x) : Surjective f := by
  intro y
  have hlo : f (min a y) = min a y := hfix _ (Or.inl (min_le_left _ _))
  have hhi : f (max b y) = max b y := hfix _ (Or.inr (le_max_left _ _))
  have hy : y ∈ Icc (f (min a y)) (f (max b y)) := by
    rw [hlo, hhi]
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc
    ((min_le_right a y).trans (le_max_right b y)) hf.continuousOn hy
  exact ⟨x, hx⟩

/-- Surjectivity of Smale's interpolation when the original map is fixed
outside an interval, Theorem 4, p. 624. -/
theorem surjective_lineInterpolation {f : ℝ → ℝ} (hf : Continuous f)
    (a b : ℝ) (hfix : ∀ x, x ≤ a ∨ b ≤ x → f x = x) (t : ℝ) :
    Surjective (lineInterpolation f t) := by
  apply surjective_of_eq_self_outside_interval
    ((continuous_const.mul continuous_id).add (continuous_const.mul hf)) a b
  exact fun x hx => lineInterpolation_eq_self (hfix x hx) t

/-- Smale's interval interpolation as an actual diffeomorphism of the real
line; Theorem 4, p. 624. Smoothness of the inverse follows from its nonzero
derivative, rather than being an additional hypothesis. -/
noncomputable def lineInterpolationDiffeomorph {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < deriv f x)
    (a b : ℝ) (hfix : ∀ x, x ≤ a ∨ b ≤ x → f x = x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ℝ ≃ₘ[ℝ] ℝ := by
  let e : ℝ ≃ₜ ℝ :=
    (StrictMono.orderIsoOfSurjective (lineInterpolation f t)
      (strictMono_lineInterpolation (hf.differentiable (by simp)) hpos ht)
      (surjective_lineInterpolation hf.continuous a b hfix t)).toHomeomorph
  have he : ContDiff ℝ ∞ (e : ℝ → ℝ) := contDiff_lineInterpolation_slice hf t
  refine
    { toEquiv := e.toEquiv
      contMDiff_toFun := he.contMDiff
      contMDiff_invFun := ?_ }
  apply ContDiff.contMDiff
  exact e.contDiff_symm_deriv
    (fun x => (lineInterpolation_derivative_pos (hpos x) ht).ne')
    (fun x => hasDerivAt_lineInterpolation
      ((hf.differentiable (by simp)) x).hasDerivAt t) he

/-- The underlying function of the interval diffeomorphism is Smale's
explicit formula, Theorem 4, p. 624. -/
@[simp] theorem lineInterpolationDiffeomorph_apply {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < deriv f x)
    (a b : ℝ) (hfix : ∀ x, x ≤ a ∨ b ≤ x → f x = x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : ℝ) :
    lineInterpolationDiffeomorph hf hpos a b hfix t ht x =
      lineInterpolation f t x := rfl

/-- Smale's interpolation with a smooth time cutoff, constant for t <= 1/3
and t >= 2/3; compare Theorem 4, p. 624 and Munkres Theorem 1.3, p. 194. -/
noncomputable def lineIsotopy (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  lineInterpolation f (Real.smoothTransition (3 * t - 1)) x

/-- Joint smoothness of the time-cutoff interpolation used in Smale's
Theorem 4, p. 624. -/
theorem contDiff_lineIsotopy {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => lineIsotopy f p.1 p.2) := by
  have htime : ContDiff ℝ ∞
      (fun p : ℝ × ℝ => Real.smoothTransition (3 * p.1 - 1)) :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_fst).sub contDiff_const)
  exact (contDiff_lineInterpolation hf).comp (htime.prodMk contDiff_snd)

/-- The time-cutoff interpolation is the identity before its initial
transition, as required for concatenation in Smale's Theorem 4, p. 624. -/
theorem lineIsotopy_eq_self {f : ℝ → ℝ} {t : ℝ} (ht : t ≤ 1 / 3) (x : ℝ) :
    lineIsotopy f t x = x := by
  rw [lineIsotopy, Real.smoothTransition.zero_of_nonpos (by linarith)]
  exact lineInterpolation_zero f x

/-- The time-cutoff interpolation reaches its final map on a neighborhood
of time one; Smale's Theorem 4, p. 624. -/
theorem lineIsotopy_eq_map {f : ℝ → ℝ} {t : ℝ} (ht : 2 / 3 ≤ t) (x : ℝ) :
    lineIsotopy f t x = f x := by
  rw [lineIsotopy, Real.smoothTransition.one_of_one_le (by linarith)]
  exact lineInterpolation_one f x

/-- Every real time of the time-cutoff interpolation is a diffeomorphism;
Smale's Theorem 4, p. 624. -/
theorem lineIsotopy_diffeomorph {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hpos : ∀ x, 0 < deriv f x)
    (a b : ℝ) (hfix : ∀ x, x ≤ a ∨ b ≤ x → f x = x) (t : ℝ) :
    ∃ g : ℝ ≃ₘ[ℝ] ℝ, ∀ x, g x = lineIsotopy f t x := by
  exact ⟨lineInterpolationDiffeomorph hf hpos a b hfix
    (Real.smoothTransition (3 * t - 1))
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun _ => rfl⟩

end Poincare.Manifold.Schoenflies.Plane
