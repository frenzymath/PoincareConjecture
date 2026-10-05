import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.VectorUniqueness

/-!
# Equality of periodic parabolic vector fields

The difference of two fields satisfies the proved zero-data comparison.
MT2007 Claim 19.1, p. 437;
`2026-09-21-periodic-vector-equality.md`.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M63

/-- A scalar parabolic coefficient and lower term give an explicit
difference-error bound from their Lipschitz estimates. MT2007 Claim
19.1, p. 437; `2026-09-21-uniqueness-graph-comparison-components.md`,
section 1. Only the second field's acceleration needs a norm bound. -/
theorem norm_parabolic_difference_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u₁ u₂ p₁ p₂ q₁ q₂ v₁ v₂ B₁ B₂ : E} {A₁ A₂ L R : ℝ}
    (hL : 0 ≤ L) (_hR : 0 ≤ R)
    (hv₁ : v₁ = A₁ • q₁ + B₁) (hv₂ : v₂ = A₂ • q₂ + B₂)
    (hA : |A₁ - A₂| ≤ L * (‖u₁ - u₂‖ + ‖p₁ - p₂‖))
    (hB : ‖B₁ - B₂‖ ≤ L * (‖u₁ - u₂‖ + ‖p₁ - p₂‖))
    (hq₂ : ‖q₂‖ ≤ R) :
    ‖(v₁ - v₂) - A₁ • (q₁ - q₂)‖ ≤
      (L * R + L) * (‖u₁ - u₂‖ + ‖p₁ - p₂‖) := by
  have heq : (v₁ - v₂) - A₁ • (q₁ - q₂) =
      (A₁ - A₂) • q₂ + (B₁ - B₂) := by
    rw [hv₁, hv₂, smul_sub, sub_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖(A₁ - A₂) • q₂‖ + ‖B₁ - B₂‖ := norm_add_le _ _
    _ = |A₁ - A₂| * ‖q₂‖ + ‖B₁ - B₂‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ (L * (‖u₁ - u₂‖ + ‖p₁ - p₂‖)) * R +
        L * (‖u₁ - u₂‖ + ‖p₁ - p₂‖) :=
      add_le_add (mul_le_mul hA hq₂ (norm_nonneg _) (by positivity)) hB
    _ = _ := by ring

/-- Two periodic vector fields with the same initial values agree when
their literal difference satisfies the parabolic error bound. Every
derivative is witnessed only in the open time slab; closed endpoints
follow by continuity. MT2007 Claim 19.1, p. 437; equality derivation. -/
theorem periodic_vector_eq_of_parabolic_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w₁ w₂ wx₁ wx₂ wxx₁ wxx₂ wt₁ wt₂ : ℝ → ℝ → E}
    {A : ℝ → ℝ → ℝ} {p a b alpha C : ℝ}
    (hp : 0 < p) (hab : a < b) (halpha : 0 < alpha) (hC : 0 ≤ C)
    (hw₁ : ContinuousOn (Function.uncurry w₁) (univ ×ˢ Icc a b))
    (hw₂ : ContinuousOn (Function.uncurry w₂) (univ ×ˢ Icc a b))
    (hper₁ : ∀ t ∈ Icc a b, Function.Periodic (fun x => w₁ x t) p)
    (hper₂ : ∀ t ∈ Icc a b, Function.Periodic (fun x => w₂ x t) p)
    (hx₁ : ∀ x t, t ∈ Ioo a b → HasDerivAt (fun y => w₁ y t) (wx₁ x t) x)
    (hx₂ : ∀ x t, t ∈ Ioo a b → HasDerivAt (fun y => w₂ y t) (wx₂ x t) x)
    (hxx₁ : ∀ x t, t ∈ Ioo a b → HasDerivAt (fun y => wx₁ y t) (wxx₁ x t) x)
    (hxx₂ : ∀ x t, t ∈ Ioo a b → HasDerivAt (fun y => wx₂ y t) (wxx₂ x t) x)
    (htime₁ : ∀ x t, t ∈ Ioo a b → HasDerivAt (w₁ x) (wt₁ x t) t)
    (htime₂ : ∀ x t, t ∈ Ioo a b → HasDerivAt (w₂ x) (wt₂ x t) t)
    (hA : ∀ x t, t ∈ Ioo a b → alpha ≤ A x t)
    (herror : ∀ x t, t ∈ Ioo a b →
      ‖(wt₁ x t - wt₂ x t) - A x t • (wxx₁ x t - wxx₂ x t)‖ ≤
        C * (‖w₁ x t - w₂ x t‖ + ‖wx₁ x t - wx₂ x t‖))
    (hinit : ∀ x, w₁ x a = w₂ x a) :
    ∀ x t, t ∈ Icc a b → w₁ x t = w₂ x t := by
  have hzero := periodic_vector_eq_zero_of_parabolic_bound
    (w := fun x t => w₁ x t - w₂ x t)
    (wx := fun x t => wx₁ x t - wx₂ x t)
    (wxx := fun x t => wxx₁ x t - wxx₂ x t)
    (wt := fun x t => wt₁ x t - wt₂ x t)
    hp hab halpha hC (hw₁.sub hw₂)
    (fun t ht => (hper₁ t ht).sub (hper₂ t ht))
    (fun x t ht => (hx₁ x t ht).sub (hx₂ x t ht))
    (fun x t ht => (hxx₁ x t ht).sub (hxx₂ x t ht))
    (fun x t ht => (htime₁ x t ht).sub (htime₂ x t ht))
    hA herror (fun x => sub_eq_zero.mpr (hinit x))
  exact fun x t ht => sub_eq_zero.mp (hzero x t ht)

end PoincareMT.M63
