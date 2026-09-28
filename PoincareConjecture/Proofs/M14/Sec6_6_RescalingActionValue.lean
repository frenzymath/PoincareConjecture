import PoincareConjecture.Proofs.M14.Sec6_6_RescalingPathInverse
import Mathlib.Order.ConditionallyCompleteLattice.Indexed









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)



theorem rescalingActionSet (T τ₁ τ₂ : ℝ) (x y : G.Point) :
    M14ActionSet (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y =
      (fun r => Real.sqrt Q * r) '' M14ActionSet G T τ₁ τ₂ x y := by
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    let q := rescalingPathInverse hM12 hM13 G Q hQ a p
    refine ⟨M14BackwardLAction G q, ⟨q, rfl⟩, ?_⟩
    have h := rescalingPath_action hM12 hM13 G Q hQ a q
    rw [rescalingPath_right_inverse] at h
    exact h.symm
  · rintro ⟨r, ⟨p, rfl⟩, rfl⟩
    exact ⟨rescalingPath hM12 hM13 G Q hQ a p,
      rescalingPath_action hM12 hM13 G Q hQ a p⟩



theorem rescalingFiniteValue {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (h : M14FiniteValueDomain G T τ₁ τ₂ x y) :
    M14FiniteValueDomain (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y := by
  unfold M14FiniteValueDomain
  rw [rescalingActionSet]
  refine ⟨h.1.image _, ?_⟩
  obtain ⟨c, hc⟩ := h.2
  refine ⟨Real.sqrt Q * c, ?_⟩
  rintro r ⟨z, hz, rfl⟩
  exact mul_le_mul_of_nonneg_left (hc hz) (Real.sqrt_nonneg Q)



theorem rescalingActionValue {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (h : M14FiniteValueDomain G T τ₁ τ₂ x y) :
    M14ActionValue (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y =
      Real.sqrt Q * M14ActionValue G T τ₁ τ₂ x y := by
  unfold M14ActionValue
  rw [rescalingActionSet]
  exact ((OrderIso.mulLeft₀ (Real.sqrt Q) (Real.sqrt_pos.mpr hQ)).map_csInf' h.1 h.2).symm



theorem rescalingReducedLength {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (hτ₂ : 0 < τ₂) (h : M14FiniteValueDomain G T τ₁ τ₂ x y) :
    M14ReducedLengthValue (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y =
      M14ReducedLengthValue G T τ₁ τ₂ x y := by
  unfold M14ReducedLengthValue
  rw [rescalingActionValue hM12 hM13 G Q hQ a h, Real.sqrt_mul hQ.le]
  field_simp [(Real.sqrt_pos.mpr hQ).ne', (Real.sqrt_pos.mpr hτ₂).ne']



noncomputable def rescalingDensity (G : GeneralizedLGeometryTransport n X time I)
    (T τ : ℝ) (x q : G.Point) : ℝ :=
  Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-M14ReducedLengthValue G T 0 τ x q)



theorem rescalingDensity_scale {T τ : ℝ} {x q : G.Point}
    (hτ : 0 < τ) (h : M14FiniteValueDomain G T 0 τ x q) :
    rescalingDensity (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ) x q =
      Real.rpow Q (-(n : ℝ) / 2) * rescalingDensity G T τ x q := by
  have hl := rescalingReducedLength hM12 hM13 G Q hQ a hτ h
  rw [mul_zero] at hl
  unfold rescalingDensity
  rw [hl]
  change (Q * τ) ^ (-(n : ℝ) / 2) * Real.exp
      (-M14ReducedLengthValue G T 0 τ x q) = _
  rw [Real.mul_rpow hQ.le hτ.le]
  simp only [div_eq_mul_inv, neg_mul]
  ac_rfl

end PoincareConjecture.M14
