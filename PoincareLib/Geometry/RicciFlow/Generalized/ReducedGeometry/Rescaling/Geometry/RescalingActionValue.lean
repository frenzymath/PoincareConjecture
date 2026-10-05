import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Paths.RescalingPathInverse
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Action infima, reduced length and density under rescaling

Morgan-Tian Lemma 6.72, p. 141, Corollary 6.74 and Lemma 6.75,
p. 142. The exact competitor correspondence scales the finite action
infimum; absolute-time normalization cancels the square root scale.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

/-- The whole action set is the positive scalar image of the old
competitor action set. Lemma 6.72, p. 141. -/
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

/-- Finite-value domains are preserved by positive rescaling; no
existence of a minimizing path is used. Lemma 6.72, p. 141. -/
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

/-- A nonempty, bounded-below action infimum gains the square root
scale. Lemma 6.72, p. 141. -/
theorem rescalingActionValue {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (h : M14FiniteValueDomain G T τ₁ τ₂ x y) :
    M14ActionValue (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y =
      Real.sqrt Q * M14ActionValue G T τ₁ τ₂ x y := by
  unfold M14ActionValue
  rw [rescalingActionSet]
  exact ((OrderIso.mulLeft₀ (Real.sqrt Q) (Real.sqrt_pos.mpr hQ)).map_csInf' h.1 h.2).symm

/-- Reduced length is invariant under positive parabolic rescaling
at positive absolute terminal time. Corollary 6.74, p. 142. -/
theorem rescalingReducedLength {T τ₁ τ₂ : ℝ} {x y : G.Point}
    (hτ₂ : 0 < τ₂) (h : M14FiniteValueDomain G T τ₁ τ₂ x y) :
    M14ReducedLengthValue (rescalingTransport hM12 hM13 G Q hQ a)
      (parabolicTime Q a T) (Q * τ₁) (Q * τ₂) x y =
      M14ReducedLengthValue G T τ₁ τ₂ x y := by
  unfold M14ReducedLengthValue
  rw [rescalingActionValue hM12 hM13 G Q hQ a h, Real.sqrt_mul hQ.le]
  field_simp [(Real.sqrt_pos.mpr hQ).ne', (Real.sqrt_pos.mpr hτ₂).ne']

/-- The actual scalar reduced-volume density without a `4 pi` factor,
Definition 6.70, p. 140, as used in Lemma 6.75, p. 142. -/
noncomputable def rescalingDensity (G : GeneralizedLGeometryTransport n X time I)
    (T τ : ℝ) (x q : G.Point) : ℝ :=
  Real.rpow τ (-(n : ℝ) / 2) * Real.exp (-M14ReducedLengthValue G T 0 τ x q)

/-- The scalar reduced-volume density has weight minus half the
dimension; its volume factor cancels this weight. Lemma 6.75, p. 142. -/
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

end PoincareMT.M14
