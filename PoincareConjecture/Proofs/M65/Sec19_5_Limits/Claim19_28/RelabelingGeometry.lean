import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.RelabelingConnection
import PoincareConjecture.Proofs.M62.Lemma19_6_Orthogonality
import PoincareConjecture.Definitions.M63Ramp








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}



theorem m65UnitTangent_fixed_relabeling (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {phi : ℝ → ℝ} {t x d : ℝ}
    (hphi : HasDerivAt phi d x) (hd : 0 < d) (ht : t ∈ Icc a b) :
    spatialUnitTangent F (fun y r => c (phi y) r) t x =
      spatialUnitTangent F c t (phi x) := by
  unfold spatialUnitTangent
  rw [m65CurveSpeed_fixed_relabeling c hc hphi hd ht]
  have hvelocity := m65CurveVelocity_comp
    ((hc.spatial_regular t ht (phi x)).mdifferentiableAt (by norm_num)) hphi
  change curveVelocity (n := n) (fun y => c (phi y) t) x = _ at hvelocity
  rw [hvelocity, smul_smul]
  congr 1
  field_simp



theorem m65SpatialDerivative_fixed_relabeling (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {phi : ℝ → ℝ} {t x d : ℝ}
    {Y : ∀ y, TangentSpace (𝓡 n) (c y t)}
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n))
      (fun y => (⟨c y t, Y y⟩ : TangentBundle (𝓡 n) M)) (phi x))
    (hphi : HasDerivAt phi d x) (hd : 0 < d) (ht : t ∈ Icc a b) :
    m62SpatialDerivative F (fun y r => c (phi y) r) t (fun y => Y (phi y)) x =
      m62SpatialDerivative F c t Y (phi x) := by
  unfold m62SpatialDerivative
  rw [m65CurveSpeed_fixed_relabeling c hc hphi hd ht]
  have hpull := m65Pullback_fixed_relabeling (F.connection t) hY hphi
  change rampHorizontalCovariantDerivative (F.connection t)
    (fun y => c (phi y) t) (fun y => Y (phi y)) x = _ at hpull
  rw [hpull, smul_smul]
  congr 1
  field_simp



theorem m65CurvatureVector_fixed_relabeling (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi) (hpos : ∀ x, 0 < deriv phi x)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    m62CurvatureVector F (fun y r => c (phi y) r) t x =
      m62CurvatureVector F c t (phi x) := by
  have hunit : spatialUnitTangent F (fun y r => c (phi y) r) t =
      fun y => spatialUnitTangent F c t (phi y) := by
    funext y
    exact m65UnitTangent_fixed_relabeling c hc (hphi y).hasDerivAt (hpos y) ht
  unfold m62CurvatureVector
  rw [hunit]
  exact m65SpatialDerivative_fixed_relabeling c hc
    ((M62.unitTangent_contMDiff F c hc ht (phi x)).mdifferentiableAt (by simp))
    (hphi x).hasDerivAt (hpos x) ht




theorem m65CurvatureJet_fixed_relabeling (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi) (hpos : ∀ x, 0 < deriv phi x)
    {t : ℝ} (ht : t ∈ Icc a b)
    (hjets : ∀ i y, MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 n).prod (𝓡 n))
      (fun r => (⟨c r t, m63CurvatureJet F c i t r⟩ : TangentBundle (𝓡 n) M)) y)
    (i : ℕ) (x : ℝ) :
    m63CurvatureJet F (fun y r => c (phi y) r) i t x =
      m63CurvatureJet F c i t (phi x) := by
  induction i generalizing x with
  | zero => exact m65CurvatureVector_fixed_relabeling c hc hphi hpos ht x
  | succ i ih =>
    change m62SpatialDerivative F (fun y r => c (phi y) r) t
      (fun y => m63CurvatureJet F (fun r s => c (phi r) s) i t y) x = _
    have heq : (fun y => m63CurvatureJet F (fun r s => c (phi r) s) i t y) =
        fun y => m63CurvatureJet F c i t (phi y) := funext ih
    rw [heq]
    exact m65SpatialDerivative_fixed_relabeling c hc (hjets i (phi x))
      (hphi x).hasDerivAt (hpos x) ht

end PoincareConjecture
