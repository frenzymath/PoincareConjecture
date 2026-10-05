import PoincareLib.Geometry.CurveShortening.Deformation.Limit.Relabeling.Intrinsic
import PoincareLib.Geometry.RicciFlow.CurveShortening.Evolution.NormalizedFields

/-!
# Smooth actual tangent and curvature jet fields

Morgan--Tian Claim 19.28, printed p. 460. A single indexed sequence
starts with the unit tangent and then the actual intrinsic curvature
jets. Every successor is the genuine arc-length covariant derivative.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

/-- The actual unit tangent followed by its covariant derivatives;
Claim 19.28, printed p. 460. -/
noncomputable def m65IntrinsicTangentJet (F : RicciFlow n M (Icc a b))
    (c : ℝ → ℝ → M) : (i : ℕ) → (t x : ℝ) → TangentSpace (𝓡 n) (c x t)
  | 0, t, x => spatialUnitTangent F c t x
  | i + 1, t, x => m63CurvatureJet F c i t x

/-- The indexed actual field satisfies its intrinsic differential
recurrence definitionally; Claim 19.28, printed p. 460. -/
theorem m65IntrinsicTangentJet_succ (c : ℝ → ℝ → M) (i : ℕ) (t x : ℝ) :
    m65IntrinsicTangentJet F c (i + 1) t x =
      m62SpatialDerivative F c t (m65IntrinsicTangentJet F c i t) x := by
  cases i <;> rfl

set_option maxHeartbeats 800000 in
-- Successor elaboration identifies the two dependent recursive field expressions.
/-- A smooth genuine solution has smooth actual curvature jets on the
open original slab; Claim 19.28, printed p. 460. -/
theorem m65CurvatureJet_joint_contMDiff [T2Space M] (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (i : ℕ) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z : ℝ × ℝ => (⟨c z.1 z.2, m63CurvatureJet F c i z.2 z.1⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ Ioo a b) := by
  induction i with
  | zero => exact M62.curvature_joint_contMDiff F c hc
  | succ i ih =>
    exact M62.spatialDerivative_joint_contMDiff F c hc
      (fun z => m63CurvatureJet F c i z.2 z.1) ih

/-- Every actual tangent jet is smooth on the original interior;
Claim 19.28, printed p. 460. -/
theorem m65IntrinsicTangentJet_joint_contMDiff [T2Space M] (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (i : ℕ) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z : ℝ × ℝ => (⟨c z.1 z.2, m65IntrinsicTangentJet F c i z.2 z.1⟩ :
        TangentBundle (𝓡 n) M)) (univ ×ˢ Ioo a b) := by
  cases i with
  | zero => exact M62.unitTangent_joint_contMDiff F c hc
  | succ i => exact m65CurvatureJet_joint_contMDiff c hc i

/-- The primitive supplied regularity already suffices for the first
spatial differential identities; Claim 19.28, printed p. 460. -/
theorem m65IntrinsicTangentJet_spatial_mdiff (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (hreg : M63IntrinsicRegularityOn F c (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (i : ℕ) (x : ℝ) :
    MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun y => (⟨c y t, m65IntrinsicTangentJet F c i t y⟩ :
        TangentBundle (𝓡 n) M)) x := by
  cases i with
  | zero =>
    exact (M62.unitTangent_contMDiff F c hc (Ioo_subset_Icc_self ht) x).mdifferentiableAt
      (by simp)
  | succ i => exact m65IntrinsicRegularity_spatial_mdiff c hreg ht i x

/-- Multiplication by positive speed converts the actual arc-length
recurrence to the actual parameter pullback derivative; Claim 19.28,
printed p. 460. -/
theorem m65IntrinsicTangentJet_pullback (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Icc a b) (i : ℕ) (x : ℝ) :
    rampHorizontalCovariantDerivative (F.connection t) (fun y => c y t)
      (m65IntrinsicTangentJet F c i t) x =
      curveSpeed F c t x • m65IntrinsicTangentJet F c (i + 1) t x := by
  rw [m65IntrinsicTangentJet_succ, m62SpatialDerivative, smul_smul,
    mul_inv_cancel₀ (M62.speed_pos F c hc ht x).ne', one_smul]

end PoincareMT
