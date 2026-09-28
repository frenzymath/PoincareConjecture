import PoincareConjecture.Proofs.M62.Lemma0_1_Speed
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Set.Icc a b)) (c : ℝ → ℝ → M)

theorem spatial_velocity_contMDiff (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    ContMDiff (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) 1
      (fun x ↦ (⟨c x t, curveVelocity (fun y ↦ c y t) x⟩ :
        TangentBundle (𝓡 n) M)) := by
  have hone : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)).tangent 1
      (fun x : ℝ ↦ (⟨x, 1⟩ : TangentBundle (𝓘(ℝ, ℝ)) ℝ)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    exact contDiff_const
  exact ((hc.spatial_regular t ht).contMDiff_tangentMap (m := 1) (by norm_num)).comp hone

theorem speed_contDiff (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) : ContDiff ℝ 1 (curveSpeed F c t) := by
  have hX := spatial_velocity_contMDiff F c hc ht
  have hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 (fun x ↦ c x t) :=
    (hc.spatial_regular t ht).of_le (by norm_num)
  have hpair : ContMDiff (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) 1
      (fun x ↦ Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (c x t)
        ((F.metric t).inner (c x t) (curveVelocity (fun y ↦ c y t) x)
          (curveVelocity (fun y ↦ c y t) x))) :=
    (((F.metric t).contMDiff.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).comp hγ).clm_bundle_apply₂
      hX hX
  have hsq : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1
      (fun x ↦ (F.metric t).inner (c x t) (curveVelocity (fun y ↦ c y t) x)
        (curveVelocity (fun y ↦ c y t) x)) := by
    intro x
    exact (Bundle.contMDiffAt_totalSpace.mp (hpair x)).2
  exact hsq.contDiff.sqrt fun x ↦ ((F.metric t).pos _ _ (hc.immersed t ht x)).ne'

theorem unitTangent_contMDiff (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    ContMDiff (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) 1
      (fun x ↦ (⟨c x t, spatialUnitTangent F c t x⟩ : TangentBundle (𝓡 n) M)) := by
  have hX := spatial_velocity_contMDiff F c hc ht
  have hv : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) 1
      (fun x ↦ (curveSpeed F c t x)⁻¹) :=
    ((speed_contDiff F c hc ht).inv (fun x ↦ (speed_pos F c hc ht x).ne')).contMDiff
  intro x
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨((hc.spatial_regular t ht).of_le (by norm_num) x), ?_⟩
  have hcoord := (hv x).smul (Bundle.contMDiffAt_totalSpace.mp (hX x)).2
  apply hcoord.congr_of_eventuallyEq
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (c x t)
  have hnear : ∀ᶠ y in 𝓝 x, c y t ∈ e.baseSet :=
    (hc.spatial_regular t ht).continuous.continuousAt
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (c x t)))
  filter_upwards [hnear] with y hy
  change (e ⟨c y t, (curveSpeed F c t y)⁻¹ • curveVelocity (fun z ↦ c z t) y⟩).2 =
    (curveSpeed F c t y)⁻¹ • (e ⟨c y t, curveVelocity (fun z ↦ c z t) y⟩).2
  simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hy] using
    (e.continuousLinearMapAt ℝ (c y t)).map_smul
      (curveSpeed F c t y)⁻¹ (curveVelocity (fun z ↦ c z t) y)

theorem curvature_unitTangent_inner_zero (hc : M62ShrinkingCurve F c) {t : ℝ}
    (ht : t ∈ Set.Icc a b) (x : ℝ) :
    (F.metric t).inner (c x t) (m62CurvatureVector F c t x)
      (spatialUnitTangent F c t x) = 0 := by
  have hS := (unitTangent_contMDiff F c hc ht x).mdifferentiableAt (by simp)
  have hpair := hasDerivAt_metric_pairing (F.connection t)
    ((hc.spatial_regular t ht x).mdifferentiableAt (by norm_num)) hS hS
  have hconst : (fun y ↦ (F.metric t).inner (c y t) (spatialUnitTangent F c t y)
      (spatialUnitTangent F c t y)) = fun _ : ℝ ↦ (1 : ℝ) :=
    funext (unitTangent_inner_self F c hc ht)
  rw [hconst] at hpair
  have heq := hpair.unique (hasDerivAt_const x (1 : ℝ))
  have hz : (F.metric t).inner (c x t)
      (rampHorizontalCovariantDerivative (F.connection t) (fun y ↦ c y t)
        (spatialUnitTangent F c t) x) (spatialUnitTangent F c t x) = 0 := by
    rw [(F.metric t).symm (c x t) (spatialUnitTangent F c t x)] at heq
    linarith
  simp only [m62CurvatureVector, m62SpatialDerivative, map_smul, smul_apply,
    smul_eq_mul, hz, mul_zero]

end PoincareConjecture.M62
