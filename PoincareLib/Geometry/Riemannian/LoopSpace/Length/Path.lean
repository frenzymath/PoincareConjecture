import PoincareLib.Geometry.Riemannian.Metric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Metric speed and length of C1 paths

Adapted from Mapher Proofs/M04/ShiEnergyPaths.lean at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc.
-/

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace PoincareMT.LoopSpace

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The speed of the actual manifold derivative in the supplied metric. -/
noncomputable def pathSpeed (g : RiemannianMetric n M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)

theorem pathSpeed_nonneg (g : RiemannianMetric n M) (γ : ℝ → M) (t : ℝ) :
    0 ≤ pathSpeed g γ t := Real.sqrt_nonneg _

theorem continuous_pathSpeed (g : RiemannianMetric n M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) : Continuous (pathSpeed g γ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hinput : Continuous
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hvelocity : Continuous (fun t : ℝ =>
      (⟨γ t, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1⟩ : TangentBundle (𝓡 n) M)) :=
    (hγ.continuous_tangentMap le_rfl).comp hinput
  exact (hvelocity.inner_bundle hvelocity).sqrt

theorem pathELength_eq_ofReal_integral_pathSpeed
    (g : RiemannianMetric n M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 γ) {a b : ℝ} (hab : a ≤ b) :
    g.pathELength γ a b = ENNReal.ofReal (∫ t in a..b, pathSpeed g γ t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 n) γ a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hnorm (t : ℝ) : ‖mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1‖ₑ =
      ENNReal.ofReal (pathSpeed g γ t) := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  simp_rw [hnorm]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (continuous_pathSpeed g hγ).continuousOn.integrableOn_Icc
    (Eventually.of_forall (pathSpeed_nonneg g γ))).symm

end PoincareMT.LoopSpace
