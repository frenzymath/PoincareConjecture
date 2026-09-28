import PoincareConjecture.Proofs.M10.CurveCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SurgeryVolume.Measure

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {γ : ℝ → M} {s : ℝ}

set_option backward.isDefEq.respectTransparency false in
omit [IsManifold (𝓡 n) ∞ M] in

theorem hasDerivAt_comp_curve {f : M → ℝ}
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f (γ s))
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s) :
    HasDerivAt (f ∘ γ) (mvfderiv (𝓡 n) f (γ s) (curveVelocity γ s)) s := by
  apply (hf.comp s hγ).differentiableAt.hasDerivAt.congr_deriv
  change (fderiv ℝ (f ∘ γ) s) 1 = _
  rw [← mfderiv_eq_fderiv, mfderiv_comp s hf hγ]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem continuous_tangentNorm_curveVelocity (g : RiemannianMetric n M)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ) :
    Continuous (fun t ↦ g.tangentNorm (γ t) (curveVelocity γ t)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  have hsection : Continuous
      (fun t : ℝ ↦ (⟨t, (1 : ℝ)⟩ : TangentBundle (𝓘(ℝ, ℝ)) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph (𝓘(ℝ, ℝ))).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hv : Continuous (fun t ↦
      (⟨γ t, curveVelocity γ t⟩ : TangentBundle (𝓡 n) M)) :=
    (hγ.continuous_tangentMap le_rfl).comp hsection
  exact Real.continuous_sqrt.comp (hv.inner_bundle hv)

set_option backward.isDefEq.respectTransparency false in

theorem pathELength_eq_ofReal_integral_tangentNorm (g : RiemannianMetric n M)
    (hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ) {a b : ℝ} (hab : a ≤ b) :
    g.pathELength γ a b =
      ENNReal.ofReal (∫ t in a..b, g.tangentNorm (γ t) (curveVelocity γ t)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hspeed := continuous_tangentNorm_curveVelocity g hγ
  have hi := hspeed.continuousOn.integrableOn_compact
    (μ := volume) (K := Set.Icc a b) isCompact_Icc
  delta RiemannianMetric.pathELength
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun _ ↦ Real.sqrt_nonneg _))]
  apply lintegral_congr
  intro t
  rw [← ofReal_norm]
  congr 1

end PoincareConjecture.SurgeryVolume.Measure
