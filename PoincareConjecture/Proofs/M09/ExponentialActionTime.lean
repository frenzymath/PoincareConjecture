import PoincareConjecture.Definitions.Ch06.ReducedLength
import PoincareConjecture.Proofs.M09.BackwardActionDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_action_hasDerivAt {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (τ : ℝ) (hτ : 0 < τ) (hmax : τ < τmax) :
    HasDerivAt (fun s ↦ A.action Z s) (backwardLIntegrand F T (A.gamma Z) τ) τ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  let U : Set (E × ℝ) := Set.univ ×ˢ Set.Ioo 0 τmax
  have hγ : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞
      (fun z ↦ A.gamma z.1 z.2) U := by
    convert! A.gamma_smooth using 1 <;>
      simp only [E, modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  have hdensity := backwardFamilyActionDensity_contDiffOn F hM04 T
    (fun z : E × ℝ ↦ A.gamma z.1 z.2) U (isOpen_univ.prod isOpen_Ioo) hγ
    (fun z hz ↦ hz.2.1)
    (fun z hz ↦ hwindow ⟨by linarith [hz.2.2], by linarith [hz.2.1]⟩)
  have hcontinuous : ContinuousOn (backwardLIntegrand F T (A.gamma Z)) (Set.Ioo 0 τmax) :=
    hdensity.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs ↦ ⟨Set.mem_univ _, hs⟩)
  have hintegrable : IntervalIntegrable (backwardLIntegrand F T (A.gamma Z))
      MeasureTheory.volume 0 τ := by
    have h := (A.path Z τ hτ hmax).l_integrable
    rw [A.path_eq] at h
    exact h
  exact intervalIntegral.integral_hasDerivAt_right hintegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcontinuous τ ⟨hτ, hmax⟩)
    (hcontinuous.continuousAt (isOpen_Ioo.mem_nhds ⟨hτ, hmax⟩))

end PoincareConjecture.Proofs.M09
