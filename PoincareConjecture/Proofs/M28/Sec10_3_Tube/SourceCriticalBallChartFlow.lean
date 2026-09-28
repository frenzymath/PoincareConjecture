import PoincareConjecture.Proofs.M28.Generalized.StrongNeckChartFlow
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeCriticalRegion
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.ChartMaps











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}
  (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
  (A1 : ℝ) (k : ℕ) (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
  [Nonempty U] (e : U → H.tubeCriticalRegion T A1 k)
  (he : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e)

include he in


theorem tubeCritical_chart_original_localDiffeomorph :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => (e x).val.val) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro x
  exact ((he x).comp (𝓡 3) (T k).carrierOpen
    (openSubtype_isLocalDiffeomorph (H.tubeCriticalRegion T A1 k) (e x))).comp
      (𝓡 3) ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier
      (openSubtype_isLocalDiffeomorph (T k).carrierOpen (e x).val)

variable (S : GeneralizedStrongNeck (E (k + H.shift)).flow
    (E (k + H.shift)).time epsilon)
  (R : RescaledRawCylinderData (C := (E (k + H.shift)).flow.slice
      (E (k + H.shift)).time)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
  (hcapture : ∀ x : U, (e x).val.val ∈ S.carrier)
  (tau : ℝ) (htau : 0 < tau)
  (hwindow : tau ≤ (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ * S.scale ^ 2 / 4)



def tubeCritical_chart_flow :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    RicciFlow 3 U (Icc (-tau) 0) :=
  GeneralizedStrongNeck.global_chart_flow S R
    ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩)
    (H.base_scalar_pos k) tau htau hwindow U hU (fun x : U => (e x).val.val)
    (H.tubeCritical_chart_original_localDiffeomorph T A1 k U hU e he) hcapture




theorem tubeCritical_chart_flow_metric_at_zero :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      ((H.tubeCritical_chart_flow T A1 k U hU e he S R hcapture
        tau htau hwindow).metric 0).inner x v w =
        (H.tubeCriticalMetric T A1 k).inner (e x)
          (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro x v w
  let i₁ : H.tubeCriticalRegion T A1 k → (T k).carrierOpen := Subtype.val
  let i₂ : (T k).carrierOpen →
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier := Subtype.val
  have h₁ := openSubtype_isLocalDiffeomorph (H.tubeCriticalRegion T A1 k)
  have h₂ := openSubtype_isLocalDiffeomorph (T k).carrierOpen
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (fun y : U => (e y).val.val) x z =
        mfderiv (𝓡 3) (𝓡 3) i₂ (i₁ (e x))
          (mfderiv (𝓡 3) (𝓡 3) i₁ (e x) (mfderiv (𝓡 3) (𝓡 3) e x z)) := by
    have hfirst := mfderiv_comp_apply x ((h₁ (e x)).mdifferentiableAt (by simp))
      ((he x).mdifferentiableAt (by simp)) z
    have hsecond := mfderiv_comp_apply x ((h₂ (i₁ (e x))).mdifferentiableAt (by simp))
      (((he x).comp (𝓡 3) (T k).carrierOpen (h₁ (e x))).mdifferentiableAt (by simp)) z
    exact hsecond.trans (congrArg (mfderiv (𝓡 3) (𝓡 3) i₂ (i₁ (e x))) hfirst)
  change ((GeneralizedStrongNeck.global_chart_flow S R _ _ tau htau hwindow
    U hU _ _ hcapture).metric 0).inner x v w = _
  rw [GeneralizedStrongNeck.global_chart_flow_metric_at_zero, hderiv, hderiv]
  rfl

end PoincareConjecture.M28.CounterexampleNeckFamily
