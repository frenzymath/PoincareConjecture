import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalDiffeomorph










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M51

variable {A B : GeneralizedSliceCarrier.{u}}


theorem singularMetricCoefficient_pullback
    (gT : RiemannianMetric 3 B.carrier)
    (f : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (q : A.carrier) (a b : Fin 3)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    singularMetricCoefficient (gT.pullbackOfLocalDiffeomorph f f.isLocalDiffeomorph)
      q a b p =
    surgeryMetricCoefficient gT (fun z => f ((extChartAt (𝓡 3) q).symm z)) a b p := by
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hp)
  have hcomp := mfderiv_comp p (f.mdifferentiable (by simp) _)
    (hc.mdifferentiableAt (by simp))
  simp only [singularMetricCoefficient, singularTensorCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    RiemannianMetric.pullbackOfLocalDiffeomorph_inner, surgeryMetricCoefficient]
  rw [show (fun z => f ((extChartAt (𝓡 3) q).symm z)) =
    f ∘ (extChartAt (𝓡 3) q).symm from rfl, hcomp]
  rfl


theorem singularMetricJet_pullback
    (gT : RiemannianMetric 3 B.carrier)
    (f : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (q : A.carrier) (a b : Fin 3) (k : ℕ)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    iteratedFDeriv ℝ k
      (singularMetricCoefficient (gT.pullbackOfLocalDiffeomorph f f.isLocalDiffeomorph)
        q a b) p =
    iteratedFDeriv ℝ k
      (surgeryMetricCoefficient gT (fun z => f ((extChartAt (𝓡 3) q).symm z)) a b) p := by
  have heq : singularMetricCoefficient
      (gT.pullbackOfLocalDiffeomorph f f.isLocalDiffeomorph) q a b =ᶠ[𝓝 p]
      surgeryMetricCoefficient gT (fun z => f ((extChartAt (𝓡 3) q).symm z)) a b := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hp] with z hz
    exact singularMetricCoefficient_pullback gT f q a b hz
  exact heq.iteratedFDeriv ℝ k |>.eq_of_nhds



theorem surgeryMetricLimitOn_pullback
    (g : ℝ → RiemannianMetric 3 A.carrier)
    (gT : RiemannianMetric 3 B.carrier)
    (f : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    {U : Set A.carrier} {T : ℝ}
    (hlim : SurgeryMetricLimitOn A B g gT f U T) :
    SurgeryMetricLimitOn A A g
      (gT.pullbackOfLocalDiffeomorph f f.isLocalDiffeomorph) id U T := by
  intro q hq K hK htarget hU k a b eta heta
  obtain ⟨d, hd, hbound⟩ := hlim q hq K hK htarget hU k a b eta heta
  refine ⟨d, hd, fun t ht hT p hp => ?_⟩
  have hjet := singularMetricJet_pullback gT f q a b k (htarget hp)
  have hcoeff : surgeryMetricCoefficient
      (gT.pullbackOfLocalDiffeomorph f f.isLocalDiffeomorph)
      (fun z => id ((extChartAt (𝓡 3) q).symm z)) a b =
      singularMetricCoefficient
        (gT.pullbackOfLocalDiffeomorph f f.isLocalDiffeomorph) q a b := rfl
  rw [hcoeff, hjet]
  exact hbound t ht hT p hp

end PoincareConjecture.M51
