import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Gluing.MetricJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.OpenSlices
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.GeneralizedSliceCarrier

variable (S : GeneralizedSliceCarrier.{u}) (U : Opens S.carrier)

theorem openSubset_chart_target (q : U) :
    (extChartAt (𝓡 3) q).target ⊆ (extChartAt (𝓡 3) (q : S.carrier)).target := by
  intro z hz
  exact ⟨hz.1, (chartAt (EuclideanSpace ℝ (Fin 3)) (q : S.carrier)).subtypeRestr_target_subset
    ⟨q⟩ hz.2⟩

theorem openSubset_chart_inverse (q : U) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    (extChartAt (𝓡 3) (q : S.carrier)).symm z =
      ((extChartAt (𝓡 3) q).symm z : S.carrier) :=
  (chartAt (EuclideanSpace ℝ (Fin 3)) (q : S.carrier)).subtypeRestr_symm_eqOn ⟨q⟩ hz.2

theorem openSubset_chart_mfderiv (q : U) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q : S.carrier)).symm z =
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z := by
  have hnear : (fun y => (extChartAt (𝓡 3) (q : S.carrier)).symm y) =ᶠ[𝓝 z]
      (fun y => ((extChartAt (𝓡 3) q).symm y : S.carrier)) :=
    Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target q).mem_nhds hz)
      (fun _ hy => S.openSubset_chart_inverse U q hy)
  have hdiff := mfderiv_comp z
    (Poincare.Geometry.Manifold.RegularLevel.hasMFDerivAt_opens_subtypeVal
      (I := 𝓡 3) U ((extChartAt (𝓡 3) q).symm z)).mdifferentiableAt
    (((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hz)).mdifferentiableAt (by simp))
  rw [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal] at hdiff
  rw [hnear.mfderiv_eq]
  ext v
  exact congrArg (fun A => A v) hdiff

theorem openSubset_metricCoefficient (g : RiemannianMetric 3 S.carrier)
    (q : U) (a b : Fin 3) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    singularMetricCoefficient (S.openSubsetMetric U g) q a b z =
      singularMetricCoefficient g (q : S.carrier) a b z := by
  dsimp only [singularMetricCoefficient, singularTensorCoefficient]
  rw [openSubsetMetric_inner,
    Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
  change g.inner ((extChartAt (𝓡 3) q).symm z : S.carrier)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z _)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm z _) =
    g.inner ((extChartAt (𝓡 3) (q : S.carrier)).symm z)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q : S.carrier)).symm z _)
      (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) (q : S.carrier)).symm z _)
  rw [S.openSubset_chart_inverse U q hz, S.openSubset_chart_mfderiv U q hz]
  rfl

theorem openSubset_metricJets (g : RiemannianMetric 3 S.carrier)
    (q : U) (k : ℕ) (a b : Fin 3) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    iteratedFDeriv ℝ k (singularMetricCoefficient (S.openSubsetMetric U g) q a b) z =
      iteratedFDeriv ℝ k (singularMetricCoefficient g (q : S.carrier) a b) z := by
  have hnear := Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target q).mem_nhds hz)
    (fun w hw => S.openSubset_metricCoefficient U g q a b hw)
  exact (hnear.iteratedFDeriv ℝ k).self_of_nhds

theorem openSubset_surgeryCoefficient {B : GeneralizedSliceCarrier.{u}}
    (g : RiemannianMetric 3 B.carrier) (f : S.carrier → B.carrier)
    (q : U) (a b : Fin 3) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    surgeryMetricCoefficient g (fun w => f ((extChartAt (𝓡 3) q).symm w)) a b z =
      surgeryMetricCoefficient g (fun w => f ((extChartAt (𝓡 3) (q : S.carrier)).symm w))
        a b z := by
  have hnear : (fun w => f ((extChartAt (𝓡 3) q).symm w)) =ᶠ[𝓝 z]
      (fun w => f ((extChartAt (𝓡 3) (q : S.carrier)).symm w)) := by
    filter_upwards [(isOpen_extChartAt_target q).mem_nhds hz] with w hw
    rw [S.openSubset_chart_inverse U q hw]
  simp only [surgeryMetricCoefficient, hnear.mfderiv_eq]
  rw [S.openSubset_chart_inverse U q hz]

theorem openSubset_surgeryJets {B : GeneralizedSliceCarrier.{u}}
    (g : RiemannianMetric 3 B.carrier) (f : S.carrier → B.carrier)
    (q : U) (k : ℕ) (a b : Fin 3) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    iteratedFDeriv ℝ k
      (surgeryMetricCoefficient g (fun w => f ((extChartAt (𝓡 3) q).symm w)) a b) z =
    iteratedFDeriv ℝ k
      (surgeryMetricCoefficient g
        (fun w => f ((extChartAt (𝓡 3) (q : S.carrier)).symm w)) a b) z := by
  have hnear := Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target q).mem_nhds hz)
    (fun w hw => S.openSubset_surgeryCoefficient U g f q a b hw)
  exact (hnear.iteratedFDeriv ℝ k).self_of_nhds

end PoincareConjecture.GeneralizedSliceCarrier

namespace PoincareConjecture

theorem SurgeryMetricLimitOn.openSubset
    {A B : GeneralizedSliceCarrier.{u}}
    {g : ℝ → RiemannianMetric 3 A.carrier} {gT : RiemannianMetric 3 B.carrier}
    {f : A.carrier → B.carrier} {U : Set A.carrier} {T : ℝ}
    (h : SurgeryMetricLimitOn A B g gT f U T)
    (V : Opens A.carrier) (hVU : (V : Set A.carrier) ⊆ U) :
    SurgeryMetricLimitOn (A.openSubset V) B (fun t => A.openSubsetMetric V (g t)) gT
      (fun x => f x.val) univ T := by
  intro q _ C hC hCt _ k a b ε hε
  have hsub : (extChartAt (𝓡 3) q.val).symm '' C ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    rw [A.openSubset_chart_inverse V q (hCt hz)]
    exact hVU ((extChartAt (𝓡 3) q).symm z).property
  obtain ⟨d, hd, hbound⟩ := h q.val (hVU q.property) C hC
    (hCt.trans (A.openSubset_chart_target V q)) hsub k a b ε hε
  refine ⟨d, hd, ?_⟩
  intro t htd htT z hz
  rw [A.openSubset_metricJets V (g t) q k a b (hCt hz),
    A.openSubset_surgeryJets V gT f q k a b (hCt hz)]
  exact hbound t htd htT z hz

end PoincareConjecture
