import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckLocality
import PoincareConjecture.Definitions.M13MetricHomothety
import PoincareConjecture.Definitions.Ch09.NeckCapTopology










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.RoundCylinderClose



theorem congr_cylinder {epsilon u : ℝ} {B D : RoundCylinderTwoTensor}
    (hB : RoundCylinderClose epsilon u B)
    (hBD : ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w : RoundCylinderTangent z, B z v w = D z v w) :
    RoundCylinderClose epsilon u D := by
  obtain ⟨hs, b, hb, hbound⟩ := hB
  refine ⟨hs.congr_cylinder hBD, b, hb, ?_⟩
  intro z hz
  rw [← M34.roundCylinderJetErrorSquared_eq_of_eqOn_cylinder hBD u _ hz]
  exact hbound z hz

end PoincareConjecture.RoundCylinderClose

namespace PoincareConjecture.EpsilonNeck

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}



theorem metricIsometry_comparison (N : EpsilonNeck g)
    (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞) (hf : MetricHomothety g h f 1) :
    RoundCylinderClose N.epsilon 0 (fun z v w => N.scale⁻¹ ^ 2 *
      roundCylinderPullback h (f ∘ N.coordinate_map) z v w) := by
  apply N.metric_comparison.close.congr_cylinder
  intro z hz v w
  have hNd := ((N.coordinate_map_smooth z ⟨mem_univ _, hz⟩).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have hchain := mfderiv_comp z (f.mdifferentiable (by simp) _) hNd
  congr 1
  simp only [roundCylinderPullback, hchain, ContinuousLinearMap.comp_apply, Function.comp_apply]
  simpa only [one_mul] using (hf (N.coordinate_map z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w)).symm

end PoincareConjecture.EpsilonNeck
