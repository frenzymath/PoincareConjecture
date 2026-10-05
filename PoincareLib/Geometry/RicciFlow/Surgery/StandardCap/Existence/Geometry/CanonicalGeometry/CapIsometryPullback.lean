import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.CanonicalGeometry.StrongNeckLocality
import PoincareLib.Geometry.Riemannian.Homothety.Basic
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Cap

/-!
# Exact neck pullbacks through an actual metric isometry

The genuine manifold chain rule identifies the two normalized tensors
on the whole open cylinder. Locality retains every finite derivative
and the same strict witness. Source: Definition 9.72, pp. 230-231,
and Theorem 12.28, pp. 323-324; cap-isometry-and-ordinary-transfer.md.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.RoundCylinderClose

/-- Exact equality on the tested open cylinder preserves the actual
static comparison and its original strict witness (Definition 9.72). -/
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

end PoincareMT.RoundCylinderClose

namespace PoincareMT.EpsilonNeck

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}

/-- The actual composed coordinate retains the complete normalized
cylinder comparison under a genuine global isometry (Definition 9.72). -/
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

end PoincareMT.EpsilonNeck
