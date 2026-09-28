import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Splitting.TimeTransport.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {a b : ℝ}

theorem contMDiffOn_scalarCurvature_surface_Icc (hab : a < b)
    (F : RicciFlow 2 M (Icc a b)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2)
      (Icc a b ×ˢ univ) := by
  rintro ⟨t, x⟩ ⟨ht, _⟩
  let v : TangentSpace (𝓡 2) x := EuclideanSpace.basisFun (Fin 2) ℝ 0
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin 2)) v
  have hX : ContMDiffAt (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) ∞
      (T% X) x := FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 2) _ v
  have hRic := Splitting.contMDiffWithinAt_ricci_fields hab F ht hX hX
  have hmetric := F.contMDiffWithinAt_inner_fields ht hX hX
  have hpos : 0 < (F.metric t).inner x (X x) (X x) := by
    simp only [X, FiberBundle.extend_apply_self]
    exact (F.metric t).pos x v ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ne_zero 0)
  have hquot := ((contMDiffWithinAt_const (c := (2 : ℝ))).mul hRic).div₀
    hmetric (ne_of_gt hpos)
  apply hquot.congr_of_eventuallyEq_of_mem
    (hx := show (t, x) ∈ Icc a b ×ˢ (univ : Set M) from ⟨ht, mem_univ _⟩)
  filter_upwards [hmetric.continuousWithinAt.eventually (eventually_ne_nhds (ne_of_gt hpos))]
    with p hp
  simp only [Pi.div_apply, Pi.mul_apply]
  rw [(F.connection p.1).ricci_eq_half_scalarCurvature_mul_inner]
  field_simp [hp]

theorem continuousOn_scalarCurvature_surface_Icc_swap (hab : a < b)
    (F : RicciFlow 2 M (Icc a b)) :
    ContinuousOn (fun z : M × ℝ => (F.connection z.2).scalarCurvature z.1)
      (univ ×ˢ Icc a b) := by
  intro z hz
  have hc := (contMDiffOn_scalarCurvature_surface_Icc hab F
    (z.2, z.1) ⟨hz.2, hz.1⟩).continuousWithinAt
  exact hc.comp (f := Prod.swap) (x := z) (continuous_swap.continuousAt.continuousWithinAt)
    (fun z hz => ⟨hz.2, hz.1⟩)

end PoincareConjecture.RicciFlow
