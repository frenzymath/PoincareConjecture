import PoincareConjecture.Proofs.M34.Standard.OrdinaryHorizontalLift
import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryProductGeometry












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

noncomputable section

variable {n : ℕ} {I : SpacetimeInterval}
  {g : ℝ → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

set_option backward.isDefEq.respectTransparency false in


theorem ordinaryProductHorizontalLift_hasDerivAt
    (R : OrdinaryProductSpacetimeConclusion g I) (z : R.spacetime.Point)
    {a : ℝ → EuclideanSpace ℝ (Fin n)} {s : ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (ha : HasDerivAt a v s) :
    HasDerivAt (fun r => ordinaryProductHorizontalLift R z (a r))
      (ordinaryProductHorizontalLift R z v) s := by
  let : NormedAddCommGroup (TangentSpace (spacetimeModel n) z) :=
    inferInstanceAs (NormedAddCommGroup (SpacetimeModelVector n))
  let : NormedSpace ℝ (TangentSpace (spacetimeModel n) z) :=
    inferInstanceAs (NormedSpace ℝ (SpacetimeModelVector n))
  have hd : HasFDerivAt (ordinaryProductHorizontalLift R z)
      (ordinaryProductHorizontalLift R z) (a s) :=
    (ordinaryProductHorizontalLift R z).hasFDerivAt
  exact HasFDerivAt.comp_hasDerivAt (F := EuclideanSpace ℝ (Fin n))
    (E := R.spacetime.Horizontal z) (f := a)
    (l := ordinaryProductHorizontalLift R z) (l' := ordinaryProductHorizontalLift R z) s hd ha

set_option backward.isDefEq.respectTransparency false in



noncomputable def ordinaryModelHorizontalExtension
    (R : OrdinaryProductRicciGeometry g I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    (gamma : ℝ → (ordinaryProductLGeometry R hRicci).Point)
    (a : ℝ → EuclideanSpace ℝ (Fin n)) (K O : Set ℝ)
    (hO : IsOpen O) (hKO : K ⊆ O) (ha : ContDiffOn ℝ ∞ a O) :
    M14PullbackExtension (ordinaryProductLGeometry R hRicci) gamma K
      (fun s => ordinaryProductHorizontalLift R.product (gamma s) (a s)) where
  extension := fun r z => ordinaryProductHorizontalLift R.product z (a r)
  domain := univ
  domain_open := isOpen_univ
  graph_mem := fun _ _ => mem_univ _
  spatial_smooth := fun r => ordinaryProductHorizontalLift_smooth R.product (a r)
  joint_smooth := by
    refine ⟨O ×ˢ univ, hO.prod isOpen_univ, fun s hs => ⟨hKO hs, mem_univ _⟩, ?_⟩
    exact ordinaryProductHorizontalLift_contMDiffOn R.product contMDiffOn_snd
      (ha.contMDiffOn.comp contMDiffOn_fst (fun _ hs => hs.1))
  agrees := fun _ _ => rfl
  parameter_derivative := by
    intro s hs
    refine ⟨ordinaryProductHorizontalLift R.product (gamma s) (deriv a s), ?_⟩
    exact ordinaryProductHorizontalLift_hasDerivAt R.product (gamma s)
      ((ha.contDiffAt (hO.mem_nhds (hKO hs))).differentiableAt (by simp)).hasDerivAt

end

end PoincareConjecture.M34
