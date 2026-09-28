import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ConnectedComponent
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

noncomputable section
set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology

namespace Poincare

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

def connectedComponentDiffeomorph (e : M ≃ₘ⟮𝓡 n, 𝓡 m⟯ N) (p : M) :
    connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p ≃ₘ⟮𝓡 n, 𝓡 m⟯
      connectedComponentOpens (EuclideanSpace ℝ (Fin m)) (e p) := by
  let U := connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p
  let V := connectedComponentOpens (EuclideanSpace ℝ (Fin m)) (e p)
  let E : U ≃ V :=
    { toFun := fun x => ⟨e x.val, e.continuous.mapsTo_connectedComponent p x.property⟩
      invFun := fun y => ⟨e.symm y.val, by
        have hy := e.symm.continuous.mapsTo_connectedComponent (e p) y.property
        change e.symm y.val ∈ connectedComponent p
        simpa only [e.symm_apply_apply] using hy⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val) }
  refine { E with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff V E).mp
    exact e.contMDiff.comp contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff U E.symm).mp
    exact e.symm.contMDiff.comp contMDiff_subtype_val

@[simp] theorem connectedComponentDiffeomorph_val
    (e : M ≃ₘ⟮𝓡 n, 𝓡 m⟯ N) (p : M)
    (x : connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p) :
    (connectedComponentDiffeomorph e p x).val = e x.val := rfl

end Poincare
