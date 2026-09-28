import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Lift

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {M : Type u} {N : Type}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]

noncomputable def CapModelEquivalence.pullbackSmall {kind : CapModelKind}
    {p : RealProjectiveThree} {U : Set N} (K : CapModelEquivalence kind p U)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) :
    CapModelEquivalence kind p (e ⁻¹' U) := by
  let : TopologicalSpace K.model := K.model_topology
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) K.model := K.model_charted
  let : IsManifold (𝓡 3) ∞ K.model := K.model_manifold
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ULift.{u} K.model) :=
    Poincare.Manifold.uliftChartedSpace _ K.model
  let : IsManifold (𝓡 3) ∞ (ULift.{u} K.model) :=
    Poincare.Manifold.uliftIsManifold (𝓡 3) K.model
  let D : Diffeomorph (𝓡 3) (𝓡 3) (ULift.{u} K.model) K.model ∞ :=
    Poincare.Manifold.uliftDiffeomorph (𝓡 3) K.model
  refine {
    model := ULift.{u} K.model
    model_topology := inferInstance
    model_charted := inferInstance
    model_manifold := inferInstance
    standard_model := ?_
    standard_smooth := ?_
    forward := D.symm ∘ K.forward ∘ e
    inverse := e.symm ∘ K.inverse ∘ D
    inverse_mem := fun y => by simpa using K.inverse_mem (D y)
    left_inverse := ?_
    right_inverse := ?_
    forward_smooth := ?_
    inverse_smooth := ?_ }
  · cases kind <;>
      exact ((Homeomorph.ulift.trans K.standard_model).trans Homeomorph.ulift).trans
        Homeomorph.ulift.symm
  · cases kind with
    | euclidean =>
        obtain ⟨d⟩ := K.standard_smooth
        exact ⟨D.trans d⟩
    | puncturedProjective =>
        obtain ⟨C⟩ := K.standard_smooth
        refine ⟨{
          cover := D.symm ∘ C.cover
          image_eq := ?_
          fibers := fun x y hx hy => D.symm.injective.eq_iff.trans (C.fibers x y hx hy)
          local_diffeomorph := fun x => (C.local_diffeomorph x).comp (𝓡 3)
            (ULift.{u} K.model) (D.symm.isLocalDiffeomorph _) }⟩
        rw [image_comp, C.image_eq]
        exact image_univ_of_surjective D.symm.surjective
  · intro x hx
    dsimp only [Function.comp_apply]
    rw [D.apply_symm_apply, K.left_inverse (e x) hx, e.symm_apply_apply]
  · intro y
    dsimp only [Function.comp_apply]
    rw [e.apply_symm_apply, K.right_inverse, D.symm_apply_apply]
  · exact D.symm.contMDiff.comp_contMDiffOn
      (K.forward_smooth.comp e.contMDiff.contMDiffOn (fun _ hx => hx))
  · exact e.symm.contMDiff.comp_contMDiffOn
      (K.inverse_smooth.comp D.contMDiff.contMDiffOn (fun _ _ => mem_univ _))

@[simp] theorem CapModelEquivalence.pullbackSmall_forward {kind : CapModelKind}
    {p : RealProjectiveThree} {U : Set N} (K : CapModelEquivalence kind p U)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (x : M) :
    (K.pullbackSmall e).forward x = ULift.up (K.forward (e x)) := rfl

@[simp] theorem CapModelEquivalence.pullbackSmall_inverse {kind : CapModelKind}
    {p : RealProjectiveThree} {U : Set N} (K : CapModelEquivalence kind p U)
    (e : Diffeomorph (𝓡 3) (𝓡 3) M N ∞) (y : ULift.{u} K.model) :
    (K.pullbackSmall e).inverse y = e.symm (K.inverse y.down) := rfl

end PoincareConjecture
