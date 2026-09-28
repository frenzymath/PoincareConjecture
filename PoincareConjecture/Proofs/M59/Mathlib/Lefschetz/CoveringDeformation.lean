import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Equiv











set_option autoImplicit false

noncomputable section

open scoped unitInterval

universe u v

namespace PoincareConjecture.Proofs.M59

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  (p : C(E, X)) (hp : IsCoveringMap p) (H : C(I × X, X))
  (hzero : ∀ x, H (0, x) = x)



def coveringLiftedDeformation : C(I × E, E) :=
  hp.liftHomotopy
    ⟨fun q => H (q.1, p q.2), H.continuous.comp
      (continuous_fst.prodMk (p.continuous.comp continuous_snd))⟩
    (ContinuousMap.id E) (fun e => hzero (p e))



theorem coveringLiftedDeformation_projection (t : I) (e : E) :
    p (coveringLiftedDeformation p hp H hzero (t, e)) = H (t, p e) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) (t, e)



theorem coveringLiftedDeformation_zero (e : E) :
    coveringLiftedDeformation p hp H hzero (0, e) = e :=
  hp.liftHomotopy_zero _ _ _ e



theorem coveringLiftedDeformation_fixed (e : E) (he : ∀ t, H (t, p e) = p e) (t : I) :
    coveringLiftedDeformation p hp H hzero (t, e) = e := by
  have h := hp.eq_of_comp_eq
    ((coveringLiftedDeformation p hp H hzero).continuous.comp
      (continuous_id.prodMk continuous_const)) continuous_const
    (funext fun q => (coveringLiftedDeformation_projection p hp H hzero q e).trans (he q))
    0 (coveringLiftedDeformation_zero p hp H hzero e)
  exact congrFun h t

variable (S : Set X) (hone : ∀ x, H (1, x) ∈ S)
  (hfixed : ∀ x ∈ S, ∀ t, H (t, x) = x)



def coveringDeformationRetraction : C(E, p ⁻¹' S) := by
  refine ⟨fun e => ⟨coveringLiftedDeformation p hp H hzero (1, e), ?_⟩, ?_⟩
  · change p (coveringLiftedDeformation p hp H hzero (1, e)) ∈ S
    rw [coveringLiftedDeformation_projection]
    exact hone (p e)
  · exact ((coveringLiftedDeformation p hp H hzero).continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _




def coveringDeformationEquiv : ContinuousMap.HomotopyEquiv (p ⁻¹' S) E where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := coveringDeformationRetraction p hp H hzero S hone
  left_inv := by
    have h : (coveringDeformationRetraction p hp H hzero S hone).comp
        ⟨Subtype.val, continuous_subtype_val⟩ = ContinuousMap.id (p ⁻¹' S) := by
      ext e : 1
      apply Subtype.ext
      exact coveringLiftedDeformation_fixed p hp H hzero e.val
        (hfixed (p e.val) e.property) 1
    rw [h]
  right_inv := by
    apply Nonempty.intro
    apply ContinuousMap.Homotopy.symm
    exact {
      toContinuousMap := coveringLiftedDeformation p hp H hzero
      map_zero_left := coveringLiftedDeformation_zero p hp H hzero
      map_one_left := fun _ => rfl }

end PoincareConjecture.Proofs.M59
