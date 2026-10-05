import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Equiv

/-!
# Strong deformations lifted through a covering

A deformation into a subspace that fixes that subspace pointwise lifts
from the identity to a deformation into its inverse image. The inclusion
of this inverse image is therefore an actual homotopy equivalence.
Source: Hatcher, Proposition 1.30, printed p. 60, used in the comparison
of Theorem 2.27, pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open scoped unitInterval

universe u v

namespace PoincareMT.Proofs.M59

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  (p : C(E, X)) (hp : IsCoveringMap p) (H : C(I × X, X))
  (hzero : ∀ x, H (0, x) = x)

/-- Lift a deformation of the base, starting at the actual identity
on the covering space. Source: Hatcher, Proposition 1.30, p. 60. -/
def coveringLiftedDeformation : C(I × E, E) :=
  hp.liftHomotopy
    ⟨fun q => H (q.1, p q.2), H.continuous.comp
      (continuous_fst.prodMk (p.continuous.comp continuous_snd))⟩
    (ContinuousMap.id E) (fun e => hzero (p e))

/-- The lifted deformation projects to the original one at every time.
Source: Hatcher, Proposition 1.30, p. 60. -/
theorem coveringLiftedDeformation_projection (t : I) (e : E) :
    p (coveringLiftedDeformation p hp H hzero (t, e)) = H (t, p e) :=
  congrFun (hp.liftHomotopy_lifts _ _ _) (t, e)

/-- The lifted deformation starts at the actual identity.
Source: Hatcher, Proposition 1.30, p. 60. -/
theorem coveringLiftedDeformation_zero (e : E) :
    coveringLiftedDeformation p hp H hzero (0, e) = e :=
  hp.liftHomotopy_zero _ _ _ e

/-- A point whose projection stays fixed has a constant lifted path.
Source: uniqueness of covering lifts, Hatcher, Proposition 1.34, p. 62. -/
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

/-- The final lifted map takes values in the actual inverse-image
subspace. Source: Hatcher, Proposition 1.30, p. 60. -/
def coveringDeformationRetraction : C(E, p ⁻¹' S) := by
  refine ⟨fun e => ⟨coveringLiftedDeformation p hp H hzero (1, e), ?_⟩, ?_⟩
  · change p (coveringLiftedDeformation p hp H hzero (1, e)) ∈ S
    rw [coveringLiftedDeformation_projection]
    exact hone (p e)
  · exact ((coveringLiftedDeformation p hp H hzero).continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _

/-- Lifting a strong deformation yields a homotopy equivalence whose
forward map is the literal subspace inclusion.
Source: Hatcher, Proposition 1.30, p. 60. -/
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

end PoincareMT.Proofs.M59
