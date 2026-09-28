import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.Trees
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Topology

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryPath

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {f g : S2 → E3}

def reflected (hv : ‖v‖ = 1) (P : SphereSurgeryPath v f g) :
    SphereSurgeryPath v (heightReflection hv ∘ f) (heightReflection hv ∘ g) := by
  induction P with
  | refl f => exact .refl (heightReflection hv ∘ f)
  | minus S next ih => exact .plus S.reflected ih
  | plus S next ih => exact .minus S.reflected ih

@[simp] theorem reflected_core (hv : ‖v‖ = 1) (P : SphereSurgeryPath v f g) :
    (P.reflected hv).core = P.core := by
  induction P with
  | refl => rfl
  | minus S next ih => exact congrArg (fun U => U ∩ S.eMinus '' closedBall 0 1) ih
  | plus S next ih => exact congrArg (fun U => U ∩ S.ePlus '' closedBall 0 1) ih

@[simp] theorem reflected_boundaryHeights (hv : ‖v‖ = 1) (P : SphereSurgeryPath v f g) :
    (P.reflected hv).boundaryHeights = Neg.neg '' P.boundaryHeights := by
  induction P with
  | refl => simp only [reflected, boundaryHeights, image_empty]
  | @minus f g c R S next ih =>
    change insert (-c + S.a) (next.reflected hv).boundaryHeights =
      Neg.neg '' insert (c - S.a) next.boundaryHeights
    rw [ih]
    simp only [Set.image_insert_eq, neg_sub]
    congr 1
    ring
  | @plus f g c R S next ih =>
    change insert (-c - S.a) (next.reflected hv).boundaryHeights =
      Neg.neg '' insert (c + S.a) next.boundaryHeights
    rw [ih]
    simp only [Set.image_insert_eq, neg_add_rev]
    congr 1
    ring

theorem Protects.reflected (hv : ‖v‖ = 1) {P : SphereSurgeryPath v f g} {B : Set Real}
    (hP : P.Protects B) : (P.reflected hv).Protects (Neg.neg '' B) := by
  induction P with
  | refl => trivial
  | minus S next ih =>
    refine ⟨?_, ih hP.2⟩
    rintro k ⟨j, hj, rfl⟩
    simpa only [neg_sub_neg, abs_sub_comm] using hP.1 j hj
  | plus S next ih =>
    refine ⟨?_, ih hP.2⟩
    rintro k ⟨j, hj, rfl⟩
    simpa only [neg_sub_neg, abs_sub_comm] using hP.1 j hj

theorem PreservesCaps.reflected (hv : ‖v‖ = 1) {P : SphereSurgeryPath v f g}
    (hP : P.PreservesCaps) : (P.reflected hv).PreservesCaps := by
  induction P with
  | refl => trivial
  | minus S next ih =>
    refine ⟨?_, ih hP.2⟩
    change (next.reflected hv).Protects S.reflected.capPlusHeights
    rw [S.reflected_capPlusHeights]
    exact hP.1.reflected hv
  | plus S next ih =>
    refine ⟨?_, ih hP.2⟩
    change (next.reflected hv).Protects S.reflected.capMinusHeights
    rw [S.reflected_capMinusHeights]
    exact hP.1.reflected hv

end Poincare.Manifold.Schoenflies.SphereSurgeryPath

end

end M38Schoenflies
