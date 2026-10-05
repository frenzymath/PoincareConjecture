import PoincareLib.Topology.Manifold.NeckCap.Geometry.Topology.Gluing.Projective.ProjectiveCover
import PoincareLib.Topology.Quotient.Coordinates

/-!
# The topological model of an actual punctured projective cover

The actual restricted cover and the canonical restricted quotient have
the same fibers. The lower quotient-coordinate theorem identifies their
targets, retaining both commuting formulas. This is the punctured model
adapter for Morgan--Tian A.21, pp. 510-514; see the independently reviewed
`tasks/M25/case-projective/punctured-double-model-plan.md`, declaration P1.
No assertion about the frozen cover at its omitted antipodal pair is used.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.StandardPuncturedProjectiveCover

/-- An actual punctured smooth cover has its literal punctured quotient
model with both commuting identities. MT A.21, pp. 510-514; P1 of the
punctured-double model derivation. -/
theorem exists_punctured_homeomorph
    {Q : Type u} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    {p : PoincareMT.RealProjectiveThree} {U : Set Q}
    (C : PoincareMT.StandardPuncturedProjectiveCover Q p U) :
    ∃ e : U ≃ₜ PoincareMT.PuncturedRealProjectiveThree p,
      (∀ x : PoincareMT.M25.Topology3D.projectiveCoverDomain p,
        e (PoincareMT.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover
          C x) = ⟨Quotient.mk' x.1, x.2⟩) ∧
      (∀ x : PoincareMT.M25.Topology3D.projectiveCoverDomain p,
        e.symm ⟨Quotient.mk' x.1, x.2⟩ =
          PoincareMT.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover
            C x) := by
  have hloc :=
    PoincareMT.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover_isLocalHomeomorph C
  let f : C(PoincareMT.M25.Topology3D.projectiveCoverDomain p, U) :=
    ⟨PoincareMT.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover C,
      hloc.continuous⟩
  let q : PoincareMT.M25.Topology3D.projectiveCoverDomain p →
      PoincareMT.PuncturedRealProjectiveThree p :=
    fun x => ⟨Quotient.mk' x.1, x.2⟩
  have hproj : IsOpenQuotientMap
      (@Quotient.mk' PoincareMT.UnitThreeSphere PoincareMT.realProjectiveThreeSetoid) :=
    Poincare.Topology.isOpenQuotientMap_of_pair_fibers
      PoincareMT.realProjectiveThreeSetoid Neg.neg continuous_neg (fun _ _ => Iff.rfl)
  have hq : IsOpenQuotientMap q :=
    hproj.restrictPreimage_of_isOpen_preimage
      {y : PoincareMT.RealProjectiveThree | y ≠ p}
      (PoincareMT.M25.Topology3D.isOpen_projectiveCoverDomain p)
  let g : C(PoincareMT.M25.Topology3D.projectiveCoverDomain p,
      PoincareMT.PuncturedRealProjectiveThree p) := ⟨q, hq.continuous⟩
  have hf : Topology.IsQuotientMap f :=
    hloc.isOpenMap.isQuotientMap hloc.continuous
      (PoincareMT.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover_surjective C)
  have hg : Topology.IsQuotientMap g := hq.isQuotientMap
  have hfg : ∀ x y, f x = f y ↔ g x = g y := by
    intro x y
    have hleft : f x = f y ↔ C.cover x.1 = C.cover y.1 := Subtype.ext_iff
    have hright : g x = g y ↔
        (Quotient.mk' x.1 : PoincareMT.RealProjectiveThree) = Quotient.mk' y.1 :=
      Subtype.ext_iff
    exact hleft.trans (((C.fibers x.1 y.1 x.2 y.2).trans
      (@Quotient.eq PoincareMT.UnitThreeSphere
        PoincareMT.realProjectiveThreeSetoid x.1 y.1).symm).trans hright.symm)
  let e := hf.homeomorphOfFibers hg hfg
  have hcomm (x : PoincareMT.M25.Topology3D.projectiveCoverDomain p) :
      e (PoincareMT.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover C x) =
        ⟨Quotient.mk' x.1, x.2⟩ :=
    hf.homeomorphOfFibers_apply hg hfg x
  refine ⟨e, hcomm, ?_⟩
  intro x
  rw [← hcomm x]
  exact e.symm_apply_apply _

end PoincareMT.StandardPuncturedProjectiveCover
