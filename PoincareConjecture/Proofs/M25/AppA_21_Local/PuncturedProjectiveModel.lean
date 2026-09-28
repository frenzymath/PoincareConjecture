import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCover
import PoincareConjecture.Proofs.Horizon.Topology.Quotient.Coordinates

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StandardPuncturedProjectiveCover

theorem exists_punctured_homeomorph
    {Q : Type u} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    {p : PoincareConjecture.RealProjectiveThree} {U : Set Q}
    (C : PoincareConjecture.StandardPuncturedProjectiveCover Q p U) :
    ∃ e : U ≃ₜ PoincareConjecture.PuncturedRealProjectiveThree p,
      (∀ x : PoincareConjecture.M25.Topology3D.projectiveCoverDomain p,
        e (PoincareConjecture.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover
          C x) = ⟨Quotient.mk' x.1, x.2⟩) ∧
      (∀ x : PoincareConjecture.M25.Topology3D.projectiveCoverDomain p,
        e.symm ⟨Quotient.mk' x.1, x.2⟩ =
          PoincareConjecture.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover
            C x) := by
  have hloc :=
    PoincareConjecture.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover_isLocalHomeomorph C
  let f : C(PoincareConjecture.M25.Topology3D.projectiveCoverDomain p, U) :=
    ⟨PoincareConjecture.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover C,
      hloc.continuous⟩
  let q : PoincareConjecture.M25.Topology3D.projectiveCoverDomain p →
      PoincareConjecture.PuncturedRealProjectiveThree p :=
    fun x => ⟨Quotient.mk' x.1, x.2⟩
  have hproj : IsOpenQuotientMap
      (@Quotient.mk' PoincareConjecture.UnitThreeSphere PoincareConjecture.realProjectiveThreeSetoid) :=
    Poincare.Topology.isOpenQuotientMap_of_pair_fibers
      PoincareConjecture.realProjectiveThreeSetoid Neg.neg continuous_neg (fun _ _ => Iff.rfl)
  have hq : IsOpenQuotientMap q :=
    hproj.restrictPreimage_of_isOpen_preimage
      {y : PoincareConjecture.RealProjectiveThree | y ≠ p}
      (PoincareConjecture.M25.Topology3D.isOpen_projectiveCoverDomain p)
  let g : C(PoincareConjecture.M25.Topology3D.projectiveCoverDomain p,
      PoincareConjecture.PuncturedRealProjectiveThree p) := ⟨q, hq.continuous⟩
  have hf : Topology.IsQuotientMap f :=
    hloc.isOpenMap.isQuotientMap hloc.continuous
      (PoincareConjecture.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover_surjective C)
  have hg : Topology.IsQuotientMap g := hq.isQuotientMap
  have hfg : ∀ x y, f x = f y ↔ g x = g y := by
    intro x y
    have hleft : f x = f y ↔ C.cover x.1 = C.cover y.1 := Subtype.ext_iff
    have hright : g x = g y ↔
        (Quotient.mk' x.1 : PoincareConjecture.RealProjectiveThree) = Quotient.mk' y.1 :=
      Subtype.ext_iff
    exact hleft.trans (((C.fibers x.1 y.1 x.2 y.2).trans
      (@Quotient.eq PoincareConjecture.UnitThreeSphere
        PoincareConjecture.realProjectiveThreeSetoid x.1 y.1).symm).trans hright.symm)
  let e := hf.homeomorphOfFibers hg hfg
  have hcomm (x : PoincareConjecture.M25.Topology3D.projectiveCoverDomain p) :
      e (PoincareConjecture.M25.Topology3D.StandardPuncturedProjectiveCover.restrictedCover C x) =
        ⟨Quotient.mk' x.1, x.2⟩ :=
    hf.homeomorphOfFibers_apply hg hfg x
  refine ⟨e, hcomm, ?_⟩
  intro x
  rw [← hcomm x]
  exact e.symm_apply_apply _

end PoincareConjecture.StandardPuncturedProjectiveCover
