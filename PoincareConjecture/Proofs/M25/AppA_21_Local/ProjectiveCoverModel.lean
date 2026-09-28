import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.Horizon.Topology.Quotient.Coordinates

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.StandardProjectiveSmoothCover

theorem exists_projective_homeomorph
    {Q : Type u} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    (C : PoincareConjecture.StandardProjectiveSmoothCover Q) :
    ∃ e : Q ≃ₜ PoincareConjecture.RealProjectiveThree,
      (∀ x : PoincareConjecture.UnitThreeSphere,
        e (C.cover x) =
          (Quotient.mk' x : PoincareConjecture.RealProjectiveThree)) ∧
      (∀ x : PoincareConjecture.UnitThreeSphere,
        e.symm (Quotient.mk' x) = C.cover x) := by
  have hloc := C.local_diffeomorph.isLocalHomeomorph
  let f : C(PoincareConjecture.UnitThreeSphere, Q) := ⟨C.cover, hloc.continuous⟩
  let g : C(PoincareConjecture.UnitThreeSphere, PoincareConjecture.RealProjectiveThree) :=
    ⟨Quotient.mk', continuous_quotient_mk'⟩
  have hf : Topology.IsQuotientMap f :=
    hloc.isOpenMap.isQuotientMap hloc.continuous C.surjective
  have hg : Topology.IsQuotientMap g := isQuotientMap_quotient_mk'
  have hfg : ∀ x y, f x = f y ↔ g x = g y := by
    intro x y
    change C.cover x = C.cover y ↔
      (Quotient.mk' x : PoincareConjecture.RealProjectiveThree) = Quotient.mk' y
    exact (C.fibers x y).trans
      (@Quotient.eq PoincareConjecture.UnitThreeSphere
        PoincareConjecture.realProjectiveThreeSetoid x y).symm
  let e := hf.homeomorphOfFibers hg hfg
  have hcomm (x : PoincareConjecture.UnitThreeSphere) :
      e (C.cover x) = (Quotient.mk' x : PoincareConjecture.RealProjectiveThree) :=
    hf.homeomorphOfFibers_apply hg hfg x
  refine ⟨e, hcomm, ?_⟩
  intro x
  rw [← hcomm x]
  exact e.symm_apply_apply (C.cover x)

end PoincareConjecture.StandardProjectiveSmoothCover
