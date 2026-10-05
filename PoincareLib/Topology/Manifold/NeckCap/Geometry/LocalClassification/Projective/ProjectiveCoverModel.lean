import PoincareLib.Topology.Manifold.NeckCap.Theory
import PoincareLib.Topology.Quotient.Coordinates

/-!
# The topological model of an actual smooth projective cover

The supplied surjective local diffeomorphism and its literal antipodal
fibers identify its target with the frozen projective quotient. This fills
the topological model input for Morgan--Tian Proposition A.21, pp. 510-514,
after the actual smooth cover has been constructed. The argument reuses
the lower quotient-fiber homeomorphism; see the independently reviewed
`tasks/M25/case-projective/closed-cover-model-plan.md`, declaration C1.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.StandardProjectiveSmoothCover

/-- The actual smooth antipodal cover supplies its topological projective
model and both commuting identities, as used in MT A.21, pp. 510-514. -/
theorem exists_projective_homeomorph
    {Q : Type u} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    (C : PoincareMT.StandardProjectiveSmoothCover Q) :
    ∃ e : Q ≃ₜ PoincareMT.RealProjectiveThree,
      (∀ x : PoincareMT.UnitThreeSphere,
        e (C.cover x) =
          (Quotient.mk' x : PoincareMT.RealProjectiveThree)) ∧
      (∀ x : PoincareMT.UnitThreeSphere,
        e.symm (Quotient.mk' x) = C.cover x) := by
  have hloc := C.local_diffeomorph.isLocalHomeomorph
  let f : C(PoincareMT.UnitThreeSphere, Q) := ⟨C.cover, hloc.continuous⟩
  let g : C(PoincareMT.UnitThreeSphere, PoincareMT.RealProjectiveThree) :=
    ⟨Quotient.mk', continuous_quotient_mk'⟩
  have hf : Topology.IsQuotientMap f :=
    hloc.isOpenMap.isQuotientMap hloc.continuous C.surjective
  have hg : Topology.IsQuotientMap g := isQuotientMap_quotient_mk'
  have hfg : ∀ x y, f x = f y ↔ g x = g y := by
    intro x y
    change C.cover x = C.cover y ↔
      (Quotient.mk' x : PoincareMT.RealProjectiveThree) = Quotient.mk' y
    exact (C.fibers x y).trans
      (@Quotient.eq PoincareMT.UnitThreeSphere
        PoincareMT.realProjectiveThreeSetoid x y).symm
  let e := hf.homeomorphOfFibers hg hfg
  have hcomm (x : PoincareMT.UnitThreeSphere) :
      e (C.cover x) = (Quotient.mk' x : PoincareMT.RealProjectiveThree) :=
    hf.homeomorphOfFibers_apply hg hfg x
  refine ⟨e, hcomm, ?_⟩
  intro x
  rw [← hcomm x]
  exact e.symm_apply_apply (C.cover x)

end PoincareMT.StandardProjectiveSmoothCover
