import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.SecondCoordinateLifts
import Mathlib.Topology.Covering.Basic

/-!
# Nonempty second-coordinate levels on the retained boundary

A covering from a nonempty finite phase onto the connected target torus is
surjective. Its actual tangential formula on the collar center therefore
places every second-coordinate level on the retained boundary.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

/-- Compactness of the entire finite phase and connectedness of the target
force a nonempty covering to be surjective, without a connected source. -/
theorem hamiltonZero_phase_covering_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hne : J.space.Nonempty) (g : C(J.space, C0 × C0))
    (hg : IsCoveringMap g) : Function.Surjective g := by
  let : CompactSpace J.space :=
    isCompact_iff_compactSpace.mp (J.isCompact_space_of_finite hJ)
  have hrange : (range g).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨g ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
  exact range_eq_univ.mp
    (IsClopen.eq_univ
      ⟨(isCompact_range g.continuous).isClosed, hg.isOpenMap.isOpen_range⟩ hrange)

/-- The installed whole-phase covering meets every second-coordinate level
on the actual entire boundary of the retained source domain. -/
theorem hamiltonZero_second_boundary_level_nonempty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hne : J.space.Nonempty) (psi : C(H0, H0))
    (c : E × ℝ → X0) {R : Set X0}
    (hboundary : ∀ x : J.space, c (x, 0) ∈ frontier R)
    (g : C(J.space, C0 × C0)) (hg : IsCoveringMap g)
    (hphase : ∀ x : J.space,
      (Q0 (hamiltonZeroAmbientMap psi (c (x, 0)))).1 = g x)
    (theta : C0) :
    (frontier R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}).Nonempty := by
  obtain ⟨x, hx⟩ := hamiltonZero_phase_covering_surjective J hJ hne g hg (0, theta)
  refine ⟨c (x, 0), hboundary x, ?_⟩
  change hamiltonZeroSecondCircleMap psi (c (x, 0)) = theta
  rw [hamiltonZeroSecondCircleMap_ambient, hphase, hx]

/-- Closedness of the retained PL domain puts every boundary level inside
the actual second-coordinate level in that domain. -/
theorem hamiltonZero_second_level_nonempty
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite)
    (hne : J.space.Nonempty) (psi : C(H0, H0))
    (c : E × ℝ → X0) {R : Set X0}
    {e : ι → OpenPartialHomeomorph X0 V3} (he : PLDomain e R)
    (hboundary : ∀ x : J.space, c (x, 0) ∈ frontier R)
    (g : C(J.space, C0 × C0)) (hg : IsCoveringMap g)
    (hphase : ∀ x : J.space,
      (Q0 (hamiltonZeroAmbientMap psi (c (x, 0)))).1 = g x)
    (theta : C0) :
    (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}).Nonempty := by
  obtain ⟨x, hx, hlevel⟩ := hamiltonZero_second_boundary_level_nonempty
    J hJ hne psi c hboundary g hg hphase theta
  exact ⟨x, he.closed.frontier_subset hx, hlevel⟩

end PoincareMT.M76
