import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateLifts
import Mathlib.Topology.Covering.Basic

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_compact_phase_covering_surjective
    {E : Type*} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g) : Function.Surjective g := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hrange : (range g).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨g ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
  exact range_eq_univ.mp (IsClopen.eq_univ
    ⟨(isCompact_range g.continuous).isClosed, hg.isOpenMap.isOpen_range⟩ hrange)

theorem hamiltonZero_installed_second_boundary_levels_nonempty
    {E : Type*} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (phi : C(H0, H0))
    (c : E × ℝ → X0) {R : Set X0}
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hphase : ∀ x : K, (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1 = g x) :
    ∀ theta : C0,
      (frontier R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}).Nonempty := by
  intro theta
  obtain ⟨x, hx⟩ := hamiltonZero_compact_phase_covering_surjective hK hne g hg (0, theta)
  refine ⟨c (x, 0), hzero.subset ⟨(x, 0), ⟨x.property, rfl⟩, rfl⟩, ?_⟩
  change hamiltonZeroSecondCircleMap phi (c (x, 0)) = theta
  rw [hamiltonZeroSecondCircleMap_ambient, hphase, hx]

theorem hamiltonZero_installed_second_levels_nonempty
    {E ι : Type*} [TopologicalSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (phi : C(H0, H0))
    (c : E × ℝ → X0) {R : Set X0}
    {e : ι → OpenPartialHomeomorph X0 V3} (he : PLDomain e R)
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hphase : ∀ x : K, (Q0 (hamiltonZeroAmbientMap phi (c (x, 0)))).1 = g x) :
    ∀ theta : C0, (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}).Nonempty := by
  intro theta
  obtain ⟨x, hx, hlevel⟩ :=
    hamiltonZero_installed_second_boundary_levels_nonempty hK hne phi c hzero g hg hphase theta
  exact ⟨x, he.closed.frontier_subset hx, hlevel⟩

end PoincareConjecture.M76
