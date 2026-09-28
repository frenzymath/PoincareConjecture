import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.IncompressibleCutIrreducibility
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.SlabExcision

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem IsPLIrreducible.of_boundary_meeting_cut
    {X ι σ : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R N : Set X}
    (hI : IsPLIrreducible e R) (he : PLDomain e N) (hNR : N ⊆ R)
    (M : σ → Set X) (hMfront : ∀ i, M i ⊆ frontier N)
    (hcut : ∀ x ∈ frontier N, x ∈ interior R → ∃ i, x ∈ M i)
    (hMconn : ∀ i, IsPreconnected (M i))
    (hmeet : ∀ i, (M i ∩ frontier R).Nonempty) :
    IsPLIrreducible e N := by
  refine ⟨he, ?_⟩
  intro S hSN hs
  obtain ⟨sphere⟩ := hs
  have hSint : S ⊆ interior R := hSN.trans (interior_mono hNR)
  obtain ⟨D, hDR, ⟨ball⟩⟩ := hI.2 S hSint ⟨sphere⟩
  have hDint : D ⊆ interior R := ball.subset_interior hDR hSint
  have hDM (i : σ) : Disjoint D (M i) := by
    have hMS : Disjoint (M i) S :=
      disjoint_interior_frontier.symm.mono (hMfront i) hSN
    apply disjoint_left.mpr
    intro x hxD hxM
    have hxint : x ∈ interior D := by
      rw [ball.interior_eq_sdiff]
      exact ⟨hxD, fun hxS => disjoint_left.mp hMS hxM hxS⟩
    have hMint : M i ⊆ interior D := by
      apply (hMconn i).subset_of_closure_inter_subset isOpen_interior ⟨x, hxM, hxint⟩
      rw [ball.closure_interior, ball.interior_eq_sdiff]
      exact fun y hy => ⟨hy.1, fun hyS => disjoint_left.mp hMS hy.2 hyS⟩
    obtain ⟨y, hyM, hyR⟩ := hmeet i
    exact hyR.2 (hDint (interior_subset (hMint hyM)))
  have hDfront : Disjoint D (frontier N) := by
    apply disjoint_left.mpr
    intro x hxD hxfront
    obtain ⟨i, hxi⟩ := hcut x hxfront (hDint hxD)
    exact disjoint_left.mp (hDM i) hxD hxi
  have hDconn : IsPreconnected D := by
    rw [← ball.closure_interior]
    exact ball.isConnected_interior.isPreconnected.closure
  have hDN : D ⊆ interior N := by
    apply hDconn.subset_of_closure_inter_subset isOpen_interior
    · obtain ⟨x, hx⟩ := sphere.isConnected.nonempty
      exact ⟨x, ball.boundary_subset hx, hSN hx⟩
    · intro x hx
      have hxN : x ∈ N := he.closed.closure_eq.subset (closure_mono interior_subset hx.1)
      exact (mem_interior_iff_notMem_frontier hxN).mpr
        (fun hxf => disjoint_left.mp hDfront hx.2 hxf)
  exact ⟨D, hDN.trans interior_subset, ⟨ball⟩⟩

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem isPLIrreducible_hamiltonZero_second_slab_of_boundary_meeting_components
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) {R : Set X0} (hI : IsPLIrreducible e R)
    {u v : ℝ} {a b : C0}
    (he : PLDomain e (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p u v))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p u v) =
      ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v) ∩
        frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {a}) ∪
          (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {b})))
    (hcomponents : ∀ theta ∈ ({a, b} : Set C0),
      ∀ x ∈ R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta},
        (connectedComponentIn (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}) x ∩
          frontier R).Nonempty) :
    IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p u v) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let F : Bool → Set X0 := fun side =>
    R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {if side then b else a}
  let M (i : Σ side : Bool, F side) := connectedComponentIn (F i.1) i.2
  have hMfront (i : Σ side : Bool, F side) : M i ⊆ frontier
      (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v) := by
    intro x hx
    have hxF := connectedComponentIn_subset (F i.1) i.2 hx
    rw [hfront]
    apply Or.inr
    rcases i with ⟨side, y⟩
    cases side
    · exact Or.inl hxF
    · exact Or.inr hxF
  apply hI.of_boundary_meeting_cut he inter_subset_left M hMfront
  · intro x hx hxint
    rw [hfront] at hx
    rcases hx with hxold | hxa | hxb
    · exact (hxold.2.2 hxint).elim
    · exact ⟨⟨false, ⟨x, hxa⟩⟩, mem_connectedComponentIn hxa⟩
    · exact ⟨⟨true, ⟨x, hxb⟩⟩, mem_connectedComponentIn hxb⟩
  · intro i
    exact isPreconnected_connectedComponentIn
  · rintro ⟨side, x⟩
    cases side
    · exact hcomponents a (Or.inl rfl) x x.property
    · exact hcomponents b (Or.inr rfl) x x.property

theorem isPLIrreducible_hamiltonZero_complementary_second_slabs
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    (phi : C(H0, H0)) {R : Set X0} (hI : IsPLIrreducible e R) {a b : ℝ}
    (hslabs : ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(b : C0)})))
    (hcomponents : ∀ theta ∈ ({a, b} : Set ℝ),
      ∀ x ∈ R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(theta : C0)},
        (connectedComponentIn (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(theta : C0)}) x ∩
          frontier R).Nonempty) :
    ∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) := by
  intro side
  apply isPLIrreducible_hamiltonZero_second_slab_of_boundary_meeting_components phi hI
    (hslabs side).1 (hslabs side).2
  intro theta htheta
  rcases htheta with rfl | rfl
  · exact hcomponents a (Or.inl rfl)
  · exact hcomponents b (Or.inr rfl)

end PoincareConjecture.M76
