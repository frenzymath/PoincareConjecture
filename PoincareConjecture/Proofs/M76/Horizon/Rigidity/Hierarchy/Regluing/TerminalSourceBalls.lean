import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalSphericalFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.IrreducibleSphericalBoundaryComponent
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Cancellation.SelectedComponentBoundaries

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76

theorem exists_ball_components_of_irreducible_spherical_frontier_partition
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {N : Set X}
    (hI : IsPLIrreducible e N) (hN : IsCompact N) (hproper : N ≠ univ)
    {n : ℕ} (S : Fin n → Set X)
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hcover : (⋃ i, S i) = frontier N)
    (hS : ∀ i, IsCompact (S i) ∧ (S i).Nonempty ∧
      Nonempty (ChartwisePLSphere e (S i))) :
    (∀ x ∈ N, Nonempty (ChartwisePLBall e (connectedComponentIn N x)
      (frontier (connectedComponentIn N x)))) ∧
    ∃ P : Fin n → Set X,
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (⋃ i, P i) = N ∧
      ∀ i, IsCompact (P i) ∧ Nonempty (ChartwisePLBall e (P i) (frontier (P i))) ∧
        frontier (P i) = S i ∧ ∀ x ∈ P i, connectedComponentIn N x = P i := by
  classical
  have hSF (i : Fin n) : S i ⊆ frontier N :=
    (subset_iUnion S i).trans hcover.subset
  have hSN (i : Fin n) : S i ⊆ N := (hSF i).trans hI.1.closed.frontier_subset
  have hSclopen (i : Fin n) : IsClopen ((Subtype.val : frontier N → X) ⁻¹' S i) := by
    have h := Poincare.Topology.isClopen_part_of_finite_closed_partition
      S (fun j => (hS j).1.isClosed) hdis i
    exact h.preimage (Homeomorph.setCongr hcover.symm).continuous
  have componentBall {x : X} (hx : x ∈ N) {i : Fin n}
      (hmeet : (frontier (connectedComponentIn N x) ∩ S i).Nonempty) :
      frontier (connectedComponentIn N x) = S i ∧
        Nonempty (ChartwisePLBall e (connectedComponentIn N x) (S i)) := by
    have hfront := hI.1.frontier_connectedComponentIn_of_compact hN hx
    obtain ⟨sph⟩ := (hS i).2.2
    obtain ⟨z, hzfront, hzi⟩ := hmeet
    have hSP : S i ⊆ connectedComponentIn N x := by
      have h := sph.isConnected.isPreconnected.subset_connectedComponentIn hzi (hSN i)
      rwa [← connectedComponentIn_eq ((hfront.subset hzfront).1)] at h
    have hSPfront : S i ⊆ frontier (connectedComponentIn N x) := by
      rw [hfront]
      exact subset_inter hSP (hSF i)
    have hc : IsClopen
        ((Subtype.val : frontier (connectedComponentIn N x) → X) ⁻¹' S i) := by
      let inc : frontier (connectedComponentIn N x) → frontier N :=
        Set.inclusion (fun _ hz => (hfront.subset hz).2)
      exact (hSclopen i).preimage (show Continuous inc from continuous_inclusion _)
    exact (hI.connectedComponentIn hN hx).nonempty_ball_of_spherical_boundary_component
      (Set.isCompact_connectedComponentIn_of_mem hN hx)
      (isConnected_connectedComponentIn_iff.mpr hx) hSPfront hc sph
  have componentFront {x : X} (hx : x ∈ N) :
      (frontier (connectedComponentIn N x)).Nonempty := by
    apply nonempty_frontier_iff.mpr
    refine ⟨⟨x, mem_connectedComponentIn hx⟩, ?_⟩
    intro hall
    apply hproper
    exact eq_univ_of_univ_subset (hall ▸ connectedComponentIn_subset N x)
  have hballs : ∀ x ∈ N, Nonempty (ChartwisePLBall e (connectedComponentIn N x)
      (frontier (connectedComponentIn N x))) := by
    intro x hx
    obtain ⟨z, hz⟩ := componentFront hx
    have hzF := ((hI.1.frontier_connectedComponentIn_of_compact hN hx).subset hz).2
    obtain ⟨i, hzi⟩ := mem_iUnion.mp (hcover.symm.subset hzF)
    obtain ⟨heq, hball⟩ := componentBall hx ⟨z, hz, hzi⟩
    exact heq.symm ▸ hball
  let z (i : Fin n) : X := Classical.choose (hS i).2.1
  have hz (i : Fin n) : z i ∈ S i := Classical.choose_spec (hS i).2.1
  let P (i : Fin n) : Set X := connectedComponentIn N (z i)
  have hfront (i : Fin n) : frontier (P i) = S i := by
    apply (componentBall (hSN i (hz i)) ?_).1
    refine ⟨z i, ?_, hz i⟩
    rw [hI.1.frontier_connectedComponentIn_of_compact hN (hSN i (hz i))]
    exact ⟨mem_connectedComponentIn (hSN i (hz i)), hSF i (hz i)⟩
  have hPdis : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro y hyi hyj
    have heq : P i = P j := (connectedComponentIn_eq hyi).trans
      (connectedComponentIn_eq hyj).symm
    have hSeq : S i = S j := (hfront i).symm.trans ((congrArg frontier heq).trans (hfront j))
    exact disjoint_left.mp (hdis hij) (hz i) (hSeq ▸ hz i)
  have hPcover : (⋃ i, P i) = N := by
    apply Subset.antisymm (iUnion_subset fun i => connectedComponentIn_subset N (z i))
    intro x hx
    obtain ⟨y, hy⟩ := componentFront hx
    have hyF := ((hI.1.frontier_connectedComponentIn_of_compact hN hx).subset hy).2
    obtain ⟨i, hyi⟩ := mem_iUnion.mp (hcover.symm.subset hyF)
    obtain ⟨hfrontx, _⟩ := componentBall hx ⟨y, hy, hyi⟩
    have hzcomp : z i ∈ connectedComponentIn N x :=
      (Set.isCompact_connectedComponentIn_of_mem hN hx).isClosed.frontier_subset
        (hfrontx.symm ▸ hz i)
    exact mem_iUnion.mpr ⟨i, (connectedComponentIn_eq hzcomp).symm ▸ mem_connectedComponentIn hx⟩
  exact ⟨hballs, P, hPdis, hPcover, fun i =>
    ⟨Set.isCompact_connectedComponentIn_of_mem hN (hSN i (hz i)),
      hballs (z i) (hSN i (hz i)), hfront i, fun _ hx => (connectedComponentIn_eq hx).symm⟩⟩

local notation "V3" => (Fin 3 → ℝ)
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_terminal_source_balls
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {N : Set X0} (hI : IsPLIrreducible e N) (hN : IsCompact N) (hne : N.Nonempty)
    {u v a b alpha beta : ℝ} (huv : u < v) (hab : a < b) (halpha : alpha < beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p)
    (hNarc : MapsTo (hamiltonZeroCircleMap phi) N (AddCircle.closedIntervalArc p alpha beta))
    (boundaryMap : C(frontier N, frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)))
    (hvalue : ∀ x : frontier N, Q0 (hamiltonZeroAmbientMap phi x) =
      (((((boundaryMap x : E3).1.1) : C0), (((boundaryMap x : E3).1.2) : C0)),
        (((boundaryMap x : E3).2) : C0)))
    (hc : IsCoveringMap boundaryMap) :
    (∀ x ∈ N, Nonempty (ChartwisePLBall e (connectedComponentIn N x)
      (frontier (connectedComponentIn N x)))) ∧
    ∃ (n : ℕ) (P : Fin n → Set X0),
      Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (⋃ i, P i) = N ∧
      ∀ i, IsCompact (P i) ∧ Nonempty (ChartwisePLBall e (P i) (frontier (P i))) ∧
        ∀ x ∈ P i, connectedComponentIn N x = P i := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : PreconnectedSpace X0 := preconnectedSpace_iff_univ.mpr (by
    simpa only [image_univ, (Q0).symm.surjective.range_eq] using
      isPreconnected_univ.image (Q0).symm (Q0).symm.continuous.continuousOn)
  have hproper : N ≠ univ := by
    intro hNu
    let t : ℝ := (beta + (alpha + p)) / 2
    obtain ⟨x, hx⟩ := surjective_hamiltonZeroCircleMap phi F (t : C0)
    have hm := hNarc (hNu.symm ▸ mem_univ x)
    rw [hx] at hm
    obtain ⟨s, hs, hst⟩ := hm
    have hsI : s ∈ Ico alpha (alpha + p) := ⟨hs.1, hs.2.trans_lt hfirst⟩
    have htI : t ∈ Ico alpha (alpha + p) := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico hsI htI).mp hst
    dsimp [t] at heq
    linarith [hs.2]
  obtain ⟨n, S, hdis, hcover, hS⟩ := exists_hamiltonZero_terminal_spherical_frontier
    hd hphi hI.1 hN hne huv hab halpha hthird hsecond hfirst boundaryMap hvalue hc
  obtain ⟨hballs, P, hPdis, hPcover, hP⟩ :=
    exists_ball_components_of_irreducible_spherical_frontier_partition hI hN hproper S hdis hcover
      (fun i => ⟨(hS i).1, (hS i).2.1, (hS i).2.2.1⟩)
  exact ⟨hballs, n, P, hPdis, hPcover, fun i => ⟨(hP i).1, (hP i).2.1, (hP i).2.2.2⟩⟩

end PoincareConjecture.M76
