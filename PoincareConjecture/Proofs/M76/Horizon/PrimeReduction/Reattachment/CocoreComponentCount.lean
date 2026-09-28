import PoincareConjecture.Proofs.Horizon.Topology.Connected.FourContacts.Resolution
import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicRegularSection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RegularCocoreSection

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem cocore_component_count_eq_zero_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : HasDisjointPolygonPresentation S) :
    Nat.card (ConnectedComponents S) = 0 ↔ S = ∅ := by
  obtain ⟨m,k,P,hP,hcover,hdis⟩ := hS
  have hconn (i : Fin m) : IsConnected ((P i).boundary ℝ) := by
    obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hP i).2 (hP i).1
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  have hcount := Poincare.Topology.card_connectedComponents_of_finite_closed_cover
    (fun i => (P i).boundary ℝ) (fun i => (P i).isClosed_boundary) hconn hdis hcover.symm
  have hcm : Nat.card (ConnectedComponents S) = m := by simpa using hcount
  constructor
  · intro hz
    have hm : m = 0 := hcm.symm.trans hz
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i,_⟩ := mem_iUnion.mp (hcover.subset hx)
    have := i.isLt
    omega
  · intro hzero
    by_contra hne
    have hm : 0 < m := by omega
    obtain ⟨x,hx⟩ := (hconn ⟨0,hm⟩).nonempty
    have hxS := hcover.symm.subset (mem_iUnion_of_mem ⟨0,hm⟩ hx)
    simp only [hzero,mem_empty_iff_false] at hxS

theorem component_count_after_closed_connected_deletion
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (C : I → Set X) (hclosed : ∀ i, IsClosed (C i))
    (hconn : ∀ i, IsConnected (C i))
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    {S L : Set X} (hcover : (⋃ i, C i) = S)
    (hLS : L ⊆ S) (hL : IsConnected L) (hLc : IsClosed L)
    (hrem : IsClosed (S \ L)) :
    Nat.card (ConnectedComponents ↥(S \ L)) + 1 =
      Nat.card (ConnectedComponents S) := by
  classical
  obtain ⟨x,hx⟩ := hL.nonempty
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover.superset (hLS hx))
  have hcomponent := Poincare.Topology.connectedComponentIn_eq_of_finite_closed_cover
    C hclosed (fun i => (hconn i).isPreconnected) hdis hcover hj
  have hLC : L ⊆ C j := hcomponent ▸ hL.isPreconnected.subset_connectedComponentIn hx hLS
  have hCjS : C j ⊆ S := fun _ hz => hcover.subset (mem_iUnion_of_mem j hz)
  have hCL : C j ⊆ L := by
    have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp
      (hconn j).isPreconnected L (S \ L) hLc hrem
      (fun z hz => by
        by_cases hzL : z ∈ L
        · exact Or.inl hzL
        · exact Or.inr ⟨hCjS hz,hzL⟩)
      (by simp only [inter_sdiff_self, inter_empty])
    rcases hsplit with h | h
    · exact h
    · exact False.elim ((h hj).2 hx)
  have hLj : L = C j := Subset.antisymm hLC hCL
  have hrest : (⋃ i : {i : I // i ≠ j}, C i) = S \ L := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi⟩ := mem_iUnion.mp hz
      refine ⟨hcover.subset (mem_iUnion_of_mem i.val hi),?_⟩
      rw [hLj]
      exact fun h => disjoint_left.mp (hdis i.property) hi h
    · rintro ⟨hz,hzL⟩
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hcover.superset hz)
      have hij : i ≠ j := by
        intro he
        exact hzL (hLj.symm ▸ (he ▸ hi))
      exact mem_iUnion_of_mem ⟨i,hij⟩ hi
  rw [Poincare.Topology.card_connectedComponents_of_finite_closed_cover
    (fun i : {i : I // i ≠ j} => C i) (fun i => hclosed i) (fun i => hconn i)
    (fun i k hik => hdis (fun h => hik (Subtype.ext h))) hrest,
    Poincare.Topology.card_connectedComponents_of_finite_closed_cover C hclosed hconn hdis hcover]
  let _ := Fintype.ofFinite I
  have hcount : Nat.card {i : I // i ≠ j} = Nat.card I - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simpa only [Fintype.card_subtype_eq] using
      Fintype.card_subtype_compl (fun i : I => i = j)
  have hpos : 0 < Nat.card I := Finite.card_pos_iff.mpr ⟨j⟩
  omega

theorem cocore_component_count_after_polygon_deletion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : HasDisjointPolygonPresentation S)
    {n : ℕ} (L : Polygon E (n + 3))
    (hinj : Function.Injective L) (hedges : L.HasSimplicialEdges)
    (hLS : L.boundary ℝ ⊆ S) (hrem : IsCompact (S \ L.boundary ℝ)) :
    Nat.card (ConnectedComponents ↥(S \ L.boundary ℝ)) + 1 =
      Nat.card (ConnectedComponents S) := by
  obtain ⟨m,k,P,hP,hcover,hdis⟩ := hS
  have hconn (i : Fin m) : IsConnected ((P i).boundary ℝ) := by
    obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hP i).2 (hP i).1
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  have hL : IsConnected (L.boundary ℝ) := by
    obtain ⟨e⟩ := L.nonempty_boundary_homeomorph_circle hedges hinj
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  exact component_count_after_closed_connected_deletion (fun i => (P i).boundary ℝ)
    (fun i => (P i).isClosed_boundary) hconn hdis hcover.symm hLS hL
    L.isClosed_boundary hrem.isClosed

theorem cocore_component_count_closed_partition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S A B : Set E} (hS : HasDisjointPolygonPresentation S)
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B) (hcover : A ∪ B = S) :
    Nat.card (ConnectedComponents A) + Nat.card (ConnectedComponents B) =
      Nat.card (ConnectedComponents S) := by
  classical
  obtain ⟨m,k,P,hP,hScover,hPdis⟩ := hS
  obtain ⟨I,hI,hIc,hIpair,hIcpair⟩ := Polygon.exists_disjoint_polygon_family_of_closed_cut
    k P (fun i => (hP i).2) (fun i => (hP i).1) hPdis hA hB hdis
    (hcover.trans hScover)
  have hconn (i : Fin m) : IsConnected ((P i).boundary ℝ) := by
    obtain ⟨e⟩ := (P i).nonempty_boundary_homeomorph_circle (hP i).2 (hP i).1
    exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mpr inferInstance)
  rw [Poincare.Topology.card_connectedComponents_of_finite_closed_cover
    (fun i : I => (P i).boundary ℝ) (fun i => (P i).isClosed_boundary)
    (fun i => hconn i) hIpair hI.symm,
    Poincare.Topology.card_connectedComponents_of_finite_closed_cover
    (fun i : (Iᶜ : Set (Fin m)) => (P i).boundary ℝ) (fun i => (P i).isClosed_boundary)
    (fun i => hconn i) hIcpair hIc.symm,
    Poincare.Topology.card_connectedComponents_of_finite_closed_cover
    (fun i => (P i).boundary ℝ) (fun i => (P i).isClosed_boundary)
    hconn hPdis hScover.symm, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.Set.sumCompl I)

theorem cocore_component_counts_after_circle_surgery
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S A B : Set E} (hS : HasDisjointPolygonPresentation S)
    {n : ℕ} (L : Polygon E (n + 3))
    (hinj : Function.Injective L) (hedges : L.HasSimplicialEdges)
    (hLS : L.boundary ℝ ⊆ S) (hrem : IsCompact (S \ L.boundary ℝ))
    (hA : IsClosed A) (hB : IsClosed B) (hdis : Disjoint A B)
    (hcover : A ∪ B = S \ L.boundary ℝ) :
    Nat.card (ConnectedComponents A) + Nat.card (ConnectedComponents B) + 1 =
        Nat.card (ConnectedComponents S) ∧
      Nat.card (ConnectedComponents A) < Nat.card (ConnectedComponents S) ∧
      Nat.card (ConnectedComponents B) < Nat.card (ConnectedComponents S) := by
  have hwhole : L.boundary ℝ ∪ (S \ L.boundary ℝ) = S := union_sdiff_cancel hLS
  have hp := (hwhole.symm ▸ hS).closed_cut L.isClosed_boundary hrem.isClosed
    disjoint_sdiff_right
  have hdelete := cocore_component_count_after_polygon_deletion hS L hinj hedges hLS hrem
  have hpartition := cocore_component_count_closed_partition hp.2 hA hB hdis hcover
  omega

theorem exists_innermost_disk_with_component_decrease
    {T U Z : Set (Fin 3 → ℝ)} (h : HasDisjointPolygonPresentation ((T ∩ U) ∩ Z))
    (hU : Convex ℝ U) (hinside : (T ∩ U) ∩ Z ⊆ interior U)
    (a : (ℝ × ℝ) →ᴬ[ℝ] (Fin 3 → ℝ)) (r : (Fin 3 → ℝ) →ᴬ[ℝ] (ℝ × ℝ))
    (hleft : Function.LeftInverse r a) (hright : LeftInvOn a r Z)
    (ha : MapsTo a univ Z) (hne : ((T ∩ U) ∩ Z).Nonempty) :
    ∃ (n : ℕ) (L : Polygon (Fin 3 → ℝ) (n + 3)) (B : Set (Fin 3 → ℝ)),
      Function.Injective L ∧ L.HasSimplicialEdges ∧
      IsFinitePLBallPair (ℝ × ℝ) B (L.boundary ℝ) ∧
      B ⊆ interior U ∩ Z ∧ B ∩ T = L.boundary ℝ ∧
      IsCompact (((T ∩ U) ∩ Z) \ L.boundary ℝ) ∧
      Nat.card (ConnectedComponents ↥(((T ∩ U) ∩ Z) \ L.boundary ℝ)) + 1 =
        Nat.card (ConnectedComponents ↥((T ∩ U) ∩ Z)) := by
  obtain ⟨n,L,B,hi,he,hB,hsub,hmeet,hrem⟩ :=
    exists_innermost_disk_in_convex_section_with_polygon h hU hinside a r hleft hright ha hne
  refine ⟨n,L,B,hi,he,hB,hsub,hmeet,hrem,?_⟩
  apply cocore_component_count_after_polygon_deletion h L hi he _ hrem
  intro x hx
  have hxB := hB.1 hx
  exact ⟨⟨(hmeet.symm.subset hx).2,interior_subset (hsub hxB).1⟩,(hsub hxB).2⟩

end PoincareConjecture.M76
