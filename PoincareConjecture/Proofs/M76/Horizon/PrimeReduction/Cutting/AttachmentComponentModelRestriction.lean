import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.SelectedBoundaryReplacementModels
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.TwoPortComponentCarriers










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem component_models_of_two_port_attachment
    {X E ι : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {e : ι → OpenPartialHomeomorph X V3} {f : X → E} {Q H Z N : Set X}
    (hQ : IsCompact Q) (hQPL : PLDomain e Q) (hH : IsCompact H) (hHconn : IsConnected H)
    (hAPL : PLDomain e (Q ∪ H))
    (cap : Bool → Set X) (hcapconn : ∀ b, IsConnected (cap b))
    (hcontact : Q ∩ H = cap false ∪ cap true)
    (a : Bool → X) (ha : ∀ b, a b ∈ cap b)
    (p : Bool → Set X) (sp : ∀ b, ChartwisePLSphere e (p b))
    (hpdis : Disjoint (p false) (p true)) (hcapP : ∀ b, cap b ⊆ p b)
    (hZ : IsClosed Z) (hHZ : Disjoint H Z)
    (hpZ : ∀ b, Disjoint (p b) Z) (hN : IsConnected N) (hNc : IsClosed N)
    (hNZ : Disjoint N Z) (hNH : (N ∩ H).Nonempty)
    (hQfront : frontier Q = Z ∪ (p false ∪ p true))
    (hAfront : frontier (Q ∪ H) = Z ∪ N)
    (K : SimplicialComplex ℝ E) (g : E → X)
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hreal : ∀ x ∈ connectedComponentIn (Q ∪ H) (a false), f x ∈ K.space ∧ g (f x) = x)
    (hm : HasPuncturedSphereModel e f (connectedComponentIn (Q ∪ H) (a false))) :
    ∀ b, HasPuncturedSphereModel e f (connectedComponentIn Q (a b)) := by
  classical
  let D := fun b => connectedComponentIn Q (a b)
  let C := connectedComponentIn (Q ∪ H) (a false)
  let Q' := D false ∪ D true
  let T := Q' ∩ Z
  have hcapQ (b : Bool) : cap b ⊆ Q := by
    intro x hx
    apply (hcontact.symm.subset ?_).1
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have haQ (b : Bool) := hcapQ b (ha b)
  let : LocallyPathConnectedSpace Q := hQPL.locallyPathConnectedSpace
  have hrec : C = Q' ∪ H :=
    (Topology.componentIn_closed_attachment_of_two_connected_ports hQ.isClosed hH.isClosed
      hHconn (hcapconn false) (hcapconn true) hcontact (ha false) (ha true)).1
  have hCcompact : IsCompact C := isCompact_connectedComponentIn_of_mem
    (hQ.union hH) (Or.inl (haQ false))
  have hHC : H ⊆ C := subset_union_right.trans hrec.symm.subset
  have hNA : N ⊆ Q ∪ H :=
    (subset_union_right.trans hAfront.symm.subset).trans (hQ.union hH).isClosed.frontier_subset
  have hNC : N ⊆ C := by
    obtain ⟨x, hxN, hxH⟩ := hNH
    have hxC := hHC hxH
    change N ⊆ connectedComponentIn (Q ∪ H) (a false)
    rw [connectedComponentIn_eq hxC]
    exact hN.isPreconnected.subset_connectedComponentIn hxN hNA
  have hDc (b : Bool) : IsCompact (D b) := isCompact_connectedComponentIn_of_mem hQ (haQ b)
  have hQ'c : IsCompact Q' := (hDc false).union (hDc true)
  have hQ'Q : Q' ⊆ Q := union_subset (connectedComponentIn_subset _ _)
    (connectedComponentIn_subset _ _)
  have hQ'o : IsOpen ((Subtype.val : Q → X) ⁻¹' Q') := by
    rw [preimage_union]
    exact (isOpen_preimage_connectedComponentIn (haQ false)).union
      (isOpen_preimage_connectedComponentIn (haQ true))
  have hQ'PL := hQPL.of_relative_clopen_subset hQ'Q hQ'c.isClosed hQ'o
  have hQ'C : Q' ⊆ C := subset_union_left.trans hrec.symm.subset
  have hQ'f : frontier Q' = Q' ∩ frontier Q := by
    obtain ⟨O, hO, hQ'O⟩ := exists_open_inter_of_relative_open hQ'Q hQ'o
    exact frontier_eq_inter_of_eq_inter_open hQ.isClosed hQ'c.isClosed hO hQ'O
  have hpQ (b : Bool) : p b ⊆ Q := by
    apply subset_trans _ hQ.isClosed.frontier_subset
    rw [hQfront]
    cases b
    · exact subset_union_of_subset_right subset_union_left _
    · exact subset_union_of_subset_right subset_union_right _
  have hpD (b : Bool) : p b ⊆ D b :=
    (sp b).isConnected.isPreconnected.subset_connectedComponentIn (hcapP b (ha b)) (hpQ b)
  have hpQ' (b : Bool) : p b ⊆ Q' := by
    cases b
    · exact (hpD false).trans subset_union_left
    · exact (hpD true).trans subset_union_right
  have hnewfront : frontier Q' = T ∪ ⋃ b, p b := by
    rw [hQ'f, hQfront]
    apply Subset.antisymm
    · rintro x ⟨hx, hz | hp0 | hp1⟩
      · exact Or.inl ⟨hx, hz⟩
      · exact Or.inr (mem_iUnion.mpr ⟨false, hp0⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨true, hp1⟩)
    · rintro x (⟨hx, hz⟩ | hx)
      · exact ⟨hx, Or.inl hz⟩
      · obtain ⟨b, hb⟩ := mem_iUnion.mp hx
        refine ⟨hpQ' b hb, Or.inr ?_⟩
        cases b
        · exact Or.inl hb
        · exact Or.inr hb
  have hCf : frontier C = C ∩ frontier (Q ∪ H) := by
    let : LocallyPathConnectedSpace (Q ∪ H : Set X) := hAPL.locallyPathConnectedSpace
    obtain ⟨O, hO, hCO⟩ := exists_open_inter_of_relative_open
      (connectedComponentIn_subset (Q ∪ H) (a false))
      (isOpen_preimage_connectedComponentIn (Or.inl (haQ false)))
    exact frontier_eq_inter_of_eq_inter_open (hQ.union hH).isClosed hCcompact.isClosed hO hCO
  have hCZ : C ∩ Z = T := by
    rw [hrec, union_inter_distrib_right, hHZ.inter_eq, union_empty]
  have hparentfront : frontier C = N ∪ T := by
    rw [hCf, hAfront, inter_union_distrib_left, hCZ, inter_eq_right.mpr hNC, union_comm]
  have hppair : Pairwise fun b c => Disjoint (p b) (p c) := by
    intro b c hbc
    cases b <;> cases c
    · exact False.elim (hbc rfl)
    · exact hpdis
    · exact hpdis.symm
    · exact False.elim (hbc rfl)
  have hmodels := hm.component_models_of_selected_boundary_replacement hCcompact.isClosed
    hQ'c hQ'PL hQ'C K g hg hgi hreal hN hNc (hQ'c.isClosed.inter hZ)
    (hNZ.mono_right inter_subset_right) hparentfront p sp hppair
    (fun b => (hpZ b).mono_right inter_subset_right) hnewfront
  intro b
  have haQ' : a b ∈ Q' := hpQ' b (hcapP b (ha b))
  have hcomponent : connectedComponentIn Q' (a b) = D b := by
    apply Subset.antisymm
    · exact connectedComponentIn_mono _ hQ'Q
    · have hDsub : D b ⊆ Q' := by
        cases b
        · exact subset_union_left
        · exact subset_union_right
      exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
        (mem_connectedComponentIn (haQ b)) hDsub
  change HasPuncturedSphereModel e f (D b)
  exact hcomponent ▸ hmodels (a b) haQ'

end PoincareConjecture.M76
