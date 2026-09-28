import PoincareConjecture.Proofs.M39.Remark15_13_Separation
import PoincareConjecture.Proofs.M39.Prop15_12_BranchData
import PoincareConjecture.Proofs.M39.Mathlib.CollaredSeparation
import PoincareConjecture.Proofs.M39.Mathlib.RootedSeparation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M39

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  (I : RepairedComparisonMapInput D T hT)

local notation "E" => D.flow.event T hT

theorem comparisonBranches_nonempty : Nonempty (ComparisonBranches I) := by
  classical
  have : ConnectedSpace I.parent.carrier.carrier :=
    connectedSpace_iff_univ.mpr I.parent.connected
  have : LocallyConnectedSpace I.parent.carrier.carrier :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) _
  have hex (i : rootCaps I) :
      ∃ V W : Set I.parent.carrier.carrier,
        IsOpen V ∧ IsOpen W ∧ IsConnected V ∧ IsConnected W ∧
        parentNeckRegion E i.1 I.parent 0 ((E).necks i.1).neck.epsilon⁻¹ ⊆ V ∧
        parentNeckRegion E i.1 I.parent (-((E).necks i.1).neck.epsilon⁻¹) 0 ⊆ W ∧
        Disjoint V W ∧ V ∪ W = (parentNeckSphere E i.1 I.parent)ᶜ ∧
        frontier V = parentNeckSphere E i.1 I.parent ∧
        frontier W = parentNeckSphere E i.1 I.parent := by
    obtain ⟨hS, hSne, hU, hSU, hsplit, hN, hP, hSN, hSP⟩ :=
      parentNeck_collarData E i.1 I.parent
        (rootCap_parentSphere_nonempty I i.1 i.2)
    apply exists_separating_components_of_collar hS hSne hU hSU hsplit hN hP hSN hSP
    simpa only [← compl_eq_univ_sdiff, parentSphere, parentNeckSphere, preNeckSphere] using
      (rootCap_parentSphere_separating I i.1 i.2).2
  choose V W hV hW hVconn hWconn hPV hNW hVW hcover hVfront hWfront using hex
  have hsroot (i : rootCaps I) :
      parentNeckSphere E i.1 I.parent ⊆ retainedRoot I := by
    intro x hx
    exact rootCap_preSphere_subset I i.1 i.2 hx
  have hnroot (i : rootCaps I) :
      parentNeckRegion E i.1 I.parent (-((E).necks i.1).neck.epsilon⁻¹) 0 ⊆
        retainedRoot I := by
    intro x hx
    exact rootCap_negative_subset_root I i.1 i.2 hx
  have hproot (i : rootCaps I) :
      Disjoint (parentNeckRegion E i.1 I.parent 0 ((E).necks i.1).neck.epsilon⁻¹)
        (retainedRoot I) := by
    apply Set.disjoint_left.mpr
    intro x hxP hxA
    exact Set.disjoint_left.mp (positive_neck_disjoint_root I i.1) hxP hxA
  have hroot (i : rootCaps I) : Disjoint (V i) (retainedRoot I) := by
    obtain ⟨_, hSne, hU, hSU, hsplit, _, _, _, _⟩ :=
      parentNeck_collarData E i.1 I.parent
        (rootCap_parentSphere_nonempty I i.1 i.2)
    have havoid : Disjoint (retainedRoot I ∩ V i) (parentNeckCarrier E i.1 I.parent) := by
      apply Set.disjoint_left.mpr
      rintro x ⟨hxA, hxV⟩ hxU
      have hxS : x ∉ parentNeckSphere E i.1 I.parent :=
        (hcover i).subset (Or.inl hxV)
      rcases hsplit.subset ⟨hxU, hxS⟩ with hxN | hxP
      · exact Set.disjoint_left.mp (hVW i) hxV (hNW i hxN)
      · exact Set.disjoint_left.mp (hproot i) hxP hxA
    have hout : (retainedRoot I \ V i).Nonempty := by
      obtain ⟨x, hxS⟩ := hSne
      exact ⟨x, hsroot i hxS, fun hxV => (hcover i).subset (Or.inl hxV) hxS⟩
    have hfront : frontier (V i) ⊆ parentNeckCarrier E i.1 I.parent := by
      rw [hVfront i]
      exact hSU
    exact ((retainedRoot_isConnected I).isPreconnected.disjoint_of_frontier_neighborhood
      (retainedRoot_isClosed I) (hV i) hU hfront havoid hout).symm
  have hfrontroot (i : rootCaps I) : frontier (V i) ⊆ retainedRoot I := by
    rw [hVfront i]
    exact hsroot i
  have hfrontne (i : rootCaps I) : (frontier (V i)).Nonempty := by
    rw [hVfront i]
    exact rootCap_parentSphere_nonempty I i.1 i.2
  have hfrontdisj : Pairwise (fun i j => Disjoint (frontier (V i)) (frontier (V j))) := by
    intro i j hij
    rw [hVfront i, hVfront j]
    exact parentSphere_disjoint I i.1 j.1 (fun h => hij (Subtype.ext h))
  have hdisjoint : Pairwise (fun i j => Disjoint (V i) (V j)) :=
    pairwise_disjoint_of_frontier_subset_root V hV (fun i => (hVconn i).isPreconnected)
      hroot hfrontroot hfrontne hfrontdisj
  have hrootfront : frontier (retainedRoot I) =
      ⋃ i : rootCaps I, parentNeckSphere E i.1 I.parent := by
    simpa only [iUnion_subtype, parentNeckSphere, preNeckSphere, parentSphere] using
      frontier_retainedRoot I
  have hfull (i : rootCaps I) :
      parentNeckCarrier E i.1 I.parent ⊆ retainedRoot I ∪ V i := by
    obtain ⟨_, _, _, _, hsplit, _, _, _, _⟩ :=
      parentNeck_collarData E i.1 I.parent
        (rootCap_parentSphere_nonempty I i.1 i.2)
    intro x hxU
    by_cases hxS : x ∈ parentNeckSphere E i.1 I.parent
    · exact Or.inl (hsroot i hxS)
    · rcases hsplit.subset ⟨hxU, hxS⟩ with hxN | hxP
      · exact Or.inl (hnroot i hxN)
      · exact Or.inr (hPV i hxP)
  have htotal : retainedRoot I ∪ ⋃ i, V i = univ := by
    apply root_union_outward_eq_univ (retainedRoot_isClosed I)
      (retainedRoot_isConnected I).nonempty V hV hfrontroot
    intro x hx
    rw [hrootfront] at hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨_, _, hU, hSU, _, _, _, _, _⟩ :=
      parentNeck_collarData E i.1 I.parent
        (rootCap_parentSphere_nonempty I i.1 i.2)
    exact ⟨i, Filter.mem_of_superset (hU.mem_nhds (hSU hxi)) (hfull i)⟩
  exact ⟨{
    caps := rootCaps I
    root := retainedRoot I
    root_closed := retainedRoot_isClosed I
    retained_eq := retained_eq_interior_root I
    outward := V
    outward_open := hV
    outward_disjoint_root := hroot
    outward_disjoint := hdisjoint
    cover := htotal
    frontier_root := hrootfront
    negative_root := hnroot
    positive_outward := hPV
    local_output_in_child := fun i => rootCap_local_output_in_child I i.1 i.2
  }⟩

end PoincareConjecture.M39
