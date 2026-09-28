import PoincareConjecture.Proofs.M39.Prop15_12_BranchData
import PoincareConjecture.Proofs.M39.Prop15_12_ExtensionData
import PoincareConjecture.Proofs.M39.Prop15_12_MapConstruction
import PoincareConjecture.Proofs.M36.MetricComparison

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M39

section Coordinates

variable {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
  {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
  (E : SurgeryEventData g₀ K P slice metric T)

private def parentHeight (i : Fin (E).cap_count)
    (C : SurgerySelectedComponent (slice (E).tMinus)) (x : C.carrier.carrier) : ℝ :=
  (((E).necks i).neck.coordinate_inverse ((E).limit_identify.map (C.inclusion x))).2

private theorem parentRegion_iff (i : Fin (E).cap_count)
    (C : SurgerySelectedComponent (slice (E).tMinus)) (a b : ℝ)
    (x : C.carrier.carrier) :
    x ∈ parentNeckRegion E i C a b ↔
      C.inclusion x ∈ (E).regular_limit ∧
      (E).limit_identify.map (C.inclusion x) ∈ ((E).necks i).neck.carrier ∧
      a < parentHeight E i C x ∧ parentHeight E i C x < b := by
  change C.inclusion x ∈ (E).limit_identify.inverse '' ((E).necks i).neck.region a b ↔ _
  rw [limitInverse_image_eq E]
  rfl

private theorem parentCarrier_iff (i : Fin (E).cap_count)
    (C : SurgerySelectedComponent (slice (E).tMinus)) (x : C.carrier.carrier) :
    x ∈ parentNeckCarrier E i C ↔
      C.inclusion x ∈ (E).regular_limit ∧
      (E).limit_identify.map (C.inclusion x) ∈ ((E).necks i).neck.carrier := by
  change C.inclusion x ∈ (E).limit_identify.inverse '' ((E).necks i).neck.carrier ↔ _
  rw [limitInverse_image_eq E]
  rfl

private theorem parentSphere_iff (i : Fin (E).cap_count)
    (C : SurgerySelectedComponent (slice (E).tMinus)) (x : C.carrier.carrier) :
    x ∈ parentNeckSphere E i C ↔
      C.inclusion x ∈ (E).regular_limit ∧
      (E).limit_identify.map (C.inclusion x) ∈ ((E).necks i).neck.carrier ∧
      parentHeight E i C x = 0 := by
  change C.inclusion x ∈ (E).limit_identify.inverse '' ((E).necks i).neck.central_sphere ↔ _
  rw [limitInverse_image_eq E]
  change (_ ∧ _ ∈ ((E).necks i).neck.central_sphere) ↔ _
  rw [M36.neck_central_iff]
  rfl

end Coordinates

section Gluing

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  (I : RepairedComparisonMapInput D T hT)

local notation "E" => D.flow.event T hT

theorem comparisonExtension_of_branches (B : ComparisonBranches I) :
    Nonempty (ComparisonExtension I) := by
  classical
  choose b hb hbell htail using localComparison_constant_tail E
  let c : Fin (E).cap_count → ℝ := fun i => (b i + ((E).necks i).neck.epsilon⁻¹) / 2
  have hbc (i : Fin (E).cap_count) : b i < c i := by
    dsimp [c]
    linarith [hbell i]
  have hc0 (i : Fin (E).cap_count) : 0 < c i := (hb i).trans (hbc i)
  have hcell (i : Fin (E).cap_count) : c i < ((E).necks i).neck.epsilon⁻¹ := by
    dsimp [c]
    linarith [hbell i]
  have hell (i : Fin (E).cap_count) : 0 < ((E).necks i).neck.epsilon⁻¹ :=
    (hb i).trans (hbell i)
  let neck (i : B.caps) : Set I.parent.carrier.carrier :=
    parentNeckRegion E i.1 I.parent (-((E).necks i.1).neck.epsilon⁻¹) (c i.1)
  let tail (i : B.caps) : Set I.parent.carrier.carrier :=
    B.outward i \ I.parent.inclusion ⁻¹' positiveNeckControl E i.1 (b i.1)
  have hretRoot : I.retained ⊆ B.root := by
    rw [B.retained_eq]
    exact interior_subset
  have hsphereFront (i : B.caps) :
      parentNeckSphere E i.1 I.parent ⊆ frontier B.root := by
    intro x hx
    rw [B.frontier_root]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hnegativeRetained (i : B.caps) :
      parentNeckRegion E i.1 I.parent (-((E).necks i.1).neck.epsilon⁻¹) 0 ⊆ I.retained := by
    rw [B.retained_eq]
    exact interior_maximal (B.negative_root i)
      (parentNeckRegion_isOpen E i.1 I.parent _ _)
  have hneckCarrier (i : B.caps) : neck i ⊆ parentNeckCarrier E i.1 I.parent :=
    preimage_mono (preNeckRegion_subset_carrier E i.1 _ _)
  have hneckBranch (i : B.caps) (x : I.parent.carrier.carrier)
      (hx : x ∈ parentNeckCarrier E i.1 I.parent) : x ∈ B.root ∨ x ∈ B.outward i := by
    have hm := (parentCarrier_iff E i.1 I.parent x).mp hx
    have hheight := (((E).necks i.1).neck.coordinate_inverse_mem _ hm.2).2
    rcases lt_trichotomy (parentHeight E i.1 I.parent x) 0 with hneg | hzero | hpos
    · exact Or.inl (B.negative_root i ((parentRegion_iff E i.1 I.parent _ _ x).mpr
        ⟨hm.1, hm.2, hheight.1, hneg⟩))
    · exact Or.inl (B.root_closed.frontier_subset (hsphereFront i
        ((parentSphere_iff E i.1 I.parent x).mpr ⟨hm.1, hm.2, hzero⟩)))
    · exact Or.inr (B.positive_outward i ((parentRegion_iff E i.1 I.parent _ _ x).mpr
        ⟨hm.1, hm.2, hpos, hheight.2⟩))
  have hneckIndex (i j : B.caps) (x : I.parent.carrier.carrier)
      (hx : x ∈ neck i) (hy : x ∈ B.outward j) : i = j := by
    by_contra hij
    rcases hneckBranch i x (hneckCarrier i hx) with hxroot | hxi
    · exact Set.disjoint_left.mp (B.outward_disjoint_root j) hy hxroot
    · exact Set.disjoint_left.mp (B.outward_disjoint hij) hxi hy
  have hretNeck (i : B.caps) (x : I.parent.carrier.carrier)
      (hr : x ∈ I.retained) (hn : x ∈ neck i) :
      localChildComparison E i.1 I.child (I.parent.inclusion x) = retainedMap I x := by
    have hm := (parentRegion_iff E i.1 I.parent _ _ x).mp hn
    have hneg : parentHeight E i.1 I.parent x < 0 := by
      by_contra hnot
      rcases (le_of_not_gt hnot).eq_or_lt with hzero | hpos
      · have hf := hsphereFront i ((parentSphere_iff E i.1 I.parent x).mpr
          ⟨hm.1, hm.2.1, hzero.symm⟩)
        exact (mem_frontier_iff_notMem_interior (hretRoot hr)).mp hf (B.retained_eq ▸ hr)
      · have hout := B.positive_outward i ((parentRegion_iff E i.1 I.parent _ _ x).mpr
          ⟨hm.1, hm.2.1, hpos, (((E).necks i.1).neck.coordinate_inverse_mem _ hm.2.1).2.2⟩)
        exact Set.disjoint_left.mp (B.outward_disjoint_root i) hout (hretRoot hr)
    exact localChildComparison_eq_retention E i.1 I.child hm.1
      ⟨hm.2.1, hm.2.2.1, hneg⟩
  have hneckTail (i j : B.caps) (x : I.parent.carrier.carrier)
      (hn : x ∈ neck i) (ht : x ∈ tail j) :
      localChildComparison E i.1 I.child (I.parent.inclusion x) =
        I.child.inverse ((E).caps j.1).tip := by
    have hij := hneckIndex i j x hn ht.1
    subst j
    have hm := (parentRegion_iff E i.1 I.parent _ _ x).mp hn
    have hzero : 0 ≤ parentHeight E i.1 I.parent x := by
      by_contra hnot
      have hroot := B.negative_root i ((parentRegion_iff E i.1 I.parent _ _ x).mpr
        ⟨hm.1, hm.2.1, hm.2.2.1, lt_of_not_ge hnot⟩)
      exact Set.disjoint_left.mp (B.outward_disjoint_root i) ht.1 hroot
    have hbig : b i.1 < parentHeight E i.1 I.parent x := by
      by_contra hnot
      exact ht.2 ((mem_positiveNeckControl_iff E i.1 (hbell i.1)).mpr
        ⟨hm.1, hm.2.1, hzero, le_of_not_gt hnot⟩)
    exact congrArg I.child.inverse (htail i.1 (I.parent.inclusion x) hm.2.1 hbig.le)
  have hretTail (i : B.caps) : Disjoint I.retained (tail i) :=
    (B.outward_disjoint_root i).symm.mono hretRoot sdiff_subset
  have hneckDisjoint : Pairwise (fun i j : B.caps => Disjoint (neck i) (neck j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hi := (parentRegion_iff E i.1 I.parent _ _ x).mp hxi
    have hj := (parentRegion_iff E j.1 I.parent _ _ x).mp hxj
    exact Set.disjoint_left.mp
      ((E).neck_carrier_disjoint i.1 j.1 (fun heq => hij (Subtype.ext heq))) hi.2.1 hj.2.1
  have htailDisjoint : Pairwise (fun i j : B.caps => Disjoint (tail i) (tail j)) :=
    fun _ _ hij => (B.outward_disjoint hij).mono sdiff_subset sdiff_subset
  let domains : Option (B.caps ⊕ B.caps) → Set I.parent.carrier.carrier
    | none => I.retained
    | some (.inl i) => neck i
    | some (.inr i) => tail i
  let formulas : Option (B.caps ⊕ B.caps) →
      I.parent.carrier.carrier → I.child.carrier.carrier
    | none => retainedMap I
    | some (.inl i) => localChildComparison E i.1 I.child ∘ I.parent.inclusion
    | some (.inr i) => fun _ => I.child.inverse ((E).caps i.1).tip
  have hopen : ∀ j, IsOpen (domains j) := by
    rintro (_ | (i | i))
    · exact I.retained_open
    · exact parentNeckRegion_isOpen E i.1 I.parent _ _
    · exact (B.outward_open i).sdiff
        ((positiveNeckControl_compact E i.1 (hbell i.1)).isClosed.preimage
          I.parent.inclusion_openEmbedding.continuous)
  have hcontinuous : ∀ j, ContinuousOn (formulas j) (domains j) := by
    rintro (_ | (i | i))
    · exact (retainedMap_smooth I).continuousOn
    · apply (localChildComparison_continuousOn E i.1 I.child
        (B.local_output_in_child i)).comp I.parent.inclusion_smooth.continuous.continuousOn
      intro x hx
      have hm := (parentRegion_iff E i.1 I.parent _ _ x).mp hx
      exact ⟨hm.1, hm.2.1⟩
    · exact continuousOn_const
  have hcompatible : ∀ i j x, x ∈ domains i → x ∈ domains j →
      formulas i x = formulas j x := by
    intro i j x hxi hxj
    rcases i with _ | (i | i) <;> rcases j with _ | (j | j)
    · rfl
    · exact (hretNeck j x hxi hxj).symm
    · exact (Set.disjoint_left.mp (hretTail j) hxi hxj).elim
    · exact hretNeck i x hxj hxi
    · by_cases hij : i = j
      · subst j
        rfl
      · exact (Set.disjoint_left.mp (hneckDisjoint hij) hxi hxj).elim
    · exact hneckTail i j x hxi hxj
    · exact (Set.disjoint_left.mp (hretTail i) hxj hxi).elim
    · exact (hneckTail j i x hxj hxi).symm
    · by_cases hij : i = j
      · subst j
        rfl
      · exact (Set.disjoint_left.mp (htailDisjoint hij) hxi hxj).elim
  have hcover : ∀ x, ∃ j, x ∈ domains j := by
    intro x
    by_cases hr : x ∈ I.retained
    · exact ⟨none, hr⟩
    have hx : x ∈ B.root ∪ ⋃ i, B.outward i := B.cover.symm ▸ mem_univ x
    rcases hx with hxroot | hxout
    · have hf : x ∈ frontier B.root :=
        (mem_frontier_iff_notMem_interior hxroot).mpr (by rwa [← B.retained_eq])
      rw [B.frontier_root] at hf
      obtain ⟨i, hi⟩ := mem_iUnion.mp hf
      have hm := (parentSphere_iff E i.1 I.parent x).mp hi
      refine ⟨some (.inl i), (parentRegion_iff E i.1 I.parent _ _ x).mpr ?_⟩
      refine ⟨hm.1, hm.2.1, ?_, ?_⟩
      · rw [hm.2.2]
        exact neg_lt_zero.mpr (hell i.1)
      · rw [hm.2.2]
        exact hc0 i.1
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxout
      by_cases hs : I.parent.inclusion x ∈ positiveNeckControl E i.1 (b i.1)
      · have hm := (mem_positiveNeckControl_iff E i.1 (hbell i.1)).mp hs
        refine ⟨some (.inl i), (parentRegion_iff E i.1 I.parent _ _ x).mpr ?_⟩
        exact ⟨hm.1, hm.2.1, lt_of_lt_of_le (neg_lt_zero.mpr (hell i.1)) hm.2.2.1,
          lt_of_le_of_lt hm.2.2.2 (hbc i.1)⟩
      · exact ⟨some (.inr i), hi, hs⟩
  have hcoverNhds : ∀ x, ∃ j, domains j ∈ 𝓝 x := by
    intro x
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨j, (hopen j).mem_nhds hj⟩
  let pieces (j : Option (B.caps ⊕ B.caps)) :
      ContinuousMap (domains j) I.child.carrier.carrier :=
    ⟨fun x => formulas j x, (hcontinuous j).domRestrict⟩
  have hpieces : ∀ i j x (hi : x ∈ domains i) (hj : x ∈ domains j),
      pieces i ⟨x, hi⟩ = pieces j ⟨x, hj⟩ :=
    fun i j x hi hj => hcompatible i j x hi hj
  let f := ContinuousMap.liftCover domains pieces hpieces hcoverNhds
  have hf : ∀ j x (hx : x ∈ domains j), f x = formulas j x := by
    intro j x hx
    exact ContinuousMap.liftCover_coe (S := domains) (φ := pieces)
      (hφ := hpieces) (hS := hcoverNhds) ⟨x, hx⟩
  have htip (i : Fin (E).cap_count) : ((E).caps i).tip ∈ ((E).caps i).carrier := by
    rw [← ((E).caps i).image]
    refine ⟨0, ?_, ((E).caps i).map_tip⟩
    rw [((E).caps i).domain_eq]
    change D.flow.standard_initial.metric.edist 0 0 ≤ _
    rw [M36.metric_edist_self]
    exact bot_le
  refine ⟨{
    map := f
    retained_agreement := ?_
    outside_image_in_caps := ?_
    control := regularControl E c
    control_compact := regularControl_compact E c hcell
    control_regular := regularControl_subset_regular E c
    local_model := ?_ }⟩
  · intro x hx
    rw [hf none x hx]
    exact inclusion_retainedMap I hx
  · intro x hx
    obtain ⟨j, hj⟩ := hcover x
    rcases j with _ | (i | i)
    · exact (hx hj).elim
    · refine ⟨i.1, ?_⟩
      rw [hf (some (.inl i)) x hj]
      change I.child.inclusion (localChildComparison E i.1 I.child
        (I.parent.inclusion x)) ∈ ((E).caps i.1).carrier
      rw [inclusion_localChildComparison E i.1 I.child (B.local_output_in_child i)]
      have hm := (parentRegion_iff E i.1 I.parent _ _ x).mp hj
      rcases lt_trichotomy (parentHeight E i.1 I.parent x) 0 with hneg | hzero | hpos
      · exact (hx (hnegativeRetained i ((parentRegion_iff E i.1 I.parent _ _ x).mpr
          ⟨hm.1, hm.2.1, hm.2.2.1, hneg⟩))).elim
      · exact localComparison_central_mem_cap E i.1
          ((M36.neck_central_iff _).mpr ⟨hm.2.1, hzero⟩)
      · exact localComparison_positive_mem_cap E i.1
          ⟨hm.2.1, hpos, (((E).necks i.1).neck.coordinate_inverse_mem _ hm.2.1).2.2⟩
    · refine ⟨i.1, ?_⟩
      rw [hf (some (.inr i)) x hj]
      change I.child.inclusion (I.child.inverse ((E).caps i.1).tip) ∈ ((E).caps i.1).carrier
      obtain ⟨y, hy⟩ := cap_tip_mem_child E i.1 I.child (B.local_output_in_child i)
      rw [← hy, I.child.left_inverse, hy]
      exact htip i.1
  · intro x
    obtain ⟨j, hj⟩ := hcover x
    refine ⟨domains j, hopen j, hj, ?_⟩
    rcases j with _ | (i | i)
    · right
      refine ⟨fun y hy => retained_pre_subset_regularControl E c
        (interior_subset (I.retained_subset y hy)), Or.inl subset_rfl⟩
    · right
      refine ⟨fun y hy => regularControl_contains_neck_region E c i.1 hy, Or.inr ?_⟩
      refine ⟨i.1, B.local_output_in_child i, ?_, ?_⟩
      · intro y hy
        exact ((parentRegion_iff E i.1 I.parent _ _ y).mp hy).2.1
      · intro y hy
        exact hf (some (.inl i)) y hy
    · left
      exact ⟨I.child.inverse ((E).caps i.1).tip, fun y hy => hf (some (.inr i)) y hy⟩

end Gluing

end PoincareConjecture.M39
