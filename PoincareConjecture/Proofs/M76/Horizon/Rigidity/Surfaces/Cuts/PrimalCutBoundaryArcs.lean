import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalDiskSpokes
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.JoinedPLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalBoundary









set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}

namespace OriginalPrimalCutDiskData

variable (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)

noncomputable def boundaryBridge (i : Fin 4) :=
  zeroSheet (ι := Fin 4) '' exteriorCopiedBridge K P D hcofaces A.bands A.exteriorHeight
    (exteriorFourIndex K P D labels (A.gaps.bridgeOrder i))

noncomputable def bridgeBegin (i : Fin 4) := zeroSheet (ι := Fin 4) (A.gaps.bridgeStart i)
noncomputable def bridgeEnd (i : Fin 4) := zeroSheet (ι := Fin 4) (A.gaps.bridgeFinish i)
noncomputable def gapCenter (i : Fin 4) := A.sectorCopy (A.matching i) A.sectors.center

noncomputable def boundaryBridgeUnion :=
  zeroSheet (ι := Fin 4) '' complementaryBridgeCopies K P D hcofaces A.bands A.exteriorHeight

theorem sectorCopy_finitePL (i : Fin 4) : FinitePiecewiseAffineOn (A.sectorCopy i) (A.sectors.sector i) :=
  (separatedSheet_finitePL A.freshHeight i (A.freshHeightPL i)).comp
    (heightGraph_finitePL (A.sectorHeightPL i)) (fun _ hx => mem_image_of_mem _ hx)

theorem sectorCopy_injective (i : Fin 4) : Function.Injective (A.sectorCopy i) :=
  graphAttachmentSheet_injective A.sectorHeight A.freshHeight i

theorem sectorCopy_on_rim (i : Fin 4) {x : E} (hx : x ∈ A.sectors.rim i) :
    A.sectorCopy i x = zeroSheet (ι := Fin 4) (heightGraph (A.sectorHeight i) x) := by
  apply (separatedSheet_eq_zeroSheet_iff A.freshHeight i _ _).mpr
  exact ⟨rfl,(A.freshHeight_spec i x ((A.sectors.sector_ball i).1 (Or.inl hx))).2.mpr hx⟩

theorem sectorCopies_pairwise_disjoint :
    Pairwise (fun i j => Disjoint (A.sectorCopy i '' A.sectors.sector i)
      (A.sectorCopy j '' A.sectors.sector j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  have hxy : x = y := congrArg (fun p => p.1.1) (hxz.trans hyz.symm)
  subst y
  exact A.sectors.attached_sector_copies_ne A.sectorHeight A.freshHeight
    (fun i x hx => (A.freshHeight_spec i x hx).2) A.sector_graphs_pairwise_disjoint
    hij hx hy (hxz.trans hyz.symm)

theorem copied_spoke_isFinitePLInterval (i t : Fin 4) (ht : t = i ∨ t = i+1) :
    IsFinitePLBallPair ℝ (A.sectorCopy i '' A.sectors.spoke t)
      {A.sectorCopy i A.sectors.center,
        A.sectorCopy i (originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order t))} := by
  have hsub : A.sectors.spoke t ⊆ A.sectors.sector i := by
    apply Subset.trans ?_ (A.sectors.sector_ball i).1
    rcases ht with rfl | rfl
    · exact subset_union_left.trans subset_union_right
    · exact subset_union_right.trans subset_union_right
  simpa only [image_pair] using (A.sectors.spoke_ball t).image_of_subset
    (A.sectorCopy_finitePL i) hsub (A.sectorCopy_injective i).injOn

theorem copied_spoke_inter_bridges (i t : Fin 4) (ht : t = i ∨ t = i+1) :
    (A.sectorCopy i '' A.sectors.spoke t) ∩ A.boundaryBridgeUnion =
      {A.sectorCopy i (originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order t))} := by
  let m := originalExteriorMarks K P D hcofaces A.bands labels
  have hmrim : m (A.sectors.order t) ∈ A.sectors.rim i := by
    apply (A.sectors.rim_ball i).1
    rcases ht with ht | ht
    · exact Or.inl (congrArg (m ∘ A.sectors.order) ht)
    · exact Or.inr (congrArg (m ∘ A.sectors.order) ht)
  have hsub : A.sectors.spoke t ⊆ A.sectors.sector i := by
    apply Subset.trans ?_ (A.sectors.sector_ball i).1
    rcases ht with rfl | rfl
    · exact subset_union_left.trans subset_union_right
    · exact subset_union_right.trans subset_union_right
  apply Subset.antisymm
  · rintro z ⟨⟨x,hx,rfl⟩,y,hy,heq⟩
    have hh := (separatedSheet_eq_zeroSheet_iff A.freshHeight i _ _).mp heq.symm
    have hxrim := (A.freshHeight_spec i x (hsub hx)).2.mp hh.2
    have hxm : x = m (A.sectors.order t) :=
      (A.sectors.spoke_rim t).subset ⟨hx,A.sectors.rim_subset i hxrim⟩
    exact congrArg (A.sectorCopy i) hxm
  · rintro z rfl
    refine ⟨mem_image_of_mem _ ((A.sectors.spoke_ball t).1 (Or.inr rfl)),?_
      ⟩
    refine ⟨heightGraph (A.sectorHeight i) (m (A.sectors.order t)),?_,
      (A.sectorCopy_on_rim i hmrim).symm⟩
    apply (show _ ⊆ complementaryBridgeCopies K P D hcofaces A.bands A.exteriorHeight from
      (A.bridgeCopies_inter_sectorGraph K P D hD hcofaces labels hP i).symm.subset.trans
        inter_subset_left)
    rcases ht with ht | ht
    · exact Or.inl (congrArg (heightGraph (A.sectorHeight i) ∘ m ∘ A.sectors.order) ht)
    · exact Or.inr (congrArg (heightGraph (A.sectorHeight i) ∘ m ∘ A.sectors.order) ht)

theorem copied_spokes_inter (i : Fin 4) :
    (A.sectorCopy i '' A.sectors.spoke i) ∩ (A.sectorCopy i '' A.sectors.spoke (i+1)) =
      {A.sectorCopy i A.sectors.center} := by
  rw [← Set.image_inter (A.sectorCopy_injective i),A.sectors.spoke_inter i (i+1)
    (by fin_cases i <;> decide),image_singleton]

theorem sector_copied_endpoints (i : Fin 4) :
    ({A.sectorCopy (A.matching i)
        (originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order (A.matching i))),
      A.sectorCopy (A.matching i)
        (originalExteriorMarks K P D hcofaces A.bands labels (A.sectors.order (A.matching i+1)))} : Set _) =
      {A.bridgeEnd i,A.bridgeBegin (i+1)} := by
  rw [A.sectorCopy_on_rim _ ((A.sectors.rim_ball _).1 (Or.inl rfl)),
    A.sectorCopy_on_rim _ ((A.sectors.rim_ball _).1 (Or.inr rfl))]
  have hp := A.sectorGraph_endpoints K P D hD hcofaces labels hP (A.matching i)
  rw [A.matching.symm_apply_apply] at hp
  simpa only [image_pair,bridgeEnd,bridgeBegin] using
    congrArg (fun S => zeroSheet (ι := Fin 4) '' S) hp

theorem boundaryBridge_interval (i : Fin 4) :
    IsFinitePLBallPair ℝ (A.boundaryBridge i) {A.bridgeBegin i,A.bridgeEnd i} := by
  have hb := exteriorCopiedBridge_interval K P D hcofaces A.bands A.exteriorHeight
    A.exteriorHeightPL (exteriorFourIndex K P D labels (A.gaps.bridgeOrder i))
  rw [← A.gaps.bridge_endpoints i] at hb
  simpa only [boundaryBridge,bridgeBegin,bridgeEnd,image_pair] using
    hb.affine_image (zeroSheet (ι := Fin 4)) zeroSheet_injective.injOn

theorem boundaryBridge_union : (⋃ i : Fin 4,A.boundaryBridge i) = A.boundaryBridgeUnion := by
  ext z
  constructor
  · intro hz
    obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hz
    exact ⟨y,mem_iUnion₂.mpr ⟨(exteriorFourIndex K P D labels (A.gaps.bridgeOrder i)).1,
      (exteriorFourIndex K P D labels (A.gaps.bridgeOrder i)).2,hy⟩,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    obtain ⟨s,j,hy⟩ := mem_iUnion₂.mp hy
    let i := A.gaps.bridgeOrder.symm ((exteriorFourIndex K P D labels).symm (s,j))
    refine mem_iUnion.mpr ⟨i,y,?_,rfl⟩
    rw [show exteriorFourIndex K P D labels (A.gaps.bridgeOrder i) = (s,j) by simp [i]]
    exact hy

theorem boundaryBridges_pairwise_disjoint (hbound : ∀ s ∈ K.faces, s.card ≤ 3) :
    Pairwise (fun i j => Disjoint (A.boundaryBridge i) (A.boundaryBridge j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  have hxy := zeroSheet_injective (hxz.trans hyz.symm)
  subst y
  apply Set.disjoint_left.mp (exteriorCopiedBridge_pairwise K P D hcofaces A.bands A.exteriorHeight
    hbound (fun i x hx => (A.exteriorHeight_spec i x hx).2) ?_) hx hy
  exact fun he => hij (A.gaps.bridgeOrder.injective ((exteriorFourIndex K P D labels).injective he))

theorem gapCenters_injective : Function.Injective A.gapCenter := by
  intro i j he
  by_contra hij
  apply Set.disjoint_left.mp (A.sectorCopies_pairwise_disjoint
    (fun hm => hij (A.matching.injective hm)))
    (mem_image_of_mem _ (A.sectors.center_mem_sector (A.matching i)))
  change A.gapCenter i ∈ A.sectorCopy (A.matching j) '' A.sectors.sector (A.matching j)
  rw [he]
  exact mem_image_of_mem _ (A.sectors.center_mem_sector (A.matching j))



structure GapSpokePair (i : Fin 4) where
  left : Set ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))
  right : Set ((E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ))
  left_ball : IsFinitePLBallPair ℝ left {A.gapCenter i,A.bridgeEnd i}
  right_ball : IsFinitePLBallPair ℝ right {A.gapCenter i,A.bridgeBegin (i+1)}
  left_subset : left ⊆ A.sectorCopy (A.matching i) '' A.sectors.sector (A.matching i)
  right_subset : right ⊆ A.sectorCopy (A.matching i) '' A.sectors.sector (A.matching i)
  union_eq : left ∪ right = A.sectorCopy (A.matching i) ''
    (A.sectors.spoke (A.matching i) ∪ A.sectors.spoke (A.matching i+1))
  inter_eq : left ∩ right = {A.gapCenter i}
  left_bridges : left ∩ A.boundaryBridgeUnion = {A.bridgeEnd i}
  right_bridges : right ∩ A.boundaryBridgeUnion = {A.bridgeBegin (i+1)}
  selection :
    (left = A.sectorCopy (A.matching i) '' A.sectors.spoke (A.matching i) ∧
      right = A.sectorCopy (A.matching i) '' A.sectors.spoke (A.matching i+1)) ∨
    (left = A.sectorCopy (A.matching i) '' A.sectors.spoke (A.matching i+1) ∧
      right = A.sectorCopy (A.matching i) '' A.sectors.spoke (A.matching i))

theorem nonempty_gapSpokePair (i : Fin 4) : Nonempty (A.GapSpokePair i) := by
  let j := A.matching i
  let m := originalExteriorMarks K P D hcofaces A.bands labels
  let L := A.sectorCopy j '' A.sectors.spoke j
  let R := A.sectorCopy j '' A.sectors.spoke (j+1)
  have hL := A.copied_spoke_isFinitePLInterval j j (Or.inl rfl)
  have hR := A.copied_spoke_isFinitePLInterval j (j+1) (Or.inr rfl)
  have hLU := A.copied_spoke_inter_bridges j j (Or.inl rfl)
  have hRU := A.copied_spoke_inter_bridges j (j+1) (Or.inr rfl)
  have hLs : L ⊆ A.sectorCopy j '' A.sectors.sector j :=
    image_mono (A.sectors.spoke_subset_sector j)
  have hRs : R ⊆ A.sectorCopy j '' A.sectors.sector j :=
    image_mono (subset_union_right.trans (subset_union_right.trans (A.sectors.sector_ball j).1))
  have hI : L ∩ R = {A.gapCenter i} := A.copied_spokes_inter j
  have hU : L ∪ R = A.sectorCopy j '' (A.sectors.spoke j ∪ A.sectors.spoke (j+1)) :=
    (image_union _ _ _).symm
  rcases Set.pair_eq_pair_iff.mp (A.sector_copied_endpoints i) with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact ⟨⟨L,R,h0 ▸ hL,h1 ▸ hR,hLs,hRs,hU,hI,h0 ▸ hLU,h1 ▸ hRU,
      Or.inl ⟨rfl,rfl⟩⟩⟩
  · exact ⟨⟨R,L,h1 ▸ hR,h0 ▸ hL,hRs,hLs,
      (union_comm R L).trans hU,(inter_comm R L).trans hI,h1 ▸ hRU,h0 ▸ hLU,
      Or.inr ⟨rfl,rfl⟩⟩⟩

noncomputable def gapSpokes (i : Fin 4) : A.GapSpokePair i :=
  Classical.choice (A.nonempty_gapSpokePair i)

noncomputable def longBoundaryArc (i : Fin 4) :=
  ((A.gapSpokes (i-1)).right ∪ A.boundaryBridge i) ∪ (A.gapSpokes i).left

theorem gapSpokes_different_disjoint {i j : Fin 4} (hij : i ≠ j) :
    Disjoint ((A.gapSpokes i).left ∪ (A.gapSpokes i).right)
      ((A.gapSpokes j).left ∪ (A.gapSpokes j).right) :=
  (A.sectorCopies_pairwise_disjoint (fun he => hij (A.matching.injective he))).mono
    (union_subset (A.gapSpokes i).left_subset (A.gapSpokes i).right_subset)
    (union_subset (A.gapSpokes j).left_subset (A.gapSpokes j).right_subset)

theorem boundaryBridge_subset_union (i : Fin 4) : A.boundaryBridge i ⊆ A.boundaryBridgeUnion := by
  rw [← A.boundaryBridge_union]
  exact subset_iUnion _ i

theorem gapSpoke_left_bridge_contact (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (i j : Fin 4) (x : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)) :
    x ∈ (A.gapSpokes i).left ∩ A.boundaryBridge j ↔ i=j ∧ x=A.bridgeEnd i := by
  constructor
  · intro hx
    have he : x = A.bridgeEnd i := (A.gapSpokes i).left_bridges.subset
      ⟨hx.1,A.boundaryBridge_subset_union j hx.2⟩
    refine ⟨?_,he⟩
    by_contra hij
    exact Set.disjoint_left.mp (A.boundaryBridges_pairwise_disjoint hbound hij)
      (he.symm ▸ (A.boundaryBridge_interval i).1 (Or.inr rfl)) hx.2
  · rintro ⟨rfl,rfl⟩
    exact ⟨(A.gapSpokes i).left_ball.1 (Or.inr rfl),(A.boundaryBridge_interval i).1 (Or.inr rfl)⟩

theorem gapSpoke_right_bridge_contact (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (i j : Fin 4) (x : (E × (ResidualHalfBandIndex K P D → ℝ)) × (Fin 4 → ℝ)) :
    x ∈ (A.gapSpokes i).right ∩ A.boundaryBridge j ↔ j=i+1 ∧ x=A.bridgeBegin (i+1) := by
  constructor
  · intro hx
    have he : x = A.bridgeBegin (i+1) := (A.gapSpokes i).right_bridges.subset
      ⟨hx.1,A.boundaryBridge_subset_union j hx.2⟩
    refine ⟨?_,he⟩
    by_contra hij
    exact Set.disjoint_left.mp (A.boundaryBridges_pairwise_disjoint hbound (Ne.symm hij))
      (he.symm ▸ (A.boundaryBridge_interval (i+1)).1 (Or.inl rfl)) hx.2
  · rintro ⟨rfl,rfl⟩
    exact ⟨(A.gapSpokes i).right_ball.1 (Or.inr rfl),
      (A.boundaryBridge_interval (i+1)).1 (Or.inl rfl)⟩

private theorem interval_pair_endpoints_ne {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {u : Set X} {a b : X}
    (hu : IsFinitePLBallPair ℝ u {a,b}) : a ≠ b := by
  intro he
  have hc := hu.ncard_boundary_eq_two
  simp only [he,pair_eq_singleton,Set.ncard_singleton] at hc
  norm_num at hc

private theorem joined_interval_pairs {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {u v : Set X} {a b c : X}
    (hu : IsFinitePLBallPair ℝ u {a,b}) (hv : IsFinitePLBallPair ℝ v {b,c})
    (hinter : u ∩ v = {b}) : IsFinitePLBallPair ℝ (u∪v) {a,c} := by
  obtain ⟨p,hp,hp0,hp1⟩ := hu.exists_unitInterval_chart_with_endpoints (interval_pair_endpoints_ne hu)
  obtain ⟨r,hr,hr0,hr1⟩ := hv.exists_unitInterval_chart_with_endpoints (interval_pair_endpoints_ne hv)
  exact Dehn.isFinitePLBallPair_joined_intervals p r hp hr hp0 hp1 hr0 hr1 hinter

theorem longBoundaryArc_isFinitePLInterval (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 4) :
    IsFinitePLBallPair ℝ (A.longBoundaryArc i) {A.gapCenter (i-1),A.gapCenter i} := by
  have hn : i-1 ≠ i := by fin_cases i <;> decide
  have hright : IsFinitePLBallPair ℝ (A.gapSpokes (i-1)).right
      {A.gapCenter (i-1),A.bridgeBegin i} := by
    simpa only [sub_add_cancel] using (A.gapSpokes (i-1)).right_ball
  have hcontact : (A.gapSpokes (i-1)).right ∩ A.boundaryBridge i = {A.bridgeBegin i} := by
    ext x
    rw [A.gapSpoke_right_bridge_contact hbound,sub_add_cancel]
    simp
  have hfirst := joined_interval_pairs hright (A.boundaryBridge_interval i) hcontact
  have hlast : IsFinitePLBallPair ℝ (A.gapSpokes i).left {A.bridgeEnd i,A.gapCenter i} := by
    simpa only [Set.pair_comm] using (A.gapSpokes i).left_ball
  apply joined_interval_pairs hfirst hlast
  have hdis : Disjoint (A.gapSpokes (i-1)).right (A.gapSpokes i).left :=
    (A.gapSpokes_different_disjoint hn).mono subset_union_right subset_union_left
  rw [union_inter_distrib_right,Set.disjoint_iff_inter_eq_empty.mp hdis,empty_union,inter_comm]
  ext x
  rw [A.gapSpoke_left_bridge_contact hbound]
  simp

theorem longBoundaryArc_inter_next (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 4) :
    A.longBoundaryArc i ∩ A.longBoundaryArc (i+1) = {A.gapCenter i} := by
  have hn : i ≠ i+1 := by fin_cases i <;> decide
  have hm : i-1 ≠ i := by fin_cases i <;> decide
  have hmp : i-1 ≠ i+1 := by fin_cases i <;> decide
  simp only [longBoundaryArc]
  rw [show i+1-1 = i by fin_cases i <;> decide]
  apply Subset.antisymm
  · rintro x ⟨hx,hy⟩
    rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
    · exact (Set.disjoint_left.mp (A.gapSpokes_different_disjoint hm) (Or.inr hx) (Or.inr hy)).elim
    · have he := ((A.gapSpoke_right_bridge_contact hbound (i-1) (i+1) x).mp ⟨hx,hy⟩).1
      exact (hn (by simpa only [sub_add_cancel] using he.symm)).elim
    · exact (Set.disjoint_left.mp (A.gapSpokes_different_disjoint hmp) (Or.inr hx) (Or.inl hy)).elim
    · exact (hn ((A.gapSpoke_right_bridge_contact hbound i i x).mp ⟨hy,hx⟩).1).elim
    · exact (Set.disjoint_left.mp (A.boundaryBridges_pairwise_disjoint hbound hn) hx hy).elim
    · exact (hn (((A.gapSpoke_left_bridge_contact hbound (i+1) i x).mp ⟨hy,hx⟩).1).symm).elim
    · exact (A.gapSpokes i).inter_eq.subset ⟨hx,hy⟩
    · exact (hn ((A.gapSpoke_left_bridge_contact hbound i (i+1) x).mp ⟨hx,hy⟩).1).elim
    · exact (Set.disjoint_left.mp (A.gapSpokes_different_disjoint hn) (Or.inl hx) (Or.inl hy)).elim
  · rintro x rfl
    exact ⟨Or.inr ((A.gapSpokes i).left_ball.1 (Or.inl rfl)),
      Or.inl (Or.inl ((A.gapSpokes i).right_ball.1 (Or.inl rfl)))⟩

theorem longBoundaryArc_disjoint_opposite (hbound : ∀ s ∈ K.faces, s.card ≤ 3) (i : Fin 4) :
    Disjoint (A.longBoundaryArc i) (A.longBoundaryArc (i+2)) := by
  have h02 : i ≠ i+2 := by fin_cases i <;> decide
  have h01 : i ≠ i+1 := by fin_cases i <;> decide
  have hm1 : i-1 ≠ i+1 := by fin_cases i <;> decide
  have hm2 : i-1 ≠ i+2 := by fin_cases i <;> decide
  have hshift : i+2-1 = i+1 := by fin_cases i <;> decide
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [longBoundaryArc] at hx hy
  rw [hshift] at hy
  rcases hx with (hx | hx) | hx <;> rcases hy with (hy | hy) | hy
  · exact Set.disjoint_left.mp (A.gapSpokes_different_disjoint hm1) (Or.inr hx) (Or.inr hy)
  · have he := ((A.gapSpoke_right_bridge_contact hbound (i-1) (i+2) x).mp ⟨hx,hy⟩).1
    exact h02 (by simpa only [sub_add_cancel] using he.symm)
  · exact Set.disjoint_left.mp (A.gapSpokes_different_disjoint hm2) (Or.inr hx) (Or.inl hy)
  · have he := ((A.gapSpoke_right_bridge_contact hbound (i+1) i x).mp ⟨hy,hx⟩).1
    exact h02 (by simpa only [add_assoc,show (1:Fin 4)+1=2 from rfl] using he)
  · exact Set.disjoint_left.mp (A.boundaryBridges_pairwise_disjoint hbound h02) hx hy
  · exact h02 (((A.gapSpoke_left_bridge_contact hbound (i+2) i x).mp ⟨hy,hx⟩).1).symm
  · exact Set.disjoint_left.mp (A.gapSpokes_different_disjoint h01) (Or.inl hx) (Or.inr hy)
  · exact h02 ((A.gapSpoke_left_bridge_contact hbound i (i+2) x).mp ⟨hx,hy⟩).1
  · exact Set.disjoint_left.mp (A.gapSpokes_different_disjoint h02) (Or.inl hx) (Or.inl hy)

theorem longBoundaryArcs_cover : (⋃ i : Fin 4,A.longBoundaryArc i) = A.rim := by
  have hspoke (i : Fin 4) : (A.gapSpokes i).left ∪ (A.gapSpokes i).right ⊆ A.rim :=
    (A.gapSpokes i).union_eq.subset.trans (A.sector_spoke_traces_subset_rim (A.matching i))
  apply Subset.antisymm
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    rcases hi with (hr | hb) | hl
    · exact hspoke (i-1) (Or.inr hr)
    · exact A.rim_eq_bridges_union_spokes.symm.subset
        (Or.inl (A.boundaryBridge_subset_union i hb))
    · exact hspoke i (Or.inl hl)
  · intro z hz
    rcases A.rim_eq_bridges_union_spokes.subset hz with hb | hs
    · obtain ⟨i,hi⟩ := mem_iUnion.mp (A.boundaryBridge_union.symm.subset hb)
      exact mem_iUnion.mpr ⟨i,Or.inl (Or.inr hi)⟩
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hs
      let i := A.matching.symm j
      have hm : A.matching i = j := A.matching.apply_symm_apply j
      have hu := (A.gapSpokes i).union_eq
      rw [hm] at hu
      rcases hu.symm.subset hj with hl | hr
      · exact mem_iUnion.mpr ⟨i,Or.inr hl⟩
      · apply mem_iUnion.mpr
        refine ⟨i+1,?_⟩
        simp only [longBoundaryArc]
        have hshift : ∀ k : Fin 4,k+1-1=k := by intro k; fin_cases k <;> decide
        rw [hshift i]
        exact Or.inl (Or.inl hr)

end OriginalPrimalCutDiskData
end PoincareConjecture.M76.OriginalTriangleCopies
