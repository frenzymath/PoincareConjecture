import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.FourRimGaps
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ConnectedRimProjection
import Mathlib.Logic.Equiv.Fin.Basic









set_option autoImplicit false

open Set Geometry Classical
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  (P : SimpleGraph K.vertices)
  (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
  (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
  (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
  [Fintype (ResidualComplementaryEdge K P D)]
  (B : ∀ s : ResidualComplementaryEdge K P D,
    OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
  (h : ResidualHalfBandIndex K P D → E → ℝ)

noncomputable def exteriorCopiedBridge (i : ResidualHalfBandIndex K P D) :
    Set (E × (ResidualHalfBandIndex K P D → ℝ)) :=
  separatedSheet h i '' residualBridge K (complementaryOriginalEdge K P hcofaces i.1.val)
    ((B i.1).ends 0) ((B i.1).ends 1)

noncomputable def exteriorCopiedMark (i : ResidualHalfBandIndex K P D) (j : Fin 2) :
    E × (ResidualHalfBandIndex K P D → ℝ) :=
  separatedSheet h i (primalEdgeMark K (complementaryOriginalEdge K P hcofaces i.1.val)
    ((B i.1).ends j))

def exteriorFourIndex (labels : ResidualComplementaryEdge K P D ≃ Fin 2) :
    Fin 4 ≃ ResidualHalfBandIndex K P D :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr labels.symm (Equiv.refl (Fin 2)))

theorem exteriorCopiedBridge_interval
    (hh : ∀ i, FinitePiecewiseAffineOn (h i) ((B i.1).piece i.2))
    (i : ResidualHalfBandIndex K P D) :
    IsFinitePLBallPair ℝ (exteriorCopiedBridge K P D hcofaces B h i)
      {exteriorCopiedMark K P D hcofaces B h i 0,
        exteriorCopiedMark K P D hcofaces B h i 1} := by
  have hb := residualBridge_isFinitePLInterval K
    (complementaryOriginalEdge K P hcofaces i.1.val) (B i.1).ends_ne (B i.1).edge_eq
  simpa only [exteriorCopiedBridge,exteriorCopiedMark,image_pair] using
    hb.image_of_subset (separatedSheet_finitePL h i (hh i))
      (show _ ⊆ (B i.1).piece i.2 from fun x hx => (B i.1).disk i.2 |>.1 (Or.inr hx))
      (separatedSheet_injective h i).injOn

omit [Fintype (ResidualComplementaryEdge K P D)] in
theorem exteriorCopiedMark_ne (i : ResidualHalfBandIndex K P D) :
    exteriorCopiedMark K P D hcofaces B h i 0 ≠
      exteriorCopiedMark K P D hcofaces B h i 1 := by
  intro he
  exact primalEdgeMark_ne K _ _ ((B i.1).ends 0) ((B i.1).ends 1)
    (by simp [(B i.1).edge_eq]) (by simp [(B i.1).edge_eq]) (Or.inr (B i.1).ends_ne)
    (congrArg Prod.fst he)

theorem exteriorCopiedBridge_pairwise
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2)) :
    Pairwise (fun i j => Disjoint (exteriorCopiedBridge K P D hcofaces B h i)
      (exteriorCopiedBridge K P D hcofaces B h j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  have hh := (separatedSheet_distinct_eq_iff h hij x y).mp (hxz.trans hyz.symm)
  have hxpiece : x ∈ (B i.1).piece i.2 := (B i.1).disk i.2 |>.1 (Or.inr hx)
  exact Set.disjoint_left.mp ((B i.1).bridge_disjoint_attachment hbound i.2) hx
    ((hz i x hxpiece).mp hh.2.1)

omit [Fintype (ResidualComplementaryEdge K P D)] in
theorem exteriorCopiedBridge_union :
    (⋃ i : ResidualHalfBandIndex K P D, exteriorCopiedBridge K P D hcofaces B h i) =
      complementaryBridgeCopies K P D hcofaces B h := by
  ext z
  simp only [exteriorCopiedBridge,complementaryBridgeCopies,mem_iUnion,Prod.exists]

omit [Fintype (ResidualComplementaryEdge K P D)] in
theorem exteriorCopiedMark_projects (i : ResidualHalfBandIndex K P D) (j : Fin 2) :
    (exteriorCopiedMark K P D hcofaces B h i j).1 ∈
      residualQuarterMarks K P D hcofaces B := by
  apply mem_iUnion.mpr
  refine ⟨i.1,?_⟩
  fin_cases j <;> simp [exteriorCopiedMark,separatedSheet]

abbrev ExteriorGapCoordinates (labels : ResidualComplementaryEdge K P D ≃ Fin 2) :=
  FourRimBridgeCoordinates (complementaryCutRim K P D hD hcofaces B h)
    (fun i => exteriorCopiedBridge K P D hcofaces B h (exteriorFourIndex K P D labels i))
    (fun i => exteriorCopiedMark K P D hcofaces B h (exteriorFourIndex K P D labels i) 0)
    (fun i => exteriorCopiedMark K P D hcofaces B h (exteriorFourIndex K P D labels i) 1)

theorem nonempty_exteriorGapCoordinates
    (labels : ResidualComplementaryEdge K P D ≃ Fin 2)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (hh : ∀ i, FinitePiecewiseAffineOn (h i) ((B i.1).piece i.2))
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    (hdisk : IsFinitePLBallPair (ℝ × ℝ) (complementaryCutCarrier K P D hD hcofaces B h)
      (complementaryCutRim K P D hD hcofaces B h)) :
    Nonempty (ExteriorGapCoordinates K P D hD hcofaces B h labels) := by
  apply exists_four_rim_bridge_coordinates hdisk
  · exact fun i => exteriorCopiedBridge_interval K P D hcofaces B h hh _
  · exact fun i => exteriorCopiedMark_ne K P D hcofaces B h _
  · intro i
    exact complementary_bridge_copy_subset_rim K P D hD hcofaces B h hbound hz _ _
  · intro i j hij
    exact exteriorCopiedBridge_pairwise K P D hcofaces B h hbound hz
      (fun he => hij ((exteriorFourIndex K P D labels).injective he))



theorem exists_original_exterior_gaps
    (labels : ResidualComplementaryEdge K P D ≃ Fin 2)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (hDtree : D.IsTree) :
    ∃ (B : ∀ s : ResidualComplementaryEdge K P D,
        OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
      (h : ResidualHalfBandIndex K P D → E → ℝ),
      (∀ i, FinitePiecewiseAffineOn (h i) ((B i.1).piece i.2)) ∧
      (∀ i x, x ∈ (B i.1).piece i.2 →
        h i x ∈ Icc 0 1 ∧ (h i x = 0 ↔ x ∈ (B i.1).attachment i.2)) ∧
      IsFinitePLBallPair (ℝ × ℝ) (complementaryCutCarrier K P D hD hcofaces B h)
        (complementaryCutRim K P D hD hcofaces B h) ∧
      FinitePiecewiseAffineOn Prod.fst (complementaryCutCarrier K P D hD hcofaces B h) ∧
      Nonempty (ExteriorGapCoordinates K P D hD hcofaces B h labels) := by
  obtain ⟨B,h,hh,hz,hdisk,hproj,_⟩ :=
    exists_original_complementary_cut_disk K P D hD hcofaces hpure hlinks hDtree
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t,_,hst,ht⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq ht
  exact ⟨B,h,hh,hz,hdisk,hproj,nonempty_exteriorGapCoordinates K P D hD hcofaces
    B h labels hbound hh (fun i x hx => (hz i x hx).2) hdisk⟩

variable (labels : ResidualComplementaryEdge K P D ≃ Fin 2)
  (C : ExteriorGapCoordinates K P D hD hcofaces B h labels)

noncomputable def exteriorGapInterior (i : Fin 4) :
    Set (E × (ResidualHalfBandIndex K P D → ℝ)) :=
  C.gap i \ {C.bridgeFinish i,C.bridgeStart (i+1)}

theorem exteriorGapInterior_isConnected (i : Fin 4) :
    IsConnected (exteriorGapInterior K P D hD hcofaces B h labels C i) :=
  (C.gap_isFinitePLBallPair_cyclic i).isConnected_sdiff

theorem exteriorGapInterior_nonempty (i : Fin 4) :
    (exteriorGapInterior K P D hD hcofaces B h labels C i).Nonempty :=
  (exteriorGapInterior_isConnected K P D hD hcofaces B h labels C i).nonempty

theorem exteriorGapInterior_closure (i : Fin 4) :
    closure (exteriorGapInterior K P D hD hcofaces B h labels C i) = C.gap i :=
  (C.gap_isFinitePLBallPair_cyclic i).closure_sdiff

theorem exteriorGapInterior_subset_rim (i : Fin 4) :
    exteriorGapInterior K P D hD hcofaces B h labels C i ⊆
      complementaryCutRim K P D hD hcofaces B h :=
  sdiff_subset.trans (C.gap_subset i)

theorem exteriorGapInterior_disjoint_copies (i : Fin 4) :
    Disjoint (exteriorGapInterior K P D hD hcofaces B h labels C i)
      (complementaryBridgeCopies K P D hcofaces B h) := by
  apply Set.disjoint_left.mpr
  intro z hz hcopy
  obtain ⟨s,j,hzcopy⟩ := mem_iUnion₂.mp hcopy
  let k : Fin 4 := C.bridgeOrder.symm ((exteriorFourIndex K P D labels).symm (s,j))
  have hindex : exteriorFourIndex K P D labels (C.bridgeOrder k) = (s,j) := by
    simp [k]
  have hcontact : z ∈ C.gap i ∩ exteriorCopiedBridge K P D hcofaces B h
      (exteriorFourIndex K P D labels (C.bridgeOrder k)) :=
    ⟨hz.1,by rw [hindex]; exact hzcopy⟩
  rcases (C.gap_inter_bridge_cyclic_iff i k z).mp hcontact with ⟨hik,hzmark⟩ | ⟨hki,hzmark⟩
  · exact hz.2 (Or.inl (hik ▸ hzmark))
  · exact hz.2 (Or.inr (hki ▸ hzmark))

theorem exteriorBridgeEndpoints_project_quarterMarks (i : Fin 4)
    {z : E × (ResidualHalfBandIndex K P D → ℝ)}
    (hz : z ∈ ({C.bridgeStart i,C.bridgeFinish i} : Set _)) :
    z.1 ∈ residualQuarterMarks K P D hcofaces B := by
  have hcopy := (C.bridge_endpoints i).subset hz
  rcases hcopy with he | he
  · rw [he]
    exact exteriorCopiedMark_projects K P D hcofaces B h _ 0
  · have he' : z = exteriorCopiedMark K P D hcofaces B h
        (exteriorFourIndex K P D labels (C.bridgeOrder i)) 1 := he
    rw [he']
    exact exteriorCopiedMark_projects K P D hcofaces B h _ 1

theorem exteriorGapEndpoints_project_quarterMarks (i : Fin 4)
    {z : E × (ResidualHalfBandIndex K P D → ℝ)}
    (hz : z ∈ ({C.bridgeFinish i,C.bridgeStart (i+1)} : Set _)) :
    z.1 ∈ residualQuarterMarks K P D hcofaces B := by
  rcases hz with he | he
  · apply exteriorBridgeEndpoints_project_quarterMarks K P D hD hcofaces B h labels C i
    exact Or.inr he
  · apply exteriorBridgeEndpoints_project_quarterMarks K P D hD hcofaces B h labels C (i+1)
    exact Or.inl he

end PoincareConjecture.M76.OriginalTriangleCopies
