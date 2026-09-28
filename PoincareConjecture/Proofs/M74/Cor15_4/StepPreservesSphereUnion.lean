import PoincareConjecture.Proofs.M74.Cor15_4.ComponentBookkeeping
import PoincareConjecture.Proofs.M74.Cor15_4.ComponentRestriction
import PoincareConjecture.Proofs.M74.Cor15_4.ComponentUntouched
import PoincareConjecture.Proofs.M74.Cor15_4.FiniteComponentFamily
import PoincareConjecture.Proofs.M74.Cor15_4.FiniteInduction

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M74

private theorem isConnected_of_nonempty_diffeomorph_threeSphere
    {P : GeneralizedSliceCarrier.{u}}
    (h : Nonempty (Diffeomorph (𝓡 3) (𝓡 3) P.carrier ThreeSphere ∞)) :
    IsConnected (univ : Set P.carrier) := by
  obtain ⟨d⟩ := h
  let : ConnectedSpace ThreeSphere := Subtype.connectedSpace
    (isConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 4)) (by norm_num))
  let : ConnectedSpace P.carrier := d.toHomeomorph.connectedSpace_iff.mpr inferInstance
  exact isConnected_univ

theorem SphereUnion.of_connectedSumStep
    (hbinary : ∀ B0 B1 C : GeneralizedSliceCarrier.{u},
      SmoothConnectedSumData B0 B1 C →
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) B0.carrier ThreeSphere ∞) →
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) B1.carrier ThreeSphere ∞) →
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) C.carrier ThreeSphere ∞))
    {A C : GeneralizedSliceCarrier.{u}}
    (hstep : SmoothConnectedSumStep A C) (hA : SphereUnion A) : SphereUnion C := by
  classical
  obtain ⟨n, pieces, ⟨D⟩, hpieces⟩ := hA
  obtain ⟨B0, B1, ⟨E⟩, ⟨S⟩⟩ := hstep
  have hconnected (i : Fin n) : IsConnected (univ : Set (pieces i).carrier) :=
    isConnected_of_nonempty_diffeomorph_threeSphere (hpieces i)
  have hpreconnected (i : Fin n) : IsPreconnected (univ : Set (pieces i).carrier) :=
    (hconnected i).isPreconnected
  have hregionConnected (i : Fin n) : IsConnected (D.region i) := by
    rw [← (D.identify i).map_image]
    exact (hconnected i).image _ (D.identify i).map_smooth.continuousOn
  obtain ⟨i0, hball0, _, hside0⟩ :=
    D.exists_region_for_surgeryBall E hpreconnected 0 S.first_ball
  obtain ⟨i1, hball1, _, hside1⟩ :=
    D.exists_region_for_surgeryBall E hpreconnected 1 S.second_ball
  let U : Fin n → Set B0.carrier := fun i => (E.identify 0).map ⁻¹' D.region i
  let V : Fin n → Set B1.carrier := fun i => (E.identify 1).map ⁻¹' D.region i
  have hU (i : Fin n) : IsClopen (U i) := D.pieceInSide_region_isClopen E i 0
  have hV (i : Fin n) : IsClopen (V i) := D.pieceInSide_region_isClopen E i 1
  have hchart0 : S.first_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ U i0 :=
    fun _ hx => hball0 (mem_image_of_mem _ hx)
  have hchart1 : S.second_ball.map '' ball (0 : StandardCapSpace) 2 ⊆ V i1 :=
    fun _ hx => hball1 (mem_image_of_mem _ hx)
  let T := S.selectedComponentOpens (hU i0) (hV i1) hchart0 hchart1
  have hT : IsClopen (T : Set C.carrier) :=
    S.selectedComponentRegion_isClopen (hU i0) (hV i1) hchart0 hchart1
  have hcore : Nonempty
      (Diffeomorph (𝓡 3) (𝓡 3) (C.opens T).carrier ThreeSphere ∞) :=
    hbinary (pieces i0) (pieces i1) (C.opens T)
      (S.restrictComponents (D.pieceInSide E i0 0 hside0) (D.pieceInSide E i1 1 hside1)
        (hU i0) (hV i1) hchart0 hchart1)
      (hpieces i0) (hpieces i1)
  let z0 : UnitTwoSphere := Classical.choice
    (NormedSpace.sphere_nonempty (E := StandardCapSpace).mpr zero_le_one).coe_sort
  let y0 : T := ⟨S.collar (z0, 0),
    Or.inr (mem_image_of_mem _ ⟨mem_univ z0, mem_singleton 0⟩)⟩
  let F : Fin n → Set C.carrier := fun i => S.selectedFirstRegion (U i)
  let G : Fin n → Set C.carrier := fun i => S.selectedSecondRegion (V i)
  let R : Fin n → Set C.carrier := fun i => F i ∪ G i
  have havoid0 (i : Fin n) (hi : i ≠ i0) :
      Disjoint (U i) (S.first_ball.map '' ball (0 : StandardCapSpace) 2) := by
    apply Set.disjoint_left.mpr
    intro x hx hb
    exact Set.disjoint_left.mp (D.pairwise_disjoint i i0 hi) hx
      (hball0 (mem_image_of_mem _ hb))
  have havoid1 (i : Fin n) (hi : i ≠ i1) :
      Disjoint (V i) (S.second_ball.map '' ball (0 : StandardCapSpace) 2) := by
    apply Set.disjoint_left.mpr
    intro x hx hb
    exact Set.disjoint_left.mp (D.pairwise_disjoint i i1 hi) hx
      (hball1 (mem_image_of_mem _ hb))
  have hRclopen (i : Fin n) (hi0 : i ≠ i0) (hi1 : i ≠ i1) : IsClopen (R i) :=
    (S.selectedFirstRegion_isClopen_of_disjoint_chart (hU i) (havoid0 i hi0)).union
      (S.selectedSecondRegion_isClopen_of_disjoint_chart (hV i) (havoid1 i hi1))
  have hRidentify (i : Fin n) (hi0 : i ≠ i0) (hi1 : i ≠ i1) :
      Nonempty (SurgeryRegionEquivalence (pieces i) C univ (R i)) := by
    obtain ⟨j, hj, _⟩ := E.existsUnique_region_of_isConnected (hregionConnected i)
    fin_cases j
    · have hVempty : V i = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact Set.disjoint_left.mp (E.pairwise_disjoint 0 1 (by decide)) (hj hx)
          ((E.identify 1).map_image.subset (mem_image_of_mem _ (mem_univ x)))
      have hRi : R i = F i := by
        simp only [R, G, hVempty, SmoothConnectedSumData.selectedSecondRegion,
          preimage_empty, inter_empty, union_empty]
      rw [hRi]
      exact ⟨S.firstUntouchedEquivalence (D.pieceInSide E i 0 hj) (havoid0 i hi0)⟩
    · have hUempty : U i = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact Set.disjoint_left.mp (E.pairwise_disjoint 0 1 (by decide))
          ((E.identify 0).map_image.subset (mem_image_of_mem _ (mem_univ x))) (hj hx)
      have hRi : R i = G i := by
        simp only [R, F, hUempty, SmoothConnectedSumData.selectedFirstRegion,
          preimage_empty, inter_empty, empty_union]
      rw [hRi]
      exact ⟨S.secondUntouchedEquivalence (D.pieceInSide E i 1 hj) (havoid1 i hi1)⟩
  have hFpair (i j : Fin n) (hij : i ≠ j) : Disjoint (F i) (F j) :=
    Set.disjoint_left.mpr (fun _ hx hy =>
      Set.disjoint_left.mp (D.pairwise_disjoint i j hij) hx.2 hy.2)
  have hGpair (i j : Fin n) (hij : i ≠ j) : Disjoint (G i) (G j) :=
    Set.disjoint_left.mpr (fun _ hx hy =>
      Set.disjoint_left.mp (D.pairwise_disjoint i j hij) hx.2 hy.2)
  have hFG (i j : Fin n) : Disjoint (F i) (G j) :=
    S.regions_disjoint.mono (fun _ hx => hx.1) (fun _ hx => hx.1)
  have hRpair (i j : Fin n) (hij : i ≠ j) : Disjoint (R i) (R j) := by
    apply Set.disjoint_left.mpr
    rintro x (hx | hx) (hy | hy)
    · exact Set.disjoint_left.mp (hFpair i j hij) hx hy
    · exact Set.disjoint_left.mp (hFG i j) hx hy
    · exact Set.disjoint_left.mp (hFG j i) hy hx
    · exact Set.disjoint_left.mp (hGpair i j hij) hx hy
  have hTR (i : Fin n) (hi0 : i ≠ i0) (hi1 : i ≠ i1) :
      Disjoint (T : Set C.carrier) (R i) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    change x ∈ F i0 ∪ G i1 ∪ S.collar '' (univ ×ˢ ({0} : Set ℝ)) at hx
    change x ∈ F i ∪ G i at hy
    rcases hx with (hx | hx) | hx <;> rcases hy with hy | hy
    · exact Set.disjoint_left.mp (hFpair i0 i hi0.symm) hx hy
    · exact Set.disjoint_left.mp (hFG i0 i) hx hy
    · exact Set.disjoint_left.mp (hFG i i1) hy hx
    · exact Set.disjoint_left.mp (hGpair i1 i hi1.symm) hx hy
    · exact Set.disjoint_left.mp S.central_disjoint hx (Or.inl hy.1)
    · exact Set.disjoint_left.mp S.central_disjoint hx (Or.inr hy.1)
  let Remaining := {i : Fin n // i ≠ i0 ∧ i ≠ i1}
  let newPieces : Option Remaining → GeneralizedSliceCarrier.{u} :=
    fun i => i.elim (C.opens T) (fun j => pieces j.1)
  let newRegion : Option Remaining → Set C.carrier :=
    fun i => i.elim (T : Set C.carrier) (fun j => R j.1)
  apply SphereUnion.of_finite_regions newPieces newRegion
  · intro i
    cases i with
    | none => exact hT.isOpen
    | some i => exact (hRclopen i.1 i.2.1 i.2.2).isOpen
  · intro i
    cases i with
    | none => exact hT.isClosed
    | some i => exact (hRclopen i.1 i.2.1 i.2.2).isClosed
  · intro i
    cases i with
    | none => exact C.opensEquivalence T y0
    | some i => exact Classical.choice (hRidentify i.1 i.2.1 i.2.2)
  · intro i j hij
    cases i with
    | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j => exact hTR j.1 j.2.1 j.2.2
    | some i =>
        cases j with
        | none => exact (hTR i.1 i.2.1 i.2.2).symm
        | some j =>
            apply hRpair
            intro heq
            exact hij (congrArg Option.some (Subtype.ext heq))
  · apply eq_univ_of_forall
    intro x
    have hx : x ∈ S.first_region ∪ S.second_region ∪
        S.collar '' (univ ×ˢ ({0} : Set ℝ)) := S.cover.symm ▸ mem_univ x
    rcases hx with (hx | hx) | hx
    · have hD : (E.identify 0).map (S.first_identify.inverse x) ∈ ⋃ i, D.region i :=
        D.cover.symm ▸ mem_univ _
      obtain ⟨i, hi⟩ := mem_iUnion.mp hD
      by_cases hi0 : i = i0
      · refine mem_iUnion.mpr ⟨none, Or.inl (Or.inl ⟨hx, ?_⟩)⟩
        change (E.identify 0).map (S.first_identify.inverse x) ∈ D.region i0
        simpa only [hi0] using hi
      · have hi1 : i ≠ i1 := by
          intro hei
          have hE1 : (E.identify 0).map (S.first_identify.inverse x) ∈ E.region 1 :=
            hside1 (hei ▸ hi)
          have hE0 : (E.identify 0).map (S.first_identify.inverse x) ∈ E.region 0 :=
            (E.identify 0).map_image.subset (mem_image_of_mem _ (mem_univ _))
          exact Set.disjoint_left.mp (E.pairwise_disjoint 0 1 (by decide)) hE0 hE1
        exact mem_iUnion.mpr ⟨some ⟨i, hi0, hi1⟩, Or.inl ⟨hx, hi⟩⟩
    · have hD : (E.identify 1).map (S.second_identify.inverse x) ∈ ⋃ i, D.region i :=
        D.cover.symm ▸ mem_univ _
      obtain ⟨i, hi⟩ := mem_iUnion.mp hD
      by_cases hi1 : i = i1
      · refine mem_iUnion.mpr ⟨none, Or.inl (Or.inr ⟨hx, ?_⟩)⟩
        change (E.identify 1).map (S.second_identify.inverse x) ∈ D.region i1
        simpa only [hi1] using hi
      · have hi0 : i ≠ i0 := by
          intro hei
          have hE0 : (E.identify 1).map (S.second_identify.inverse x) ∈ E.region 0 :=
            hside0 (hei ▸ hi)
          have hE1 : (E.identify 1).map (S.second_identify.inverse x) ∈ E.region 1 :=
            (E.identify 1).map_image.subset (mem_image_of_mem _ (mem_univ _))
          exact Set.disjoint_left.mp (E.pairwise_disjoint 0 1 (by decide)) hE0 hE1
        exact mem_iUnion.mpr ⟨some ⟨i, hi0, hi1⟩, Or.inr ⟨hx, hi⟩⟩
    · exact mem_iUnion.mpr ⟨none, Or.inr hx⟩
  · intro i
    cases i with
    | none => exact hcore
    | some i => exact hpieces i.1

theorem connectedSumReduction_of_binary_sphere_identity
    (hbinary : ∀ B0 B1 C : GeneralizedSliceCarrier.{u},
      SmoothConnectedSumData B0 B1 C →
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) B0.carrier ThreeSphere ∞) →
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) B1.carrier ThreeSphere ∞) →
      Nonempty (Diffeomorph (𝓡 3) (𝓡 3) C.carrier ThreeSphere ∞)) :
    M74ConnectedSumReductionStatement.{u} :=
  connectedSumReduction_of_preserves_sphereUnion
    (fun _ _ => SphereUnion.of_connectedSumStep hbinary)

end PoincareConjecture.M74
