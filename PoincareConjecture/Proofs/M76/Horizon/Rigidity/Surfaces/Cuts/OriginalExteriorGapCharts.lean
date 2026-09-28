import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalExteriorGaps
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ComplementaryRimProjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalRimEndpoints
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.IntervalProjectionHomeomorph
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice









set_option autoImplicit false

open Set Geometry
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
  (labels : ResidualComplementaryEdge K P D ≃ Fin 2)
  (C : ExteriorGapCoordinates K P D hD hcofaces B h labels)

theorem exteriorGap_exists_projection_homeomorph
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    (marks : Fin 4 → E)
    (hmarks : range marks = residualQuarterMarks K P D hcofaces B)
    (T : OriginalPrimalSectorDecomposition
      (K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP))
      (K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP)) marks)
    (i : Fin 4) :
    ∃ j : Fin 4, ∃ e : C.gap i ≃ₜ T.rim j,
      e.IsFinitePL ∧ e.symm.IsFinitePL ∧
        ∀ x, (e x : E) = (x : E × (ResidualHalfBandIndex K P D → ℝ)).1 := by
  let S := exteriorGapInterior K P D hD hcofaces B h labels C i
  have hSrim : S ⊆ complementaryCutRim K P D hD hcofaces B h :=
    exteriorGapInterior_subset_rim K P D hD hcofaces B h labels C i
  have havoid : Disjoint S (complementaryBridgeCopies K P D hcofaces B h) :=
    exteriorGapInterior_disjoint_copies K P D hD hcofaces B h labels C i
  obtain ⟨j, hj, _⟩ := complementary_connected_rim_gap_unique_original_rim
    K P D hD hcofaces B h hP hbound hz marks hmarks T
    (exteriorGapInterior_isConnected K P D hD hcofaces B h labels C i) hSrim havoid
  have hclosure : closure S = C.gap i :=
    exteriorGapInterior_closure K P D hD hcofaces B h labels C i
  have hclosed : IsClosed (T.rim j) := (T.rim_ball j).isCompact.isClosed
  have hfull : MapsTo Prod.fst (C.gap i) (T.rim j) := by
    have hmap : MapsTo Prod.fst S (T.rim j) := fun x hx ↦ hj ⟨x, hx, rfl⟩
    have hc := hmap.closure_of_continuousOn continuous_fst.continuousOn
    simpa only [hclosure, hclosed.closure_eq] using hc
  have hne : C.bridgeFinish i ≠ C.bridgeStart (i + 1) := by
    have hn := C.gap_endpoints_ne i
    fin_cases i <;>
      simpa [FourRimBridgeCoordinates.gapLo, FourRimBridgeCoordinates.gapHi,
        FourRimBridgeCoordinates.bridgeStart, FourRimBridgeCoordinates.bridgeFinish,
        C.zero, C.one] using hn
  obtain ⟨c, ⟨g, hg, hgc⟩, hc0, hc1⟩ :=
    (C.gap_isFinitePLBallPair_cyclic i).exists_unitInterval_chart_with_endpoints hne
  have hgimage : g '' Icc (0 : ℝ) 1 = C.gap i := by
    apply Subset.antisymm
    · rintro x ⟨t, ht, rfl⟩
      exact (hgc ⟨t, ht⟩) ▸ (c ⟨t, ht⟩).property
    · intro x hx
      refine ⟨c.symm ⟨x, hx⟩, (c.symm ⟨x, hx⟩).property, ?_⟩
      exact (hgc _).symm.trans (congrArg Subtype.val (c.apply_symm_apply ⟨x, hx⟩))
  have hgi : InjOn g (Icc (0 : ℝ) 1) := by
    intro x hx y hy heq
    have he : c ⟨x, hx⟩ = c ⟨y, hy⟩ := Subtype.ext
      ((hgc ⟨x, hx⟩).trans (heq.trans (hgc ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (c.injective he)
  have hg0 : g 0 = C.bridgeFinish i := (hgc 0).symm.trans hc0
  have hg1 : g 1 = C.bridgeStart (i + 1) := (hgc 1).symm.trans hc1
  have hgo : g '' Ioo (0 : ℝ) 1 ⊆ S := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨hgimage.subset ⟨t, Ioo_subset_Icc_self ht, rfl⟩, ?_⟩
    rintro (heq | heq)
    · have he := hgi (Ioo_subset_Icc_self ht) (by norm_num) (heq.trans hg0.symm)
      exact ht.1.ne' he
    · have he := hgi (Ioo_subset_Icc_self ht) (by norm_num) (heq.trans hg1.symm)
      exact ht.2.ne he
  have hfi : InjOn Prod.fst (g '' Ioo (0 : ℝ) 1) := by
    apply (complementaryCut_projection_injOn_without_bridges K P D hD hcofaces B h
      hbound hz).mono
    intro x hx
    have hs := hgo hx
    exact ⟨complementaryCut_rim_subset_carrier K P D hD hcofaces B h (hSrim hs),
      fun hc ↦ disjoint_left.mp havoid hs hc⟩
  have hf : FinitePiecewiseAffineOn Prod.fst (g '' Icc (0 : ℝ) 1) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJs, _⟩, _⟩, _⟩ :=
      C.gap_isFinitePLBallPair_cyclic i
    exact ⟨J, hJ, hJs.trans hgimage.symm, J.affineOnFaces_affine
      (ContinuousLinearMap.fst ℝ E (ResidualHalfBandIndex K P D → ℝ)).toContinuousAffineMap⟩
  have hend {z : E × (ResidualHalfBandIndex K P D → ℝ)}
      (hzend : z ∈ ({C.bridgeFinish i, C.bridgeStart (i + 1)} : Set _)) :
      z.1 ∈ ({marks (T.order j), marks (T.order (j + 1))} : Set E) := by
    apply (T.rim_inter_marks j).subset
    refine ⟨hfull ((C.gap_isFinitePLBallPair_cyclic i).1 hzend), ?_⟩
    rw [hmarks]
    exact exteriorGapEndpoints_project_quarterMarks K P D hD hcofaces B h labels C i hzend
  obtain ⟨e, he, hei, heval⟩ := exists_finitePL_gap_projection_homeomorph hg hgi hf
    (T.rim_ball j) ((image_mono hgo).trans hj) hfi
    (hg0 ▸ hend (Or.inl rfl)) (hg1 ▸ hend (Or.inr rfl))
  let e' := (Homeomorph.setCongr hgimage.symm).trans e
  have he' : e'.IsFinitePL := ⟨Prod.fst, hgimage ▸ hf, fun x ↦ heval _⟩
  exact ⟨j, e', he', he'.symm, fun x ↦ heval _⟩

theorem exteriorGap_projection_matching
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hz : ∀ i x, x ∈ (B i.1).piece i.2 →
      (h i x = 0 ↔ x ∈ (B i.1).attachment i.2))
    (marks : Fin 4 → E) (hm : Function.Injective marks)
    (hmarks : range marks = residualQuarterMarks K P D hcofaces B)
    (T : OriginalPrimalSectorDecomposition
      (K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP))
      (K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP)) marks) :
    ∃ order : Fin 4 ≃ Fin 4, ∀ i, ∃ e : C.gap i ≃ₜ T.rim (order i),
      e.IsFinitePL ∧ e.symm.IsFinitePL ∧
        ∀ x, (e x : E) = (x : E × (ResidualHalfBandIndex K P D → ℝ)).1 := by
  classical
  choose a e he hei heval using fun i ↦ exteriorGap_exists_projection_homeomorph
    K P D hD hcofaces B h labels C hP hbound hz marks hmarks T i
  have himage (i : Fin 4) : Prod.fst '' C.gap i = T.rim (a i) := by
    apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact heval i ⟨z, hz⟩ ▸ (e i ⟨z, hz⟩).property
    · intro x hx
      refine ⟨(e i).symm ⟨x, hx⟩, ((e i).symm ⟨x, hx⟩).property, ?_⟩
      exact (heval i _).symm.trans
        (congrArg Subtype.val ((e i).apply_symm_apply ⟨x, hx⟩))
  have hgapcarrier : (⋃ i, C.gap i) ⊆ complementaryCutCarrier K P D hD hcofaces B h := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact complementaryCut_rim_subset_carrier K P D hD hcofaces B h (C.gap_subset i hi)
  have hf : InjOn Prod.fst ((⋃ i, C.gap i) \ Prod.fst ⁻¹' range marks) := by
    intro p hp q hq hpq
    have hprim : p.1 ∈ K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP) := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp.1
      exact T.rim_iUnion.subset (mem_iUnion.mpr ⟨a i, (himage i).subset ⟨p, hi, rfl⟩⟩)
    have hnot : p.1 ∉ residualBridgeUnion K P D hcofaces B := by
      intro hbridge
      apply hp.2
      rw [mem_preimage, hmarks]
      exact (residualBridgeUnion_inter_primalRim K P D hcofaces B hP).subset
        ⟨hbridge, hprim⟩
    obtain ⟨z, hfiber⟩ := complementaryCut_fiber_singleton_off_bridges K P D hD hcofaces
      B h hbound hz ⟨p, hgapcarrier hp.1, rfl⟩ hnot
    have hpz : p = z := hfiber.subset ⟨hgapcarrier hp.1, rfl⟩
    have hqz : q = z := hfiber.subset ⟨hgapcarrier hq.1, hpq.symm⟩
    exact hpz.trans hqz.symm
  have ha : Function.Injective a := by
    intro i j hij
    by_contra hne
    obtain ⟨y, hy, hynot⟩ := T.rim_without_marks_nonempty hm (a i)
    obtain ⟨x, hx, hfx⟩ := (himage i).symm.subset hy
    obtain ⟨z, hz, hfz⟩ := (himage j).symm.subset (hij ▸ hy)
    have hxz := hf
      ⟨mem_iUnion.mpr ⟨i, hx⟩, by simpa only [mem_preimage, hfx] using hynot⟩
      ⟨mem_iUnion.mpr ⟨j, hz⟩, by simpa only [mem_preimage, hfz] using hynot⟩
      (hfx.trans hfz.symm)
    exact disjoint_left.mp (C.gaps_pairwise_disjoint hne) hx (hxz.symm ▸ hz)
  exact ⟨Equiv.ofBijective a ⟨ha, Finite.surjective_of_injective ha⟩,
    fun i ↦ ⟨e i, he i, hei i, heval i⟩⟩

end PoincareConjecture.M76.OriginalTriangleCopies
