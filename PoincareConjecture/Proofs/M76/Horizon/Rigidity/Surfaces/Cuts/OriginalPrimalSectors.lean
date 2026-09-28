import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalConeSectors

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

open Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

structure OriginalPrimalSectorDecomposition (d q : Set E) (marks : Fin 4 → E) where
  order : Fin 4 ≃ Fin 4
  center : E
  rim : Fin 4 → Set E
  spoke : Fin 4 → Set E
  sector : Fin 4 → Set E
  center_mem : center ∈ d \ q
  rim_ball : ∀ i, IsFinitePLBallPair ℝ (rim i) {marks (order i), marks (order (i + 1))}
  rim_cover : (rim 0 ∪ rim 1) ∪ (rim 2 ∪ rim 3) = q
  rim_inter_next : ∀ i, rim i ∩ rim (i + 1) = {marks (order (i + 1))}
  rim_disjoint_opposite : ∀ i, Disjoint (rim i) (rim (i + 2))
  spoke_ball : ∀ i, IsFinitePLBallPair ℝ (spoke i) {center, marks (order i)}
  spoke_subset : ∀ i, spoke i ⊆ d
  spoke_rim : ∀ i, spoke i ∩ q = {marks (order i)}
  spoke_inter : ∀ i j, i ≠ j → spoke i ∩ spoke j = {center}
  sector_ball : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (sector i)
    (rim i ∪ (spoke i ∪ spoke (i + 1)))
  sector_cover : (sector 0 ∪ sector 1) ∪ (sector 2 ∪ sector 3) = d
  sector_rim : ∀ i, sector i ∩ q = rim i
  sector_inter_next : ∀ i, sector i ∩ sector (i + 1) = spoke (i + 1)
  sector_inter_opposite : ∀ i, sector i ∩ sector (i + 2) = {center}

omit [FiniteDimensional ℝ E] in
private theorem capSector_inter_rim {A q : Set E} (hAq : A ⊆ q) :
    boundaryCircleCap true A ∩ (q ×ˢ {(0 : ℝ)}) = A ×ˢ {(0 : ℝ)} := by
  apply Subset.antisymm
  · intro z hz
    exact (boundaryCircleCap_plane true A).subset ⟨hz.1, trivial, hz.2.2⟩
  · intro z hz
    exact ⟨((boundaryCircleCap_plane true A).symm.subset hz).1, hAq hz.1, hz.2⟩

theorem exists_original_primal_sector_decomposition
    {d q : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (marks : Fin 4 → E) (hm : Function.Injective marks) (hq : ∀ i, marks i ∈ q) :
    Nonempty (OriginalPrimalSectorDecomposition d q marks) := by
  obtain ⟨σ, A, B, C, D, hA, hB, hC, hD, hcover, hAB, hBC, hCD, hDA, hAC, hBD⟩ :=
    exists_four_prescribed_rim_arcs hd marks hm hq
  let rim : Fin 4 → Set E := ![A, B, C, D]
  have hrimball (i : Fin 4) : IsFinitePLBallPair ℝ (rim i)
      {marks (σ i), marks (σ (i + 1))} := by
    fin_cases i
    · simpa [rim] using hA
    · simpa [rim] using hB
    · simpa [rim] using hC
    · simpa [rim] using hD
  have hrimcover : (rim 0 ∪ rim 1) ∪ (rim 2 ∪ rim 3) = q := hcover
  have hrimnext (i : Fin 4) : rim i ∩ rim (i + 1) = {marks (σ (i + 1))} := by
    fin_cases i
    · simpa [rim] using hAB
    · simpa [rim] using hBC
    · simpa [rim] using hCD
    · simpa [rim] using hDA
  have hrimopposite (i : Fin 4) : Disjoint (rim i) (rim (i + 2)) := by
    fin_cases i
    · simpa [rim] using hAC
    · simpa [rim] using hBD
    · simpa [rim] using hAC.symm
    · simpa [rim] using hBD.symm
  have hrimq (i : Fin 4) : rim i ⊆ q := by
    intro x hx
    apply hrimcover.subset
    fin_cases i
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
  have hrimne (i : Fin 4) : (rim i).Nonempty :=
    ⟨marks (σ i), (hrimball i).1 (by simp)⟩
  obtain ⟨H, hH, hHbase, hHrim⟩ := exists_disk_cap_homeomorph hd
  obtain ⟨g, hg, hgvalue⟩ := hH.symm
  have gmem {z : E × ℝ} (hz : z ∈ boundaryCircleCap true q) : g z ∈ d := by
    rw [← hgvalue ⟨z, hz⟩]
    exact (H.symm ⟨z, hz⟩).property
  have ginj : InjOn g (boundaryCircleCap true q) := by
    intro x hx y hy hxy
    have he : H.symm ⟨x, hx⟩ = H.symm ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hgvalue] using hxy
    exact congrArg Subtype.val (H.symm.injective he)
  have gbase (x : E) (hx : x ∈ q) : g (x, 0) = x := by
    have hz : (x, (0 : ℝ)) ∈ boundaryCircleCap true q :=
      ((boundaryCircleCap_plane true q).symm.subset
        (show (x, (0 : ℝ)) ∈ q ×ˢ {(0 : ℝ)} from ⟨hx, rfl⟩)).1
    rw [← hgvalue ⟨(x, 0), hz⟩]
    have he : (⟨(x, (0 : ℝ)), hz⟩ : boundaryCircleCap true q) =
        H ⟨x, hd.1 hx⟩ := Subtype.ext (hHbase ⟨x, hx⟩).symm
    rw [he, H.symm_apply_apply]
  have gimage : g '' boundaryCircleCap true q = d := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact gmem hz
    · intro x hx
      refine ⟨H ⟨x, hx⟩, (H ⟨x, hx⟩).property, ?_⟩
      rw [← hgvalue, H.symm_apply_apply]
  have gbaseimage (s : Set E) (hs : s ⊆ q) : g '' (s ×ˢ {(0 : ℝ)}) = s := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      simpa [ht0, gbase x (hs hx)] using hx
    · intro x hx
      exact ⟨(x, 0), ⟨hx, rfl⟩, gbase x (hs hx)⟩
  have ginter (s t : Set (E × ℝ)) (hs : s ⊆ boundaryCircleCap true q)
      (ht : t ⊆ boundaryCircleCap true q) : g '' s ∩ g '' t = g '' (s ∩ t) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, he⟩⟩
      have hyx : y = x := ginj (ht hy) (hs hx) he
      exact ⟨x, ⟨hx, hyx ▸ hy⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  have capmono {s t : Set E} (h : s ⊆ t) :
      boundaryCircleCap true s ⊆ boundaryCircleCap true t := by
    intro z hz
    obtain ⟨x, hx, u, hu, hzu⟩ := (mem_capSector_iff s z).mp hz
    exact (mem_capSector_iff t z).mpr ⟨x, h hx, u, hu, hzu⟩
  let spokeCap (i : Fin 4) := boundaryCircleCap true ({marks (σ i)} : Set E)
  let sectorCap (i : Fin 4) := boundaryCircleCap true (rim i)
  let center := g (0, 1)
  let spoke (i : Fin 4) := g '' spokeCap i
  let sector (i : Fin 4) := g '' sectorCap i
  have hspokeCap (i : Fin 4) : spokeCap i ⊆ boundaryCircleCap true q :=
    capmono (singleton_subset_iff.mpr (hq (σ i)))
  have hsectorCap (i : Fin 4) : sectorCap i ⊆ boundaryCircleCap true q := capmono (hrimq i)
  have hbaseCap : q ×ˢ {(0 : ℝ)} ⊆ boundaryCircleCap true q :=
    fun z hz ↦ ((boundaryCircleCap_plane true q).symm.subset hz).1
  have hapex : ((0 : E), (1 : ℝ)) ∈ boundaryCircleCap true q := by
    exact (mem_capSector_iff q _).mpr ⟨marks 0, hq 0, 0, by simp, by simp⟩
  have hc : center ∈ d \ q := by
    refine ⟨gmem hapex, ?_⟩
    intro hcq
    have he : ((0 : E), (1 : ℝ)) = (center, 0) :=
      ginj hapex (hbaseCap ⟨hcq, rfl⟩) (gbase center hcq).symm
    have := congrArg Prod.snd he
    norm_num at this
  have hspokeball (i : Fin 4) : IsFinitePLBallPair ℝ (spoke i) {center, marks (σ i)} := by
    have hinj : InjOn (capSpoke (marks (σ i))) (Icc (0 : ℝ) 1) := by
      intro u hu v hv he
      exact ((capSpoke_fibers _ _ _ _).mp he).1
    have hcapball := (isFinitePLBallPair_Icc zero_lt_one).image
      (capSpoke_finitePL (marks (σ i))) hinj
    have hcapball' : IsFinitePLBallPair ℝ (spokeCap i) {(0, 1), (marks (σ i), 0)} := by
      simpa only [spokeCap, capSector_singleton, image_pair, capSpoke_apply,
        zero_smul, sub_zero, one_smul, sub_self] using hcapball
    have ht := hcapball'.image_of_subset hg (hspokeCap i) ginj
    simpa only [spoke, image_pair, center, gbase _ (hq (σ i))] using ht
  have hspokerim (i : Fin 4) : spoke i ∩ q = {marks (σ i)} := by
    change g '' spokeCap i ∩ q = _
    rw [← gbaseimage q Subset.rfl, ginter _ _ (hspokeCap i) hbaseCap]
    rw [show spokeCap i ∩ (q ×ˢ {(0 : ℝ)}) = {marks (σ i)} ×ˢ {(0 : ℝ)} from
      capSector_inter_rim (singleton_subset_iff.mpr (hq (σ i)))]
    exact gbaseimage _ (singleton_subset_iff.mpr (hq (σ i)))
  have hspokeinter (i j : Fin 4) (hij : i ≠ j) : spoke i ∩ spoke j = {center} := by
    change g '' spokeCap i ∩ g '' spokeCap j = _
    rw [ginter _ _ (hspokeCap i) (hspokeCap j)]
    have hdis : Disjoint ({marks (σ i)} : Set E) {marks (σ j)} := by
      simp only [disjoint_singleton]
      exact fun he ↦ hij (σ.injective (hm he))
    rw [show spokeCap i ∩ spokeCap j = {(0, 1)} from
      capSector_inter_of_disjoint (singleton_nonempty _) (singleton_nonempty _) hdis,
      image_singleton]
  have hsectorball (i : Fin 4) : IsFinitePLBallPair (ℝ × ℝ) (sector i)
      (rim i ∪ (spoke i ∪ spoke (i + 1))) := by
    have ht := (capSector_isFinitePLBallPair_spokes (hrimball i)).image_of_subset
      hg (hsectorCap i) ginj
    simpa only [sector, sectorCap, image_union, gbaseimage (rim i) (hrimq i),
      ← capSector_singleton, spoke, spokeCap] using ht
  refine ⟨{
    order := σ, center := center, rim := rim, spoke := spoke, sector := sector,
    center_mem := hc, rim_ball := hrimball, rim_cover := hrimcover,
    rim_inter_next := hrimnext, rim_disjoint_opposite := hrimopposite,
    spoke_ball := hspokeball, spoke_subset := ?_, spoke_rim := hspokerim,
    spoke_inter := hspokeinter, sector_ball := hsectorball, sector_cover := ?_,
    sector_rim := ?_, sector_inter_next := ?_, sector_inter_opposite := ?_ }⟩
  · rintro i z ⟨x, hx, rfl⟩
    exact gmem (hspokeCap i hx)
  · change (g '' sectorCap 0 ∪ g '' sectorCap 1) ∪
      (g '' sectorCap 2 ∪ g '' sectorCap 3) = d
    rw [← image_union, ← image_union, ← image_union]
    change g '' ((boundaryCircleCap true (rim 0) ∪ boundaryCircleCap true (rim 1)) ∪
      (boundaryCircleCap true (rim 2) ∪ boundaryCircleCap true (rim 3))) = d
    rw [← capSector_union, ← capSector_union, ← capSector_union, hrimcover, gimage]
  · intro i
    change g '' sectorCap i ∩ q = _
    rw [← gbaseimage q Subset.rfl, ginter _ _ (hsectorCap i) hbaseCap]
    rw [show sectorCap i ∩ (q ×ˢ {(0 : ℝ)}) = rim i ×ˢ {(0 : ℝ)} from
      capSector_inter_rim (hrimq i), gbaseimage _ (hrimq i)]
  · intro i
    change g '' sectorCap i ∩ g '' sectorCap (i + 1) = g '' spokeCap (i + 1)
    rw [ginter _ _ (hsectorCap i) (hsectorCap (i + 1))]
    congr 1
    exact (capSector_inter_of_singleton (hrimnext i)).trans (capSector_singleton _).symm
  · intro i
    change g '' sectorCap i ∩ g '' sectorCap (i + 2) = {center}
    rw [ginter _ _ (hsectorCap i) (hsectorCap (i + 2))]
    rw [show sectorCap i ∩ sectorCap (i + 2) = {(0, 1)} from
      capSector_inter_of_disjoint (hrimne i) (hrimne (i + 2)) (hrimopposite i), image_singleton]

end PoincareConjecture.M76.OriginalTriangleCopies
