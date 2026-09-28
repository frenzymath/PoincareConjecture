import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedQuarterPrismVolumeMap









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_signed_sector_block_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (α β : ℝ) (sector : Bool → Bool → Set E) (face : Fin 2 → Bool → Set E)
    (axis target : Set E)
    (halfMap : ∀ i sign, ↥(signedTubeRadius i sign ×ˢ Icc α β) ≃ₜ face i sign)
    (map : ∀ eps delta, ↥(signedTubeQuarter eps delta ×ˢ Icc α β) ≃ₜ sector eps delta)
    (hmap : ∀ eps delta, (map eps delta).IsFinitePL)
    (hInter : ∀ eps delta,
      sector eps delta ∩ sector eps (!delta) = face 1 eps ∧
      sector eps delta ∩ sector (!eps) delta = face 0 delta ∧
      sector eps delta ∩ sector (!eps) (!delta) = axis)
    (hFaceMeet : ∀ eps delta, face 0 delta ∩ face 1 eps = axis)
    (hCover : (⋃ eps, ⋃ delta, sector eps delta) = target)
    (hkeep0 : ∀ eps delta (x : ↥(signedTubeRadius 0 delta ×ˢ Icc α β)),
      (map eps delta ⟨x, (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inl x.property.1)),
        x.property.2⟩ : E) = halfMap 0 delta x)
    (hkeep1 : ∀ eps delta (x : ↥(signedTubeRadius 1 eps ×ˢ Icc α β)),
      (map eps delta ⟨x, (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inr x.property.1)),
        x.property.2⟩ : E) = halfMap 1 eps x)
    (z : Icc α β → E)
    (haxis : ∀ eps delta (t : Icc α β),
      (map eps delta ⟨((0, 0), t), (signedTube_quarter_ball eps delta).1
        (Or.inr (Or.inl (left_mem_segment ℝ _ _))), t.property⟩ : E) = z t) :
    ∃ H : ↥(signedTubeDiamond ×ˢ Icc α β) ≃ₜ target, H.IsFinitePL ∧
      (∀ eps delta (x : ↥(signedTubeQuarter eps delta ×ˢ Icc α β)),
        (H ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property.1⟩⟩,
          x.property.2⟩ : E) = map eps delta x) ∧
      ∀ eps delta (x : ↥(signedTubeDiamond ×ˢ Icc α β)),
        (x : P2 × ℝ).1 ∈ signedTubeQuarter eps delta ↔ (H x : E) ∈ sector eps delta := by
  classical
  have hSrc0 (eps delta : Bool) : signedTubeRadius 0 delta ×ˢ Icc α β ⊆
      signedTubeQuarter eps delta ×ˢ Icc α β :=
    fun _ hx => ⟨(signedTube_quarter_ball eps delta).1 (Or.inr (Or.inl hx.1)), hx.2⟩
  have hSrc1 (eps delta : Bool) : signedTubeRadius 1 eps ×ˢ Icc α β ⊆
      signedTubeQuarter eps delta ×ˢ Icc α β :=
    fun _ hx => ⟨(signedTube_quarter_ball eps delta).1 (Or.inr (Or.inr hx.1)), hx.2⟩
  have hTgt0 (eps delta : Bool) : face 0 delta ⊆ sector eps delta := by
    rw [← (hInter eps delta).2.1]
    exact inter_subset_left
  have hTgt1 (eps delta : Bool) : face 1 eps ⊆ sector eps delta := by
    rw [← (hInter eps delta).1]
    exact inter_subset_left
  have hR0 (eps delta : Bool) (x : ↥(signedTubeQuarter eps delta ×ˢ Icc α β)) :
      (x : P2 × ℝ).1 ∈ signedTubeRadius 0 delta ↔ (map eps delta x : E) ∈ face 0 delta := by
    have h := (map eps delta).mem_subset_iff_of_extension (halfMap 0 delta)
      (hSrc0 eps delta) (hTgt0 eps delta) (fun y => Subtype.ext (hkeep0 eps delta y)) x
    simpa only [mem_prod, x.property.2, and_true] using h
  have hR1 (eps delta : Bool) (x : ↥(signedTubeQuarter eps delta ×ˢ Icc α β)) :
      (x : P2 × ℝ).1 ∈ signedTubeRadius 1 eps ↔ (map eps delta x : E) ∈ face 1 eps := by
    have h := (map eps delta).mem_subset_iff_of_extension (halfMap 1 eps)
      (hSrc1 eps delta) (hTgt1 eps delta) (fun y => Subtype.ext (hkeep1 eps delta y)) x
    simpa only [mem_prod, x.property.2, and_true] using h
  have hA (eps delta : Bool) (x : ↥(signedTubeQuarter eps delta ×ˢ Icc α β)) :
      (x : P2 × ℝ).1 = (0, 0) ↔ (map eps delta x : E) ∈ axis := by
    rw [← mem_singleton_iff, ← signedTube_cross_radius_inter eps delta, ← hFaceMeet eps delta]
    exact (hR0 eps delta x).and (hR1 eps delta x)
  have hoverlap (u w : Bool × Bool) (x : ↥(signedTubeQuarter u.1 u.2 ×ˢ Icc α β)) :
      (x : P2 × ℝ) ∈ signedTubeQuarter w.1 w.2 ×ˢ Icc α β ↔
        (map u.1 u.2 x : E) ∈ sector w.1 w.2 := by
    rcases u with ⟨eps, delta⟩
    rcases w with ⟨eps', delta'⟩
    dsimp only at x ⊢
    by_cases heps : eps = eps'
    · subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        exact iff_of_true x.property (map eps delta x).property
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hs : (x : P2 × ℝ).1 ∈ signedTubeQuarter eps (!delta) ↔
            (x : P2 × ℝ).1 ∈ signedTubeRadius 1 eps := by
          rw [← signedTube_quarter_inter_delta eps delta]
          simp only [mem_inter_iff, x.property.1, true_and]
        have ht : (map eps delta x : E) ∈ sector eps (!delta) ↔
            (map eps delta x : E) ∈ face 1 eps := by
          rw [← (hInter eps delta).1]
          simp only [mem_inter_iff, (map eps delta x).property, true_and]
        simpa only [mem_prod, x.property.2, and_true] using hs.trans ((hR1 eps delta x).trans ht.symm)
    · have hn : eps' = !eps := Bool.eq_not_of_ne (Ne.symm heps)
      subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        have hs : (x : P2 × ℝ).1 ∈ signedTubeQuarter (!eps) delta ↔
            (x : P2 × ℝ).1 ∈ signedTubeRadius 0 delta := by
          rw [← signedTube_quarter_inter_eps eps delta]
          simp only [mem_inter_iff, x.property.1, true_and]
        have ht : (map eps delta x : E) ∈ sector (!eps) delta ↔
            (map eps delta x : E) ∈ face 0 delta := by
          rw [← (hInter eps delta).2.1]
          simp only [mem_inter_iff, (map eps delta x).property, true_and]
        simpa only [mem_prod, x.property.2, and_true] using hs.trans ((hR0 eps delta x).trans ht.symm)
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hs : (x : P2 × ℝ).1 ∈ signedTubeQuarter (!eps) (!delta) ↔
            (x : P2 × ℝ).1 = (0, 0) := by
          rw [← mem_singleton_iff, ← signedTube_quarter_inter_opposite eps delta]
          simp only [mem_inter_iff, x.property.1, true_and]
        have ht : (map eps delta x : E) ∈ sector (!eps) (!delta) ↔
            (map eps delta x : E) ∈ axis := by
          rw [← (hInter eps delta).2.2]
          simp only [mem_inter_iff, (map eps delta x).property, true_and]
        simpa only [mem_prod, x.property.2, and_true] using hs.trans ((hA eps delta x).trans ht.symm)
  have hAxisVal (eps delta : Bool) (x : P2 × ℝ)
      (hx : x ∈ signedTubeQuarter eps delta ×ˢ Icc α β) (hz : x.1 = (0, 0)) :
      (map eps delta ⟨x, hx⟩ : E) = z ⟨x.2, hx.2⟩ := by
    have heq : (⟨x, hx⟩ : ↥(signedTubeQuarter eps delta ×ˢ Icc α β)) =
        ⟨((0, 0), x.2), (signedTube_quarter_ball eps delta).1
          (Or.inr (Or.inl (left_mem_segment ℝ _ _))), hx.2⟩ := Subtype.ext (Prod.ext hz rfl)
    rw [heq]
    exact haxis eps delta ⟨x.2, hx.2⟩
  have hagree (u w : Bool × Bool) (x : P2 × ℝ)
      (hx : x ∈ signedTubeQuarter u.1 u.2 ×ˢ Icc α β)
      (hy : x ∈ signedTubeQuarter w.1 w.2 ×ˢ Icc α β) :
      (map u.1 u.2 ⟨x, hx⟩ : E) = map w.1 w.2 ⟨x, hy⟩ := by
    rcases u with ⟨eps, delta⟩
    rcases w with ⟨eps', delta'⟩
    by_cases heps : eps = eps'
    · subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        rfl
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hr := (signedTube_quarter_inter_delta eps delta).subset ⟨hx.1, hy.1⟩
        exact (hkeep1 eps delta ⟨x, hr, hx.2⟩).trans (hkeep1 eps (!delta) ⟨x, hr, hx.2⟩).symm
    · have hn : eps' = !eps := Bool.eq_not_of_ne (Ne.symm heps)
      subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        have hr := (signedTube_quarter_inter_eps eps delta).subset ⟨hx.1, hy.1⟩
        exact (hkeep0 eps delta ⟨x, hr, hx.2⟩).trans (hkeep0 (!eps) delta ⟨x, hr, hx.2⟩).symm
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hz := (signedTube_quarter_inter_opposite eps delta).subset ⟨hx.1, hy.1⟩
        exact (hAxisVal eps delta x hx hz).trans (hAxisVal (!eps) (!delta) x hy hz).symm
  obtain ⟨G, hG, hGkeep⟩ := Homeomorph.exists_iUnion_finitePL
    (fun u : Bool × Bool => signedTubeQuarter u.1 u.2 ×ˢ Icc α β)
    (fun u : Bool × Bool => sector u.1 u.2)
    (fun u => map u.1 u.2) (fun u => hmap u.1 u.2) hoverlap hagree
  have hSource : (⋃ u : Bool × Bool, signedTubeQuarter u.1 u.2 ×ˢ Icc α β) =
      signedTubeDiamond ×ˢ Icc α β := by
    ext x
    simp only [signedTubeDiamond, mem_iUnion, mem_prod, Prod.exists]
    exact ⟨fun ⟨eps, delta, hx, ht⟩ => ⟨⟨eps, delta, hx⟩, ht⟩,
      fun ⟨⟨eps, delta, hx⟩, ht⟩ => ⟨eps, delta, hx, ht⟩⟩
  have hTarget : (⋃ u : Bool × Bool, sector u.1 u.2) = target := by
    calc
      (⋃ u : Bool × Bool, sector u.1 u.2) = ⋃ eps, ⋃ delta, sector eps delta := by
        ext x
        simp only [mem_iUnion, Prod.exists]
      _ = target := hCover
  let H := (Homeomorph.setCongr hSource.symm).trans (G.trans (Homeomorph.setCongr hTarget))
  have hH : H.IsFinitePL := hG.setCongr hSource hTarget
  have hKeep (eps delta : Bool) (x : ↥(signedTubeQuarter eps delta ×ˢ Icc α β)) :
      (H ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property.1⟩⟩, x.property.2⟩ : E) =
        map eps delta x := hGkeep (eps, delta) x
  refine ⟨H, hH, hKeep, ?_⟩
  intro eps delta x
  have hSourceSub : signedTubeQuarter eps delta ×ˢ Icc α β ⊆ signedTubeDiamond ×ˢ Icc α β :=
    fun _ hx => ⟨mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, hx.1⟩⟩, hx.2⟩
  have hTargetSub : sector eps delta ⊆ target :=
    fun _ hx => hCover.subset (mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, hx⟩⟩)
  have h := H.mem_subset_iff_of_extension (map eps delta) hSourceSub hTargetSub
    (fun y => Subtype.ext (hKeep eps delta y)) x
  simpa only [mem_prod, x.property.2, and_true] using h

end PoincareConjecture.M76.Dehn
