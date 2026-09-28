import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedQuarterMaps









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_signed_diamond_map_on_radii
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (m : E) (a : Fin 2 → Bool → E) (rad : Fin 2 → Bool → Set E)
    (Q : Bool → Bool → Set E) (q target : Set E)
    (hRad : ∀ i sign, IsFinitePLBallPair ℝ (rad i sign) {m, a i sign})
    (hANe : ∀ i sign, a i sign ≠ m)
    (hQuarter : ∀ eps delta,
      IsFinitePLBallPair P2 (Q eps delta) ((Q eps delta ∩ q) ∪ (rad 0 delta ∪ rad 1 eps)) ∧
      IsFinitePLBallPair ℝ (Q eps delta ∩ q) {a 0 delta, a 1 eps} ∧
      (rad 0 delta ∪ rad 1 eps) ∩ (Q eps delta ∩ q) = {a 0 delta, a 1 eps} ∧
      rad 0 delta ∩ rad 1 eps = {m})
    (hInter : ∀ eps delta,
      Q eps delta ∩ Q eps (!delta) = rad 1 eps ∧
      Q eps delta ∩ Q (!eps) delta = rad 0 delta ∧
      Q eps delta ∩ Q (!eps) (!delta) = {m})
    (hcover : (⋃ eps, ⋃ delta, Q eps delta) = target) :
    ∃ G : signedTubeDiamond ≃ₜ target, G.IsFinitePL ∧
      ∃ (quarter : ∀ eps delta, signedTubeQuarter eps delta ≃ₜ Q eps delta)
        (radius : ∀ i sign, signedTubeRadius i sign ≃ₜ rad i sign),
        (∀ eps delta, (quarter eps delta).IsFinitePL) ∧
        (∀ i sign, (radius i sign).IsFinitePL) ∧
        (∀ eps delta (x : signedTubeQuarter eps delta),
          (G ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) =
            quarter eps delta x) ∧
        (∀ i sign (x : signedTubeRadius i sign),
          (G ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E) = radius i sign x) ∧
        (∀ eps delta (x : signedTubeDiamond),
          (x : P2) ∈ signedTubeQuarter eps delta ↔ (G x : E) ∈ Q eps delta) ∧
        (∀ i sign (x : signedTubeDiamond),
          (x : P2) ∈ signedTubeRadius i sign ↔ (G x : E) ∈ rad i sign) ∧
        (∀ i sign (x : signedTubeRadius i sign),
          (radius i sign x : E) = m ↔ (x : P2) = (0, 0)) ∧
        (∀ i sign (x : signedTubeRadius i sign),
          (radius i sign x : E) = a i sign ↔ (x : P2) = signedTubeCorner i sign) ∧
        ∀ eps delta (x : signedTubeQuarter eps delta),
          (x : P2) ∈ signedTubeOuterArc eps delta ↔
            (quarter eps delta x : E) ∈ Q eps delta ∩ q := by
  classical
  choose er her herCenter herEnd using fun (i : Fin 2) (sign : Bool) =>
    (signedTube_radius_ball i sign).exists_marked_interval_homeomorph
      (hRad i sign) (signedTube_corner_ne_center i sign).symm (hANe i sign).symm
  have hExtensions (eps delta : Bool) := exists_signed_quarter_map_on_radii
    m a rad Q q eps delta (hQuarter eps delta).1 (hQuarter eps delta).2.1
      (hQuarter eps delta).2.2.1 (hQuarter eps delta).2.2.2 er her herCenter herEnd
  choose f hf hkeep0 hkeep1 houter hradial using hExtensions
  have hSrc0 (eps delta : Bool) : signedTubeRadius 0 delta ⊆ signedTubeQuarter eps delta :=
    fun _ hx => (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inl hx))
  have hSrc1 (eps delta : Bool) : signedTubeRadius 1 eps ⊆ signedTubeQuarter eps delta :=
    fun _ hx => (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inr hx))
  have hTgt0 (eps delta : Bool) : rad 0 delta ⊆ Q eps delta :=
    fun _ hx => (hQuarter eps delta).1.1 (Or.inr (Or.inl hx))
  have hTgt1 (eps delta : Bool) : rad 1 eps ⊆ Q eps delta :=
    fun _ hx => (hQuarter eps delta).1.1 (Or.inr (Or.inr hx))
  have hRad0 (eps delta : Bool) (x : signedTubeQuarter eps delta) :
      (x : P2) ∈ signedTubeRadius 0 delta ↔ (f eps delta x : E) ∈ rad 0 delta :=
    (f eps delta).mem_subset_iff_of_extension (er 0 delta)
      (hSrc0 eps delta) (hTgt0 eps delta)
      (fun z => Subtype.ext (hkeep0 eps delta z)) x
  have hRad1 (eps delta : Bool) (x : signedTubeQuarter eps delta) :
      (x : P2) ∈ signedTubeRadius 1 eps ↔ (f eps delta x : E) ∈ rad 1 eps :=
    (f eps delta).mem_subset_iff_of_extension (er 1 eps)
      (hSrc1 eps delta) (hTgt1 eps delta)
      (fun z => Subtype.ext (hkeep1 eps delta z)) x
  have hZero (eps delta : Bool) : (0, 0) ∈ signedTubeQuarter eps delta :=
    hSrc0 eps delta (left_mem_segment ℝ _ _)
  have hCenter (eps delta : Bool) :
      (f eps delta ⟨(0, 0), hZero eps delta⟩ : E) = m :=
    (hkeep0 eps delta ⟨(0, 0), left_mem_segment ℝ _ _⟩).trans
      ((herCenter 0 delta ⟨(0, 0), left_mem_segment ℝ _ _⟩).mpr rfl)
  have hCenterIff (eps delta : Bool) (x : signedTubeQuarter eps delta) :
      (x : P2) = (0, 0) ↔ (f eps delta x : E) = m := by
    constructor
    · intro hx
      exact (congrArg (fun z : signedTubeQuarter eps delta => (f eps delta z : E))
        (show x = ⟨(0, 0), hZero eps delta⟩ from Subtype.ext hx)).trans (hCenter eps delta)
    · intro hx
      exact congrArg Subtype.val ((f eps delta).injective
        (Subtype.ext (hx.trans (hCenter eps delta).symm)))
  have hoverlap (u v : Bool × Bool) (x : signedTubeQuarter u.1 u.2) :
      (x : P2) ∈ signedTubeQuarter v.1 v.2 ↔ (f u.1 u.2 x : E) ∈ Q v.1 v.2 := by
    rcases u with ⟨eps, delta⟩
    rcases v with ⟨eps', delta'⟩
    dsimp only at x ⊢
    by_cases heps : eps = eps'
    · subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        exact iff_of_true x.property (f eps delta x).property
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hs : (x : P2) ∈ signedTubeQuarter eps (!delta) ↔
            (x : P2) ∈ signedTubeRadius 1 eps := by
          rw [← signedTube_quarter_inter_delta eps delta]
          simp only [mem_inter_iff, x.property, true_and]
        have ht : (f eps delta x : E) ∈ Q eps (!delta) ↔
            (f eps delta x : E) ∈ rad 1 eps := by
          rw [← (hInter eps delta).1]
          simp only [mem_inter_iff, (f eps delta x).property, true_and]
        exact hs.trans ((hRad1 eps delta x).trans ht.symm)
    · have hn : eps' = !eps := Bool.eq_not_of_ne (Ne.symm heps)
      subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        have hs : (x : P2) ∈ signedTubeQuarter (!eps) delta ↔
            (x : P2) ∈ signedTubeRadius 0 delta := by
          rw [← signedTube_quarter_inter_eps eps delta]
          simp only [mem_inter_iff, x.property, true_and]
        have ht : (f eps delta x : E) ∈ Q (!eps) delta ↔
            (f eps delta x : E) ∈ rad 0 delta := by
          rw [← (hInter eps delta).2.1]
          simp only [mem_inter_iff, (f eps delta x).property, true_and]
        exact hs.trans ((hRad0 eps delta x).trans ht.symm)
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hs : (x : P2) ∈ signedTubeQuarter (!eps) (!delta) ↔
            (x : P2) = (0, 0) := by
          rw [← mem_singleton_iff, ← signedTube_quarter_inter_opposite eps delta]
          simp only [mem_inter_iff, x.property, true_and]
        have ht : (f eps delta x : E) ∈ Q (!eps) (!delta) ↔
            (f eps delta x : E) = m := by
          rw [← mem_singleton_iff, ← (hInter eps delta).2.2]
          simp only [mem_inter_iff, (f eps delta x).property, true_and]
        exact hs.trans ((hCenterIff eps delta x).trans ht.symm)
  have hagree (u v : Bool × Bool) (x : P2)
      (hx : x ∈ signedTubeQuarter u.1 u.2) (hy : x ∈ signedTubeQuarter v.1 v.2) :
      (f u.1 u.2 ⟨x, hx⟩ : E) = f v.1 v.2 ⟨x, hy⟩ := by
    rcases u with ⟨eps, delta⟩
    rcases v with ⟨eps', delta'⟩
    dsimp only at hx hy ⊢
    by_cases heps : eps = eps'
    · subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        rfl
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hr : x ∈ signedTubeRadius 1 eps :=
          (signedTube_quarter_inter_delta eps delta).subset ⟨hx, hy⟩
        exact (hkeep1 eps delta ⟨x, hr⟩).trans (hkeep1 eps (!delta) ⟨x, hr⟩).symm
    · have hn : eps' = !eps := Bool.eq_not_of_ne (Ne.symm heps)
      subst eps'
      by_cases hdelta : delta = delta'
      · subst delta'
        have hr : x ∈ signedTubeRadius 0 delta :=
          (signedTube_quarter_inter_eps eps delta).subset ⟨hx, hy⟩
        exact (hkeep0 eps delta ⟨x, hr⟩).trans (hkeep0 (!eps) delta ⟨x, hr⟩).symm
      · have hn : delta' = !delta := Bool.eq_not_of_ne (Ne.symm hdelta)
        subst delta'
        have hz : x = (0, 0) :=
          (signedTube_quarter_inter_opposite eps delta).subset ⟨hx, hy⟩
        exact ((hCenterIff eps delta ⟨x, hx⟩).mp hz).trans
          ((hCenterIff (!eps) (!delta) ⟨x, hy⟩).mp hz).symm
  obtain ⟨G, hG, hGkeep⟩ := Homeomorph.exists_iUnion_finitePL
    (fun u : Bool × Bool => signedTubeQuarter u.1 u.2)
    (fun u : Bool × Bool => Q u.1 u.2)
    (fun u => f u.1 u.2) (fun u => hf u.1 u.2) hoverlap hagree
  have hSource : (⋃ u : Bool × Bool, signedTubeQuarter u.1 u.2) = signedTubeDiamond := by
    ext x
    simp only [signedTubeDiamond, mem_iUnion, Prod.exists]
  have hTarget : (⋃ u : Bool × Bool, Q u.1 u.2) = target := by
    calc
      (⋃ u : Bool × Bool, Q u.1 u.2) = ⋃ eps, ⋃ delta, Q eps delta := by
        ext x
        simp only [mem_iUnion, Prod.exists]
      _ = target := hcover
  let G' : signedTubeDiamond ≃ₜ target :=
    (Homeomorph.setCongr hSource.symm).trans (G.trans (Homeomorph.setCongr hTarget))
  have hG' : G'.IsFinitePL := hG.setCongr hSource hTarget
  have hKeep (eps delta : Bool) (x : signedTubeQuarter eps delta) :
      (G' ⟨x, mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, x.property⟩⟩⟩ : E) =
        f eps delta x := hGkeep (eps, delta) x
  have hQtarget (eps delta : Bool) : Q eps delta ⊆ target := by
    intro z hz
    exact hcover.subset (mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, hz⟩⟩)
  have hRtarget (i : Fin 2) (sign : Bool) : rad i sign ⊆ target := by
    fin_cases i
    · exact fun z hz => hQtarget false sign (hTgt0 false sign hz)
    · exact fun z hz => hQtarget sign false (hTgt1 sign false hz)
  have hKeepRadius (i : Fin 2) (sign : Bool) (x : signedTubeRadius i sign) :
      (G' ⟨x, signedTubeRadius_subset_diamond i sign x.property⟩ : E) = er i sign x := by
    fin_cases i
    · exact (hKeep false sign ⟨x, hSrc0 false sign x.property⟩).trans (hkeep0 false sign x)
    · exact (hKeep sign false ⟨x, hSrc1 sign false x.property⟩).trans (hkeep1 sign false x)
  refine ⟨G', hG', f, er, hf, her, hKeep, hKeepRadius, ?_, ?_, herCenter, herEnd, houter⟩
  · intro eps delta x
    exact G'.mem_subset_iff_of_extension (f eps delta)
      (fun _ hx => mem_iUnion.mpr ⟨eps, mem_iUnion.mpr ⟨delta, hx⟩⟩)
      (hQtarget eps delta) (fun z => Subtype.ext (hKeep eps delta z)) x
  · intro i sign x
    exact G'.mem_subset_iff_of_extension (er i sign) (signedTubeRadius_subset_diamond i sign)
      (hRtarget i sign) (fun z => Subtype.ext (hKeepRadius i sign z)) x

end PoincareConjecture.M76.Dehn
