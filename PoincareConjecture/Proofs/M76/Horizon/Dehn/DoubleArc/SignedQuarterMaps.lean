import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcTubeJointMaps

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_signed_quarter_map_on_radii
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (m : E) (a : Fin 2 → Bool → E) (rad : Fin 2 → Bool → Set E)
    (Q : Bool → Bool → Set E) (q : Set E) (eps delta : Bool)
    (hQB : IsFinitePLBallPair P2 (Q eps delta)
      ((Q eps delta ∩ q) ∪ (rad 0 delta ∪ rad 1 eps)))
    (hOB : IsFinitePLBallPair ℝ (Q eps delta ∩ q) {a 0 delta, a 1 eps})
    (hUO : (rad 0 delta ∪ rad 1 eps) ∩ (Q eps delta ∩ q) = {a 0 delta, a 1 eps})
    (hCross : rad 0 delta ∩ rad 1 eps = {m})
    (e : ∀ i sign, signedTubeRadius i sign ≃ₜ rad i sign)
    (he : ∀ i sign, (e i sign).IsFinitePL)
    (heCenter : ∀ i sign (x : signedTubeRadius i sign),
      (e i sign x : E) = m ↔ (x : P2) = (0, 0))
    (heEnd : ∀ i sign (x : signedTubeRadius i sign),
      (e i sign x : E) = a i sign ↔ (x : P2) = signedTubeCorner i sign) :
    ∃ f : signedTubeQuarter eps delta ≃ₜ Q eps delta, f.IsFinitePL ∧
      (∀ x : signedTubeRadius 0 delta,
        (f ⟨x, (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inl x.property))⟩ : E) =
          e 0 delta x) ∧
      (∀ x : signedTubeRadius 1 eps,
        (f ⟨x, (signedTube_quarter_ball eps delta).1 (Or.inr (Or.inr x.property))⟩ : E) =
          e 1 eps x) ∧
      (∀ x : signedTubeQuarter eps delta,
        (x : P2) ∈ signedTubeOuterArc eps delta ↔ (f x : E) ∈ Q eps delta ∩ q) ∧
      ∀ x : signedTubeQuarter eps delta,
        (x : P2) ∈ signedTubeRadialRim eps delta ↔ (f x : E) ∈ rad 0 delta ∪ rad 1 eps := by
  have hSource := signedTube_cross_radius_inter eps delta
  have hm1 : m ∈ rad 1 eps := by
    have h := (e 1 eps ⟨(0, 0), left_mem_segment ℝ _ _⟩).property
    rwa [(heCenter 1 eps ⟨(0, 0), left_mem_segment ℝ _ _⟩).mpr rfl] at h
  have hoverlap (x : signedTubeRadius 0 delta) :
      (x : P2) ∈ signedTubeRadius 1 eps ↔ (e 0 delta x : E) ∈ rad 1 eps := by
    have hs : (x : P2) ∈ signedTubeRadius 1 eps ↔ (x : P2) = (0, 0) := by
      constructor
      · intro hx
        exact hSource.subset ⟨x.property, hx⟩
      · intro hx
        rw [hx]
        exact left_mem_segment ℝ _ _
    have ht : (e 0 delta x : E) ∈ rad 1 eps ↔ (e 0 delta x : E) = m := by
      constructor
      · intro hx
        exact hCross.subset ⟨(e 0 delta x).property, hx⟩
      · intro hx
        rw [hx]
        exact hm1
    exact hs.trans ((heCenter 0 delta x).symm.trans ht.symm)
  have hagree (x : P2) (hx : x ∈ signedTubeRadius 0 delta)
      (hy : x ∈ signedTubeRadius 1 eps) :
      (e 0 delta ⟨x, hx⟩ : E) = e 1 eps ⟨x, hy⟩ := by
    have hzero : x = (0, 0) := hSource.subset ⟨hx, hy⟩
    exact ((heCenter 0 delta ⟨x, hx⟩).mpr hzero).trans
      ((heCenter 1 eps ⟨x, hy⟩).mpr hzero).symm
  obtain ⟨r, hr, hr0, hr1⟩ := Homeomorph.exists_union_finitePL
    (e 0 delta) (e 1 eps) (he 0 delta) (he 1 eps) hoverlap hagree
  have hEnd0 : signedTubeCorner 0 delta ∈ signedTubeRadialRim eps delta :=
    Or.inl (right_mem_segment ℝ _ _)
  have hEnd1 : signedTubeCorner 1 eps ∈ signedTubeRadialRim eps delta :=
    Or.inr (right_mem_segment ℝ _ _)
  have hrEnd0 : (r ⟨signedTubeCorner 0 delta, hEnd0⟩ : E) = a 0 delta :=
    (hr0 ⟨signedTubeCorner 0 delta, right_mem_segment ℝ _ _⟩).trans
      ((heEnd 0 delta ⟨signedTubeCorner 0 delta, right_mem_segment ℝ _ _⟩).mpr rfl)
  have hrEnd1 : (r ⟨signedTubeCorner 1 eps, hEnd1⟩ : E) = a 1 eps :=
    (hr1 ⟨signedTubeCorner 1 eps, right_mem_segment ℝ _ _⟩).trans
      ((heEnd 1 eps ⟨signedTubeCorner 1 eps, right_mem_segment ℝ _ _⟩).mpr rfl)
  have hrBoundary (x : signedTubeRadialRim eps delta) :
      (x : P2) ∈ ({signedTubeCorner 0 delta, signedTubeCorner 1 eps} : Set P2) ↔
        (r x : E) ∈ ({a 0 delta, a 1 eps} : Set E) := by
    have h0 : (r x : E) = a 0 delta ↔ (x : P2) = signedTubeCorner 0 delta := by
      constructor
      · intro h
        exact congrArg Subtype.val (r.injective (Subtype.ext (h.trans hrEnd0.symm)))
      · intro h
        exact (congrArg (fun y : signedTubeRadialRim eps delta => (r y : E))
          (show x = ⟨signedTubeCorner 0 delta, hEnd0⟩ from Subtype.ext h)).trans hrEnd0
    have h1 : (r x : E) = a 1 eps ↔ (x : P2) = signedTubeCorner 1 eps := by
      constructor
      · intro h
        exact congrArg Subtype.val (r.injective (Subtype.ext (h.trans hrEnd1.symm)))
      · intro h
        exact (congrArg (fun y : signedTubeRadialRim eps delta => (r y : E))
          (show x = ⟨signedTubeCorner 1 eps, hEnd1⟩ from Subtype.ext h)).trans hrEnd1
    simp only [mem_insert_iff, mem_singleton_iff, h0, h1]
  have hOuter : IsFinitePLBallPair ℝ (signedTubeOuterArc eps delta)
      {signedTubeCorner 0 delta, signedTubeCorner 1 eps} := by
    simpa only [signedTubeOuterArc, pair_comm] using signedTube_segment_ball
      (signedTubeCorner 1 eps) (signedTubeCorner 0 delta)
      (signedTube_corner_ne_corner 1 eps 0 delta (by simp))
  obtain ⟨f, hf, hfR, hfOuter, hfRadial⟩ :=
    (signedTube_quarter_ball eps delta).exists_extension_of_boundary_piece
      hQB hOuter hOB (signedTube_outer_inter_rim eps delta)
      (by simpa only [inter_comm] using hUO) r hr hrBoundary
  refine ⟨f, hf, ?_, ?_, hfOuter, hfRadial⟩
  · intro x
    exact (congrArg Subtype.val (hfR ⟨x, Or.inl x.property⟩)).trans (hr0 x)
  · intro x
    exact (congrArg Subtype.val (hfR ⟨x, Or.inr x.property⟩)).trans (hr1 x)

end PoincareConjecture.M76.Dehn
