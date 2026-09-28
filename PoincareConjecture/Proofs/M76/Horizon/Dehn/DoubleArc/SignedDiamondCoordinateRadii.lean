import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedCoordinateSectors
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondRadiusMaps









set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem signedDiamond_reflection_coordinate_quarters
    {E : Type*} [TopologicalSpace E] (J : Set E) (c : Fin 2 → E → ℝ)
    (eta : Fin 2 → Bool) (G : signedTubeDiamond ≃ₜ J)
    (hQ : ∀ eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G x : E) ∈ signedCoordinateSector J c eta eps delta)
    (eps delta : Bool) (x : signedTubeDiamond) :
    (x : P2) ∈ signedTubeQuarter eps delta ↔
      ((signedTubeDiamondReflection eta).trans G x : E) ∈
        signedCoordinateSector J c (fun _ => true) eps delta := by
  have h := signedTubeDiamondReflection_trans_quarter G
    (signedCoordinateSector J c eta) hQ eta eps delta x
  simp only [signedCoordinateSector] at h ⊢
  simp only [signedTubeReindex_involutive] at h
  simpa only [signedTubeReindex, ↓reduceIte] using h

theorem signedDiamond_coordinate_radius_iff
    {E : Type*} [TopologicalSpace E] (J : Set E) (c : Fin 2 → E → ℝ)
    (G : signedTubeDiamond ≃ₜ J)
    (hQ : ∀ eps delta (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter eps delta ↔
        (G x : E) ∈ signedCoordinateSector J c (fun _ => true) eps delta)
    (i : Fin 2) (sign : Bool) (x : signedTubeDiamond) :
    (x : P2) ∈ signedTubeRadius i sign ↔
      (G x : E) ∈ signedCoordinateFace J c (fun _ => true) i sign := by
  fin_cases i
  · change (x : P2) ∈ signedTubeRadius 0 sign ↔
      (G x : E) ∈ signedCoordinateFace J c (fun _ => true) 0 sign
    rw [← signedTube_quarter_inter_eps false sign]
    change ((x : P2) ∈ signedTubeQuarter false sign ∧
      (x : P2) ∈ signedTubeQuarter (!false) sign) ↔ _
    rw [hQ, hQ]
    exact Set.ext_iff.mp (signedCoordinateSector_incidence J c (fun _ => true) false sign).2.1 (G x)
  · change (x : P2) ∈ signedTubeRadius 1 sign ↔
      (G x : E) ∈ signedCoordinateFace J c (fun _ => true) 1 sign
    rw [← signedTube_quarter_inter_delta sign false]
    change ((x : P2) ∈ signedTubeQuarter sign false ∧
      (x : P2) ∈ signedTubeQuarter sign (!false)) ↔ _
    rw [hQ, hQ]
    exact Set.ext_iff.mp (signedCoordinateSector_incidence J c (fun _ => true) sign false).1 (G x)

theorem isFinitePLBallPair_signed_diamond_radius_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J r : Set E} (G : signedTubeDiamond ≃ₜ J) (hG : G.IsFinitePL)
    (i : Fin 2) (sign : Bool) (hr : r ⊆ J)
    (hmem : ∀ x : signedTubeDiamond,
      (x : P2) ∈ signedTubeRadius i sign ↔ (G x : E) ∈ r) :
    IsFinitePLBallPair ℝ r
      {(G ⟨(0, 0), signedTubeRadius_subset_diamond i sign (left_mem_segment ℝ _ _)⟩ : E),
        (G ⟨signedTubeCorner i sign,
          signedTubeRadius_subset_diamond i sign (right_mem_segment ℝ _ _)⟩ : E)} := by
  obtain ⟨f, hf, hval⟩ := hG
  have hfi : InjOn f signedTubeDiamond := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (G.injective (Subtype.ext
      ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have himage : f '' signedTubeRadius i sign = r := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hval ⟨x, signedTubeRadius_subset_diamond i sign hx⟩]
      exact (hmem _).mp hx
    · intro hy
      let x := G.symm ⟨y, hr hy⟩
      have hGx : (G x : E) = y := congrArg Subtype.val (G.apply_symm_apply _)
      exact ⟨x, (hmem x).mpr (hGx.symm ▸ hy), (hval x).symm.trans hGx⟩
  have hball := (signedTube_radius_ball i sign).image_of_subset hf
    (signedTubeRadius_subset_diamond i sign) hfi
  rw [himage, image_pair] at hball
  rw [← hval ⟨(0, 0), signedTubeRadius_subset_diamond i sign (left_mem_segment ℝ _ _)⟩,
    ← hval ⟨signedTubeCorner i sign,
      signedTubeRadius_subset_diamond i sign (right_mem_segment ℝ _ _)⟩] at hball
  exact hball

end PoincareConjecture.M76.Dehn
