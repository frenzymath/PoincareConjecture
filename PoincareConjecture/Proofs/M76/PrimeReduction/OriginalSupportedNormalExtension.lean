import PoincareConjecture.Proofs.M76.PrimeReduction.CoordinateNormalExtension
import PoincareConjecture.Proofs.M76.PrimeReduction.CompactFaceNormalBall
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartPLTransition










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)





theorem exists_original_supported_normal_extension_with_support_coordinates
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (T : P3 ≃ᴬ[ℝ] V3)
    {D rim : Set (ℝ × ℝ)} (hD : IsFinitePLBallPair (ℝ × ℝ) D rim)
    (h : D ≃ₜ D) (hh : h.IsFinitePL)
    (hfix : ∀ x : D, (x : ℝ × ℝ) ∈ rim → h x = x)
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ z ∈ D, T (z, 0) ∈ B.target ∧ B.symm (T (z, 0)) ∈ U) :
    ∃ r : ℝ, 0 < r ∧ T '' (D ×ˢ Icc (-r) r) ⊆ B.target ∧
      let C := (B.symm ∘ T) '' (D ×ˢ Icc (-r) r)
      IsCompact C ∧ C ⊆ U ∧
      ∃ F : X ≃ₜ X,
        (∀ x : D, F (B.symm (T ((x : ℝ × ℝ), 0))) =
          B.symm (T ((h x : ℝ × ℝ), 0))) ∧
        (∀ y ∉ C, F y = y) ∧ (∀ y ∉ U, F y = y) ∧
        (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3 := by
  obtain ⟨r, hr, _, hT, _, _, hCU, hcompact, _, hCball, _, _⟩ :=
    B.exists_compact_face_normal_ball T hD hU hzero
  let S := D ×ˢ Icc (-r) r
  have hTS : T '' S ⊆ B.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact hT hx
  obtain ⟨G, hGPL, hGzero, hGout, _⟩ :=
    exists_coordinate_normal_extension T hD h hh hfix hr
  have hGfix : EqOn G id (T '' S)ᶜ := by
    intro y hy
    exact hGout y (fun hi => hy (interior_subset hi))
  obtain ⟨F, hFB, hFout⟩ :=
    B.symm.exists_supported_chart_homeomorph G hCball.isCompact hTS hGfix
  have hforward (i j : ι) :
      (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3 :=
    B.symm.supported_chart_transition_mem_piecewiseAffineGroupoid
      (e i).symm (e j).symm G F hCball.isCompact hTS hGfix hFB hFout hGPL
      (hB i) (hB j) (he i j)
  have himage : B.symm '' (T '' S) = (B.symm ∘ T) '' S := image_image _ _ _
  have hFcompact (y : X) (hy : y ∉ (B.symm ∘ T) '' S) : F y = y :=
    hFout (fun hm => hy (himage ▸ hm))
  refine ⟨r, hr, hTS, hcompact, hCU, F, ?_, hFcompact, ?_, hforward, ?_⟩
  · intro x
    have hx : T ((x : ℝ × ℝ), 0) ∈ B.target := (hzero x x.property).1
    have hy : B.symm (T ((x : ℝ × ℝ), 0)) ∈ B.source := B.mapsTo_symm hx
    have hval := hFB hy
    change F (B.symm (T ((x : ℝ × ℝ), 0))) =
      B.symm (G (B (B.symm (T ((x : ℝ × ℝ), 0))))) at hval
    rw [B.right_inv hx, hGzero x] at hval
    exact hval
  · intro y hy
    exact hFcompact y (fun hm => hy (hCU hm))
  · intro i j
    have hinv := (piecewiseAffineGroupoid V3).symm (hforward j i)
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph] using hinv



theorem exists_original_supported_normal_extension
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (B : OpenPartialHomeomorph X V3)
    (hB : ∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3)
    (T : P3 ≃ᴬ[ℝ] V3)
    {D rim : Set (ℝ × ℝ)} (hD : IsFinitePLBallPair (ℝ × ℝ) D rim)
    (h : D ≃ₜ D) (hh : h.IsFinitePL)
    (hfix : ∀ x : D, (x : ℝ × ℝ) ∈ rim → h x = x)
    {U : Set X} (hU : IsOpen U)
    (hzero : ∀ z ∈ D, T (z, 0) ∈ B.target ∧ B.symm (T (z, 0)) ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      let C := (B.symm ∘ T) '' (D ×ˢ Icc (-r) r)
      IsCompact C ∧ C ⊆ U ∧
      ∃ F : X ≃ₜ X,
        (∀ x : D, F (B.symm (T ((x : ℝ × ℝ), 0))) =
          B.symm (T ((h x : ℝ × ℝ), 0))) ∧
        (∀ y ∉ C, F y = y) ∧ (∀ y ∉ U, F y = y) ∧
        (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3) ∧
        ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
          piecewiseAffineGroupoid V3 := by
  obtain ⟨r, hr, _, hrest⟩ :=
    exists_original_supported_normal_extension_with_support_coordinates e he B hB T
      hD h hh hfix hU hzero
  exact ⟨r, hr, hrest⟩

end PoincareConjecture.M76
