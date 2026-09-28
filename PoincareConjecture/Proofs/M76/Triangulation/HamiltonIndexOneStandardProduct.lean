import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMeridianBand
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem standardMeridianBandMap_product_properties {width : ℝ}
    (hwidth : 0 < width) (hsmall : width ≤ (1 / 4 : ℝ)) :
    FinitePiecewiseAffineOn standardMeridianBandMap (D2 ×ˢ Icc (-width) width) ∧
      InjOn standardMeridianBandMap (D2 ×ˢ Icc (-width) width) ∧
      MapsTo standardMeridianBandMap (D2 ×ˢ Icc (-width) width) squareShell ∧
      (∀ p ∈ D2 ×ˢ Icc (-width) width,
        standardMeridianBandMap p ∈ frontier squareShell ↔ p.1 ∈ Q2) ∧
      IsOpen ((Subtype.val : squareShell → W) ⁻¹'
        (standardMeridianBandMap '' (D2 ×ˢ Ioo (-width) width))) ∧
      ∀ x ∈ D2, standardMeridianBandMap (x, 0) =
        (x 0, (-((x 1 + 7) / 4), -((x 1 + 7) / 4))) := by
  obtain ⟨H, hHval, hlarge, hHPL, himage, hzero⟩ :=
    exists_standard_meridian_ambient_chart
  have hsource : D2 ×ˢ Icc (-width) width ⊆ H.source := by
    intro p hp
    exact hlarge ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hfront : H.IsImage (Q2 ×ˢ (univ : Set ℝ)) (frontier squareShell) := by
    simpa only [frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero] using himage.frontier
  have hball := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
    (isFinitePLBallPair_Icc (show -width < width by linarith))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  have hPL : FinitePiecewiseAffineOn H (D2 ×ˢ Icc (-width) width) := by
    rw [← hKs]
    exact hHPL.finitePiecewiseAffineOn K hK (hKs.subset.trans hsource)
  have hopen : IsOpen ((Subtype.val : squareShell → W) ⁻¹'
      (H '' (D2 ×ˢ Ioo (-width) width))) := by
    let U : Set W := H.target ∩ H.symm ⁻¹' (univ ×ˢ Ioo (-width) width)
    have hU : IsOpen U := H.isOpen_inter_preimage_symm (isOpen_univ.prod isOpen_Ioo)
    have heq : H '' (D2 ×ˢ Ioo (-width) width) = squareShell ∩ U := by
      ext y
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hpS := hsource ⟨hp.1, Ioo_subset_Icc_self hp.2⟩
        refine ⟨(himage.apply_mem_iff hpS).mpr ⟨hp.1, mem_univ _⟩,
          H.map_source hpS, ?_⟩
        change H.symm (H p) ∈ univ ×ˢ Ioo (-width) width
        rw [H.left_inv hpS]
        exact ⟨mem_univ _, hp.2⟩
      · rintro ⟨hy, hyT, hyw⟩
        have hpS := H.map_target hyT
        have hpD := (himage.apply_mem_iff hpS).mp (by rwa [H.right_inv hyT])
        exact ⟨H.symm y, ⟨hpD.1, hyw.2⟩, H.right_inv hyT⟩
    have heq' : (Subtype.val : squareShell → W) ⁻¹'
        (H '' (D2 ×ˢ Ioo (-width) width)) =
        (Subtype.val : squareShell → W) ⁻¹' U := by
      ext y
      rw [heq]
      exact and_iff_right y.property
    rw [heq']
    exact hU.preimage continuous_subtype_val
  rw [← hHval]
  refine ⟨hPL, H.injOn.mono hsource, ?_, ?_, hopen, hzero⟩
  · intro p hp
    exact (himage.apply_mem_iff (hsource hp)).mpr ⟨hp.1, mem_univ _⟩
  · intro p hp
    exact (hfront.apply_mem_iff (hsource hp)).trans (and_iff_left (mem_univ p.2))

end PoincareConjecture.M76.HamiltonIndexOne
