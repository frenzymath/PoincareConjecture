import PoincareConjecture.Proofs.M76.Mathlib.StableThreeTorus
import PoincareConjecture.Proofs.M76.Mathlib.ThickTorusEmbedding
import PoincareConjecture.Proofs.M76.Mathlib.PuncturedThreeTorusPLComposition











set_option autoImplicit false

open Set Geometry

namespace StableTorus









theorem exists_punctured_threeTorus_PL_immersion :
    letI : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
    let q := AddCircle.centeredCubeQuotient (4 * (16 : ℝ)) 0
    ∃ f : (Circle × Circle) × Circle → CubeShell.Ambient,
      IsLocalHomeomorphOn f {q}ᶜ ∧
      (∀ r s t : ℝ, |r| ≤ 1 / 64 → |s| ≤ 1 / 64 → |t| ≤ 1 / 64 →
        f (((r : Circle), (s : Circle)), (t : Circle)) = ((r, s), t)) ∧
      ∀ a b c : ℝ,
        let T := ((AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) a).prod
          (AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) b)).prod
            (AddCircle.openPartialHomeomorphCoe (4 * (16 : ℝ)) c)
        LocallyPiecewiseAffineOn (f ∘ T) (T.source ∩ T ⁻¹' {q}ᶜ) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let p : ℝ := 4 * 16
  let Q := AddCircle.quotientCharts p
  let A := prodCharts (prodCharts Q Q) Q
  let B := prodCharts (prodCharts (realCharts ℝ) Q) Q
  obtain ⟨g, hg, hgPL, hgbound, hgcore⟩ := exists_threeTorus_band_PL_immersion
  obtain ⟨H, hHS, _, hHcore, hHrawPL⟩ := ThickTorus.exists_openPartialHomeomorph
  have hHPL : PLInCharts B (realCharts CubeShell.Ambient) H H.source := by
    apply plInCharts_real_target B H H.source H.open_source H.continuousOn_toFun
    intro i
    exact hHrawPL i.1.2 i.2
  have hgimage : MapsTo g (threeBands (1 / 16)) H.source := by
    intro z hz
    rw [hHS]
    exact lt_of_le_of_lt (hgbound z hz) (by norm_num)
  have hband := (IsLocalHomeomorphOn.OpenPartialHomeomorph.isLocalHomeomorphOn H).comp hg hgimage
  have hbandPL := hHPL.comp_mapsTo hgPL
    (prodCharts_cover (prodCharts (realCharts ℝ) Q) Q
      (prodCharts_cover (realCharts ℝ) Q (realCharts_cover ℝ) (AddCircle.quotientCharts_cover p))
      (AddCircle.quotientCharts_cover p)) hgimage
  have hbands : threeBands (1 / 16) = TorusCube.crossingBands p (1 / 16) := by
    ext z
    simp only [threeBands, twoBands, arc, TorusCube.crossingBands, mem_union,
      mem_prod, mem_univ, and_true, true_and, or_assoc]
    rfl
  have hband' : IsLocalHomeomorphOn (H ∘ g) (TorusCube.crossingBands p (1 / 16)) :=
    hbands ▸ hband
  have hbandPL' : ∀ a b c : ℝ,
      let T := ((AddCircle.openPartialHomeomorphCoe p a).prod
        (AddCircle.openPartialHomeomorphCoe p b)).prod (AddCircle.openPartialHomeomorphCoe p c)
      LocallyPiecewiseAffineOn ((H ∘ g) ∘ T)
        (T.source ∩ T ⁻¹' TorusCube.crossingBands p (1 / 16)) := by
    intro a b c
    rw [← hbands]
    exact hbandPL.real_target_coordinates ((a, b), c)
  obtain ⟨f, hf, hfixed, hfPL⟩ := TorusCube.exists_punctured_PL_immersion_of_bands p
    (d := (1 / 16 : ℝ)) (by norm_num) (by norm_num [p]) (H ∘ g) hband' hbandPL'
  refine ⟨f, hf, ?_, hfPL⟩
  intro r s t hr hs ht
  have hr32 : r ∈ Ioo (-((1 / 16) / 2)) ((1 / 16) / 2) := by
    constructor <;> linarith [(abs_le.mp hr).1, (abs_le.mp hr).2]
  have hmem : (((r : Circle), (s : Circle)), (t : Circle)) ∈
      TorusCube.crossingBands p ((1 / 16) / 2) :=
    Or.inl ⟨r, hr32, rfl⟩
  rw [hfixed hmem]
  change H (g (((r : Circle), (s : Circle)), (t : Circle))) = _
  rw [hgcore r s t (by linarith)]
  exact hHcore r s t (by linarith) (by linarith) (by linarith)

end StableTorus
