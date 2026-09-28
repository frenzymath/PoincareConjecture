import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.BandCoverage

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel SphereSurgeryCoreCap Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem flatten_height (data : TerminalSaddleData M P p e) (y : E3) :
    data.toTerminalSaddleGeometry.flatten y 2 = inner Real (M.v : E3) y :=
  (data.frame_height (data.D y)).trans (data.D_height y)

theorem terminal_model_upper_level_eq_rims
    (data : TerminalSaddleData M P p e)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    {q : S2 | inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) =
        data.ends.upperCut} =
      ⋃ j : data.ends.UpperCutIndex,
        data.modelDisk (data.labels.symm (.inr j)) '' sphere (0 : E2) 1 := by
  let d := data.toTerminalSaddleGeometry
  have hb : data.ends.upperCut ∈ d.I := ⟨data.ends.cuts_lt.le, le_rfl⟩
  ext q
  constructor
  · intro hq
    have hy : d.flatten (d.filledModel q) ∈ d.modelBand := by
      refine mem_iUnion.mpr ⟨data.ends.upperCut, mem_iUnion.mpr ⟨hb, ?_⟩⟩
      refine ⟨?_, (flatten_height data _).trans hq⟩
      change Saddle.toE3 (Saddle.toE2 (d.flatten (d.filledModel q))) data.ends.upperCut ∈
        d.flatten '' (d.filledModel '' sphere (0 : E3) 1)
      have hc : Saddle.toE3 (Saddle.toE2 (d.flatten (d.filledModel q))) data.ends.upperCut =
          d.flatten (d.filledModel q) := by
        rw [← hq, ← flatten_height data]
        ext k
        fin_cases k <;> rfl
      rw [hc]
      exact mem_image_of_mem _ (mem_image_of_mem _ q.property)
    rw [← terminal_band_image data Φ χ H hH hχ hplanar] at hy
    obtain ⟨y, hy, hHy⟩ := hy
    obtain ⟨z, hz⟩ := mem_iUnion.mp hy
    obtain ⟨hzI, hy⟩ := mem_iUnion.mp hz
    obtain ⟨w, ⟨a, rfl⟩, hw⟩ := hy.1
    have hwy : d.flatten (g a) = y := by
      rw [hw]
      ext k
      fin_cases k
      · rfl
      · rfl
      · exact hy.2.symm
    have ha : inner Real (M.v : E3) (g a) = data.ends.upperCut := by
      have ht := congrArg (fun x : E3 => x 2) hHy
      rw [hH] at ht
      change y 2 = d.flatten (d.filledModel q) 2 at ht
      rw [← hwy, flatten_height, flatten_height] at ht
      exact ht.trans hq
    have hac : a ∈ ⋃ j, range (data.ends.upperCutCircle j) := by
      rw [data.ends.iUnion_range_upperCutCircle]
      exact ha
    obtain ⟨j, c, rfl⟩ := mem_iUnion.mp hac
    let i := data.labels.symm (.inr j)
    have hlabel : data.labels i = .inr j := data.labels.apply_symm_apply _
    have hrim : d.flatten (d.filledModel q) ∈
        range (fun c : S1 => d.flatten (d.filledModel (data.modelDisk i c))) := by
      rw [← terminal_labeled_cutCircle_range data Φ χ H hH hχ hplanar hlabels i]
      refine ⟨c, ?_⟩
      simp only [terminalActualCutCircle, hlabel]
      change H (d.flatten (g (data.ends.upperCutCircle j c))) = _
      rw [hwy]
      exact hHy
    obtain ⟨x, hx⟩ := hrim
    exact mem_iUnion.mpr ⟨j, x, x.property,
      Subtype.val_injective (d.filledModel.injective (d.flatten.injective hx))⟩
  · intro hq
    obtain ⟨j, x, hx, rfl⟩ := mem_iUnion.mp hq
    exact (terminal_labeled_model_upper_boundary data Φ χ H hH hχ hplanar hlabels
      (data.labels.symm (.inr j)) j (data.labels.apply_symm_apply _)).2 x hx

theorem exists_terminal_upper_prepared_model_slice_coverage
    (data : TerminalSaddleData M P p e)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    {r : Real} (hr : 0 < r)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y)
    (C : data.ends.UpperCutIndex → OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : ∀ j, (C j).source = univ ×ˢ Ioo (-r) r)
    (hcyl : ∀ j q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
        (-data.ends.upperCut + z) • (-(M.v : E3)) +
          ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3))
    (hCrim : ∀ j, range (fun q : S1 => C j (q, 0)) =
      data.modelDisk (data.labels.symm (.inr j)) '' sphere (0 : E2) 1) :
    ∃ δ : Real, 0 < δ ∧ δ < r ∧ ∀ z ∈ Icc (-δ) δ,
      (fun q : S2 => Q (data.toTerminalSaddleGeometry.filledModel q)) ''
        {q : S2 | inner Real (-(M.v : E3)) (data.toTerminalSaddleGeometry.filledModel q) =
          -data.ends.upperCut + z} =
      ⋃ j, range (fun q : S1 => (-data.ends.upperCut + z) • (-(M.v : E3)) +
        ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
          (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) := by
  have hQneg (y : E3) : inner Real (-(M.v : E3)) (Q y) = inner Real (-(M.v : E3)) y := by
    simp only [inner_neg_left, hQ]
  let m : S2 → E3 := fun q => data.toTerminalSaddleGeometry.filledModel q
  let h : S2 → Real := fun q => inner Real (-(M.v : E3)) (m q)
  have hh : Continuous h := continuous_const.inner
    (data.toTerminalSaddleGeometry.filledModel.contMDiff.continuous.comp continuous_subtype_val)
  have hCh (j) (q : S1) (z : Real) (hz : z ∈ Ioo (-r) r) :
      h (C j (q, z)) = -data.ends.upperCut + z := by
    have ht := congrArg Prod.fst ((heightCoordinates (by simpa only [norm_neg] using norm_eq_of_mem_sphere M.v)).symm_apply_apply
      (-data.ends.upperCut + z, (Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
        (m (C j (q, 0)))))
    change inner Real (-(M.v : E3)) ((-data.ends.upperCut + z) • (-(M.v : E3)) +
      ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto (m (C j (q, 0))) : E3)) = _ at ht
    change inner Real (-(M.v : E3)) (m (C j (q, z))) = _
    rw [← hQneg, hcyl j q z hz]
    exact ht
  have hcover : {q | h q = -data.ends.upperCut} ⊆ ⋃ j, range (fun q : S1 => C j (q, 0)) := by
    change {q : S2 | inner Real (-(M.v : E3)) (data.toTerminalSaddleGeometry.filledModel q) = _} ⊆ _
    have heq : {q : S2 | inner Real (-(M.v : E3)) (data.toTerminalSaddleGeometry.filledModel q) =
        -data.ends.upperCut} =
        {q : S2 | inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) =
          data.ends.upperCut} := by
      ext q
      simp only [mem_ofPred_eq, inner_neg_left, neg_inj]
    rw [heq, terminal_model_upper_level_eq_rims data Φ χ H hH hχ hplanar hlabels]
    exact iUnion_mono (fun j => (hCrim j).ge)
  obtain ⟨δ, hδ, hδr, hlevels⟩ := exists_annular_family_full_slice_coverage hh hr C hCs hCh hcover
  refine ⟨δ, hδ, hδr, ?_⟩
  intro z hz
  change (fun q => Q (m q)) '' {q | h q = -data.ends.upperCut + z} = _
  rw [hlevels z hz, image_iUnion]
  apply iUnion_congr
  intro j
  rw [← range_comp]
  apply congrArg range
  funext q
  exact hcyl j q z ⟨by linarith [hz.1], by linarith [hz.2]⟩

theorem exists_terminal_upper_prepared_modelBand_coverage
    (data : TerminalSaddleData M P p e)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    {r : Real} (hr : 0 < r)
    (Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hQ : ∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y)
    (C : data.ends.UpperCutIndex → OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : ∀ j, (C j).source = univ ×ˢ Ioo (-r) r)
    (hcyl : ∀ j q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
        (-data.ends.upperCut + z) • (-(M.v : E3)) +
          ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3))
    (hCrim : ∀ j, range (fun q : S1 => C j (q, 0)) =
      data.modelDisk (data.labels.symm (.inr j)) '' sphere (0 : E2) 1) :
    ∃ δ : Real, 0 < δ ∧ δ < r ∧ δ < data.ends.upperCut - data.ends.lowerCut ∧
      ∀ z ∈ Icc 0 δ,
        (Q '' (data.toTerminalSaddleGeometry.flatten.symm ''
          data.toTerminalSaddleGeometry.modelBand)) ∩
            {y | inner Real (-(M.v : E3)) y = -data.ends.upperCut + z} =
        ⋃ j, range (fun q : S1 => (-data.ends.upperCut + z) • (-(M.v : E3)) +
          ((Hemisphere.Plane (-(M.v : E3))).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) := by
  have hQneg (y : E3) : inner Real (-(M.v : E3)) (Q y) = inner Real (-(M.v : E3)) y := by
    simp only [inner_neg_left, hQ]
  obtain ⟨ε, hε, hεr, hlevels⟩ :=
    exists_terminal_upper_prepared_model_slice_coverage data Φ χ H hH hχ hplanar hlabels
      hr Q hQ C hCs hcyl hCrim
  let δ := min ε (data.ends.upperCut - data.ends.lowerCut) / 2
  have hgap : 0 < data.ends.upperCut - data.ends.lowerCut := sub_pos.mpr data.ends.cuts_lt
  have hδ : 0 < δ := half_pos (lt_min hε hgap)
  have hδε : δ < ε := by dsimp [δ]; linarith [min_le_left ε (data.ends.upperCut - data.ends.lowerCut)]
  have hδgap : δ < data.ends.upperCut - data.ends.lowerCut := by
    dsimp [δ]; linarith [min_le_right ε (data.ends.upperCut - data.ends.lowerCut)]
  refine ⟨δ, hδ, hδε.trans hεr, hδgap, ?_⟩
  intro z hz
  rw [← hlevels z ⟨by linarith [hz.1], hz.2.trans hδε.le⟩]
  ext y
  constructor
  · rintro ⟨⟨_, ⟨x, hx, rfl⟩, rfl⟩, hy⟩
    have hx' : data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.flatten.symm x) ∈
          data.toTerminalSaddleGeometry.modelBand := by simpa only [Diffeomorph.apply_symm_apply] using hx
    obtain ⟨⟨q, hq, heq⟩, _⟩ := (terminal_physical_modelBand_mem_iff data _).mp hx'
    refine ⟨⟨q, hq⟩, ?_, congrArg Q heq⟩
    change inner Real (-(M.v : E3)) (data.toTerminalSaddleGeometry.filledModel q) = _
    rw [heq, ← hQneg]
    exact hy
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨data.toTerminalSaddleGeometry.filledModel q, ?_, rfl⟩, ?_⟩
    · refine ⟨data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel q), ?_, Diffeomorph.symm_apply_apply _ _⟩
      apply (terminal_physical_modelBand_mem_iff data _).mpr
      refine ⟨mem_image_of_mem _ q.property, ?_⟩
      change data.ends.lowerCut ≤ _ ∧ _ ≤ data.ends.upperCut
      have hqh : inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) =
          data.ends.upperCut - z := by
        change inner Real (-(M.v : E3)) (data.toTerminalSaddleGeometry.filledModel q) =
          -data.ends.upperCut + z at hq
        rw [inner_neg_left] at hq
        linarith
      rw [hqh]
      constructor <;> linarith [hz.1, hz.2]
    · change inner Real (-(M.v : E3)) (Q (data.toTerminalSaddleGeometry.filledModel q)) = _
      rw [hQneg]
      exact hq

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies
