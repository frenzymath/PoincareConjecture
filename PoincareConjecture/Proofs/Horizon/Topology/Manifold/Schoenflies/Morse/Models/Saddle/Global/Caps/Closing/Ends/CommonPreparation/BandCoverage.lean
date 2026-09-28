import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.TerminalFamily

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

theorem exists_annular_family_full_slice_coverage
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {ι : Type*}
    {h : X → Real} (hh : Continuous h) {b r : Real} (hr : 0 < r)
    (C : ι → OpenPartialHomeomorph (S1 × Real) X)
    (hCs : ∀ i, (C i).source = univ ×ˢ Ioo (-r) r)
    (hCh : ∀ i q z, z ∈ Ioo (-r) r → h (C i (q, z)) = b + z)
    (hcover : {x | h x = b} ⊆ ⋃ i, range (fun q : S1 => C i (q, 0))) :
    ∃ δ : Real, 0 < δ ∧ δ < r ∧ ∀ z ∈ Icc (-δ) δ,
      {x | h x = b + z} = ⋃ i, range (fun q : S1 => C i (q, z)) := by
  let U : Set X := ⋃ i, (C i).target
  have hU : IsOpen U := isOpen_iUnion (fun i => (C i).open_target)
  have hzero : b ∉ h '' Uᶜ := by
    rintro ⟨x, hx, hxb⟩
    obtain ⟨i, q, rfl⟩ := mem_iUnion.mp (hcover hxb)
    apply hx
    exact mem_iUnion.mpr ⟨i, (C i).map_source (by rw [hCs]; exact ⟨mem_univ _, by constructor <;> linarith⟩)⟩
  have hclosed : IsClosed (h '' Uᶜ) := (hU.isClosed_compl.isCompact.image hh).isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl b hzero
  let δ := min ε r / 2
  have hδ : 0 < δ := half_pos (lt_min hε hr)
  have hδε : δ < ε := by dsimp [δ]; linarith [min_le_left ε r]
  have hδr : δ < r := by dsimp [δ]; linarith [min_le_right ε r]
  refine ⟨δ, hδ, hδr, ?_⟩
  intro z hz
  have hzr : z ∈ Ioo (-r) r := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  ext x
  constructor
  · intro hx
    have hxU : x ∈ U := by
      by_contra hxU
      have hb : b + z ∈ ball b ε := by
        rw [mem_ball, Real.dist_eq, add_sub_cancel_left]
        exact (abs_le.mpr hz).trans_lt hδε
      exact hball hb ⟨x, hxU, hx⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
    let q := (C i).symm x
    have hq : q ∈ (C i).source := (C i).map_target hi
    have hqz : q.2 = z := by
      have ht := hCh i q.1 q.2 (by rw [hCs] at hq; exact hq.2)
      rw [(C i).right_inv hi] at ht
      change h x = b + z at hx
      linarith
    exact mem_iUnion.mpr ⟨i, q.1, by rw [← hqz]; exact (C i).right_inv hi⟩
  · rintro hx
    obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hx
    exact hCh i q z hzr

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem flatten_height (data : TerminalSaddleData M P p e) (y : E3) :
    data.toTerminalSaddleGeometry.flatten y 2 = inner Real (M.v : E3) y :=
  (data.frame_height (data.D y)).trans (data.D_height y)

theorem terminal_physical_modelBand_mem_iff (data : TerminalSaddleData M P p e) (y : E3) :
    data.toTerminalSaddleGeometry.flatten y ∈ data.toTerminalSaddleGeometry.modelBand ↔
      y ∈ data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1 ∧
        inner Real (M.v : E3) y ∈ data.toTerminalSaddleGeometry.I := by
  let d := data.toTerminalSaddleGeometry
  have hc (z : E3) : Saddle.toE3 (Saddle.toE2 z) (z 2) = z := by
    ext k
    fin_cases k <;> rfl
  change d.flatten y ∈ ⋃ z ∈ d.I, Saddle.slice (d.B z) z ↔ _
  simp only [mem_iUnion]
  constructor
  · rintro ⟨z, hz, hy, hyz⟩
    subst z
    change Saddle.toE3 (Saddle.toE2 (d.flatten y)) (d.flatten y 2) ∈
      d.flatten '' (d.filledModel '' sphere (0 : E3) 1) at hy
    rw [hc] at hy
    obtain ⟨x, hx, heq⟩ := hy
    exact ⟨d.flatten.injective heq ▸ hx, (flatten_height data y) ▸ hz⟩
  · rintro ⟨hy, hh⟩
    refine ⟨inner Real (M.v : E3) y, hh, ?_, flatten_height data y⟩
    change Saddle.toE3 (Saddle.toE2 (d.flatten y)) (inner Real (M.v : E3) y) ∈
      d.flatten '' (d.filledModel '' sphere (0 : E3) 1)
    rw [← flatten_height data, hc]
    exact mem_image_of_mem _ hy

theorem terminal_model_lower_level_eq_rims
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
        data.ends.lowerCut} =
      ⋃ j : data.ends.LowerCutIndex,
        data.modelDisk (data.labels.symm (.inl j)) '' sphere (0 : E2) 1 := by
  let d := data.toTerminalSaddleGeometry
  have hb : data.ends.lowerCut ∈ d.I := ⟨le_rfl, data.ends.cuts_lt.le⟩
  ext q
  constructor
  · intro hq
    have hy : d.flatten (d.filledModel q) ∈ d.modelBand := by
      refine mem_iUnion.mpr ⟨data.ends.lowerCut, mem_iUnion.mpr ⟨hb, ?_⟩⟩
      refine ⟨?_, (flatten_height data _).trans hq⟩
      change Saddle.toE3 (Saddle.toE2 (d.flatten (d.filledModel q))) data.ends.lowerCut ∈
        d.flatten '' (d.filledModel '' sphere (0 : E3) 1)
      have hc : Saddle.toE3 (Saddle.toE2 (d.flatten (d.filledModel q))) data.ends.lowerCut =
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
    have ha : inner Real (M.v : E3) (g a) = data.ends.lowerCut := by
      have ht := congrArg (fun x : E3 => x 2) hHy
      rw [hH] at ht
      change y 2 = d.flatten (d.filledModel q) 2 at ht
      rw [← hwy, flatten_height, flatten_height] at ht
      exact ht.trans hq
    have hac : a ∈ ⋃ j, range (data.ends.lowerCutCircle j) := by
      rw [data.ends.iUnion_range_lowerCutCircle]
      exact ha
    obtain ⟨j, c, rfl⟩ := mem_iUnion.mp hac
    let i := data.labels.symm (.inl j)
    have hlabel : data.labels i = .inl j := data.labels.apply_symm_apply _
    have hrim : d.flatten (d.filledModel q) ∈
        range (fun c : S1 => d.flatten (d.filledModel (data.modelDisk i c))) := by
      rw [← terminal_labeled_cutCircle_range data Φ χ H hH hχ hplanar hlabels i]
      refine ⟨c, ?_⟩
      simp only [terminalActualCutCircle, hlabel]
      change H (d.flatten (g (data.ends.lowerCutCircle j c))) = _
      rw [hwy]
      exact hHy
    obtain ⟨x, hx⟩ := hrim
    exact mem_iUnion.mpr ⟨j, x, x.property,
      Subtype.val_injective (d.filledModel.injective (d.flatten.injective hx))⟩
  · intro hq
    obtain ⟨j, x, hx, rfl⟩ := mem_iUnion.mp hq
    exact (terminal_labeled_model_lower_boundary data Φ χ H hH hχ hplanar hlabels
      (data.labels.symm (.inl j)) j (data.labels.apply_symm_apply _)).2 x hx

theorem exists_terminal_lower_prepared_model_slice_coverage
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
    (C : data.ends.LowerCutIndex → OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : ∀ j, (C j).source = univ ×ˢ Ioo (-r) r)
    (hcyl : ∀ j q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
        (data.ends.lowerCut + z) • (M.v : E3) +
          ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3))
    (hCrim : ∀ j, range (fun q : S1 => C j (q, 0)) =
      data.modelDisk (data.labels.symm (.inl j)) '' sphere (0 : E2) 1) :
    ∃ δ : Real, 0 < δ ∧ δ < r ∧ ∀ z ∈ Icc (-δ) δ,
      (fun q : S2 => Q (data.toTerminalSaddleGeometry.filledModel q)) ''
        {q : S2 | inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) =
          data.ends.lowerCut + z} =
      ⋃ j, range (fun q : S1 => (data.ends.lowerCut + z) • (M.v : E3) +
        ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) := by
  let m : S2 → E3 := fun q => data.toTerminalSaddleGeometry.filledModel q
  let h : S2 → Real := fun q => inner Real (M.v : E3) (m q)
  have hh : Continuous h := continuous_const.inner
    (data.toTerminalSaddleGeometry.filledModel.contMDiff.continuous.comp continuous_subtype_val)
  have hCh (j) (q : S1) (z : Real) (hz : z ∈ Ioo (-r) r) :
      h (C j (q, z)) = data.ends.lowerCut + z := by
    have ht := congrArg Prod.fst ((heightCoordinates (norm_eq_of_mem_sphere M.v)).symm_apply_apply
      (data.ends.lowerCut + z, (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
        (m (C j (q, 0)))))
    change inner Real (M.v : E3) ((data.ends.lowerCut + z) • (M.v : E3) +
      ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto (m (C j (q, 0))) : E3)) = _ at ht
    change inner Real (M.v : E3) (m (C j (q, z))) = _
    rw [← hQ, hcyl j q z hz]
    exact ht
  have hcover : {q | h q = data.ends.lowerCut} ⊆ ⋃ j, range (fun q : S1 => C j (q, 0)) := by
    change {q : S2 | inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) = _} ⊆ _
    rw [terminal_model_lower_level_eq_rims data Φ χ H hH hχ hplanar hlabels]
    exact iUnion_mono (fun j => (hCrim j).ge)
  obtain ⟨δ, hδ, hδr, hlevels⟩ := exists_annular_family_full_slice_coverage hh hr C hCs hCh hcover
  refine ⟨δ, hδ, hδr, ?_⟩
  intro z hz
  change (fun q => Q (m q)) '' {q | h q = data.ends.lowerCut + z} = _
  rw [hlevels z hz, image_iUnion]
  apply iUnion_congr
  intro j
  rw [← range_comp]
  apply congrArg range
  funext q
  exact hcyl j q z ⟨by linarith [hz.1], by linarith [hz.2]⟩

theorem exists_terminal_lower_prepared_modelBand_coverage
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
    (C : data.ends.LowerCutIndex → OpenPartialHomeomorph (S1 × Real) S2)
    (hCs : ∀ j, (C j).source = univ ×ˢ Ioo (-r) r)
    (hcyl : ∀ j q z, z ∈ Ioo (-r) r →
      Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
        (data.ends.lowerCut + z) • (M.v : E3) +
          ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3))
    (hCrim : ∀ j, range (fun q : S1 => C j (q, 0)) =
      data.modelDisk (data.labels.symm (.inl j)) '' sphere (0 : E2) 1) :
    ∃ δ : Real, 0 < δ ∧ δ < r ∧ δ < data.ends.upperCut - data.ends.lowerCut ∧
      ∀ z ∈ Icc 0 δ,
        (Q '' (data.toTerminalSaddleGeometry.flatten.symm ''
          data.toTerminalSaddleGeometry.modelBand)) ∩
            {y | inner Real (M.v : E3) y = data.ends.lowerCut + z} =
        ⋃ j, range (fun q : S1 => (data.ends.lowerCut + z) • (M.v : E3) +
          ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
            (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) := by
  obtain ⟨ε, hε, hεr, hlevels⟩ :=
    exists_terminal_lower_prepared_model_slice_coverage data Φ χ H hH hχ hplanar hlabels
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
    change inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) = _
    rw [heq, ← hQ]
    exact hy
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨data.toTerminalSaddleGeometry.filledModel q, ?_, rfl⟩, ?_⟩
    · refine ⟨data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel q), ?_, Diffeomorph.symm_apply_apply _ _⟩
      apply (terminal_physical_modelBand_mem_iff data _).mpr
      refine ⟨mem_image_of_mem _ q.property, ?_⟩
      change data.ends.lowerCut ≤ _ ∧ _ ≤ data.ends.upperCut
      rw [hq]
      constructor <;> linarith [hz.1, hz.2]
    · change inner Real (M.v : E3) (Q (data.toTerminalSaddleGeometry.filledModel q)) = _
      rw [hQ]
      exact hq

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
