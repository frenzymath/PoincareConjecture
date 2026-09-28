import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GraphObstacleWidth




noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture





theorem m64Intrinsic_exists_straight_chart_separator
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {t : ℝ}
    (ht : (t, (0 : ℝ)) ∈ F.source) (hF : ContDiffAt ℝ 1 F (t, 0))
    (ell : AnnulusCoordinates →L[ℝ] ℝ)
    (hpositive : 0 < ell (fderiv ℝ F (t, 0) (1, 0)))
    (hzero : ∀ᶠ z in 𝓝 (0 : ℝ), ell (F (t, z) - F (t, 0)) = 0) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ F (t, 0) ∈ W ∧ W ⊆ F.target ∧
      ∀ p ∈ W,
        (0 < ell (p - F (t, 0)) ↔ t < (F.symm p).1) ∧
        (ell (p - F (t, 0)) = 0 ↔ t = (F.symm p).1) ∧
        (0 ≤ ell (p - F (t, 0)) ↔ t ≤ (F.symm p).1) := by
  let H : ℝ × ℝ → ℝ × ℝ := fun q => (t + q.1, q.2)
  have hH : ContDiff ℝ ∞ H := (contDiff_const.add contDiff_fst).prodMk contDiff_snd
  have hH0 : H 0 = (t, 0) := by simp [H]
  let f : ℝ × ℝ → ℝ := fun q => ell (F (H q) - F (t, 0))
  have hf : ContDiffAt ℝ 1 f 0 := ell.contDiff.contDiffAt.comp 0
    (((hH0.symm ▸ hF).comp 0 (hH.of_le (by simp)).contDiffAt).sub contDiffAt_const)
  have hdH : HasFDerivAt H (ContinuousLinearMap.id ℝ (ℝ × ℝ)) 0 := by
    have hd1 : HasFDerivAt (fun q : ℝ × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) 0 := hasFDerivAt_fst
    have hd2 : HasFDerivAt (fun q : ℝ × ℝ => q.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) 0 := hasFDerivAt_snd
    convert! ((hasFDerivAt_const t (0 : ℝ × ℝ)).add hd1).prodMk hd2 using 1
    ext <;> simp
  have hdF : HasFDerivAt F (fderiv ℝ F (t, 0)) (H 0) :=
    hH0.symm ▸ hF.differentiableAt_one.hasFDerivAt
  have hdf := ell.hasFDerivAt.comp 0 ((hdF.comp 0 hdH).sub_const (F (t, 0)))
  change HasFDerivAt f
    (ell.comp ((fderiv ℝ F (t, 0)).comp (ContinuousLinearMap.id ℝ (ℝ × ℝ)))) 0 at hdf
  have hpos : 0 < fderiv ℝ f 0 (1, 0) := by
    rw [hdf.fderiv]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hpositive
  have hz : ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), q.1 = 0 → f q = 0 := by
    filter_upwards [continuousAt_snd.tendsto.eventually hzero] with q hq hq0
    simpa only [f, H, hq0, add_zero] using hq
  obtain ⟨delta, hdelta, hsign⟩ := Poincare.Analysis.exists_first_coordinate_sign_radius hf hpos hz
  let D : Set (ℝ × ℝ) := {q | |q.1 - t| < delta ∧ |q.2| < delta}
  have hD : IsOpen D := by
    change IsOpen ({q : ℝ × ℝ | |q.1 - t| < delta} ∩ {q | |q.2| < delta})
    exact (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt (by fun_prop) continuous_const)
  let W := F '' (F.source ∩ D)
  have hW : IsOpen W := F.isOpen_image_of_subset_source (F.open_source.inter hD) inter_subset_left
  have htD : (t, (0 : ℝ)) ∈ D := by simp [D, hdelta]
  refine ⟨W, hW, ⟨(t, 0), ⟨ht, htD⟩, rfl⟩, ?_, ?_⟩
  · rintro p ⟨q, hq, rfl⟩
    exact F.map_source hq.1
  · rintro p ⟨q, hq, rfl⟩
    rw [F.left_inv hq.1]
    have hs := hsign (q.1 - t) q.2 hq.2.1 hq.2.2
    have he : H (q.1 - t, q.2) = q := by dsimp only [H]; congr 1; ring
    simpa only [f, he, sub_pos, sub_eq_zero, eq_comm, sub_nonneg] using hs

end PoincareConjecture
