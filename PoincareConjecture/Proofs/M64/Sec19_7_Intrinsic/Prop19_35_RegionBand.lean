import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FittedRectangle
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.Polygonal















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_exists_loop_region_band
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates) (a b r : ℝ)
      (hab : a < b) (B : SmoothGraphBandPair F (fun _ => 0) (fun _ => r) hab)
      (W : Set AnnulusCoordinates),
      0 < r ∧ ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target ∧
      B.lower.carrier ∪ B.upper.carrier ⊆ closure U ∧
      (B.lower.boundary 2).map (1 / 2) = gamma p ∧ IsOpen W ∧ gamma p ∈ W ∧
      W ∩ closure U ⊆ B.lower.carrier ∪ B.upper.carrier := by
  obtain ⟨H, x, r, sigma, W, hr, hsigma, hbase, hH, hHi, hrect, hW, hpW, hcover⟩ :=
    m64Intrinsic_exists_fitted_loop_region_rectangle hg hend hinj hp hregular
      hU hV hdisj hfU hfV
  have hsquare : sigma * sigma = 1 := by rcases hsigma with rfl | rfl <;> norm_num
  have hE : ∃ E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ),
      ∀ q : ℝ × ℝ, E q = (q.1, sigma * q.2) := by
    rcases hsigma with rfl | rfl
    · exact ⟨ContinuousLinearEquiv.refl ℝ (ℝ × ℝ), fun _ => by simp⟩
    · refine ⟨(ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ), ?_⟩
      intro q
      simp
  obtain ⟨E, hE⟩ := hE
  let A := collarParameterEquiv.trans E
  let F := A.toHomeomorph.toOpenPartialHomeomorph.trans H
  have hFformula (z : AnnulusCoordinates) :
      F z = H ((collarParameterEquiv z).1, sigma * (collarParameterEquiv z).2) := by
    change H (E (collarParameterEquiv z)) = _
    rw [hE]
  have hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source := by
    apply contMDiffOn_iff_contDiffOn.mpr
    exact hH.comp A.contDiff.contDiffOn (fun _ hz => hz.2)
  have hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target := by
    apply contMDiffOn_iff_contDiffOn.mpr
    exact A.symm.contDiff.comp_contDiffOn (hHi.mono (fun _ hz => hz.1))
  have hab : x - r < x + r := by linarith
  have hband : coordinateGraphBand (fun _ => 0) (fun _ => r) (x - r) (x + r) ⊆ F.source := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    change E (collarParameterEquiv z) ∈ H.source
    rw [hE]
    exact (hrect _ hz.1 _ ⟨hz.2.1, hz.2.2⟩).1
  obtain ⟨B⟩ := exists_smoothGraphBandPair F hF hFi isOpen_univ
    (contDiffOn_const (c := (0 : ℝ))) (contDiffOn_const (c := r)) hab
      (fun _ _ => mem_univ _) (fun _ _ => hr) hband (0 : AnnulusCoordinates) (by
        intro z _
        simp)
  refine ⟨F, x - r, x + r, r, hab, B, W, hr, hF, hFi, ?_, ?_, hW, hpW, ?_⟩
  · rw [B.cover]
    rintro z ⟨q, hq, rfl⟩
    rw [hFformula]
    exact (hrect _ hq.1 _ ⟨hq.2.1, hq.2.2⟩).2.1
  · rw [B.lower_edge, hFformula, collarParameterEquiv.apply_symm_apply]
    dsimp only
    rw [mul_zero, show x - r + 1 / 2 * (x + r - (x - r)) = x by ring, hbase]
  · rw [B.cover]
    intro z hz
    obtain ⟨q, hq, heq⟩ := hcover hz
    refine ⟨collarParameterEquiv.symm (q.1, sigma * q.2), ?_, ?_⟩
    · change collarParameterEquiv (collarParameterEquiv.symm (q.1, sigma * q.2)) ∈
        {v : ℝ × ℝ | v.1 ∈ Icc (x - r) (x + r) ∧ 0 ≤ v.2 ∧ v.2 ≤ r}
      rw [collarParameterEquiv.apply_symm_apply]
      exact ⟨hq.1, hq.2.1, hq.2.2⟩
    · rw [hFformula, collarParameterEquiv.apply_symm_apply]
      dsimp only
      rw [← mul_assoc, hsquare, one_mul]
      exact heq

end PoincareConjecture
