import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_CollarImage
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff















noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_exists_open_embedded_normal_strip (N : IntrinsicAnnulus) :
    ∃ (normal : ℝ → AnnulusCoordinates)
      (u : ℝ × ℝ → AnnulusCoordinates) (r : ℝ)
      (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates),
      0 < r ∧ r ≤ 1 ∧ ContDiff ℝ ∞ normal ∧ ContDiff ℝ ∞ u ∧
      (∀ a, N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
          (normal a) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary 1 a) (normal a)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) a) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary 1 a) (normal a)) ∧
      (∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a) ∧
      (∀ a, HasDerivAt (fun t => u (a, t)) (normal a) 0) ∧
      (∀ a ∈ Icc (0 : ℝ) rampPeriod, ∀ t ∈ Icc (0 : ℝ) r,
        Function.Injective (fderiv ℝ u (a, t)) ∧
        u (a, t) ∈ standardAnnulusDomain) ∧
      (∀ a ∈ Icc (0 : ℝ) rampPeriod,
        N.metric.IsGeodesicOn (fun t => u (a, t)) (Icc (0 : ℝ) r)) ∧
      (Ioo (0 : ℝ) rampPeriod ×ˢ Ioo (0 : ℝ) r) ⊆ F.source ∧
      (∀ z, F z = u z) ∧
      ContDiffOn ℝ ∞ F F.source ∧
      ContDiffOn ℝ ∞ F.symm F.target ∧
      (∀ z ∈ Ioo (0 : ℝ) rampPeriod ×ˢ Ioo (0 : ℝ) r,
        Function.Injective (fderiv ℝ u z) ∧ u z ∈ standardAnnulusDomain) := by
  obtain ⟨normal, u, r, hr, hrone, hnormal_smooth, hu, hnormal,
      hboundary, hvelocity, hinj, hregular, hgeo⟩ :=
    m64Intrinsic_exists_embedded_normal_collar N
  let e : ℝ × ℝ → AnnulusCoordinates := u
  have he : ContDiff ℝ ∞ e := by simpa [e] using hu
  let U : Set (ℝ × ℝ) := Ioo (0 : ℝ) rampPeriod ×ˢ Ioo (0 : ℝ) r
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  have hUsub : U ⊆ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) r := by
    intro z hz
    exact ⟨⟨le_of_lt hz.1.1, hz.1.2⟩,
      ⟨le_of_lt hz.2.1, hz.2.2.le⟩⟩
  have heinj : InjOn e U := by
    intro z hz w hw hzw
    exact hinj (hUsub hz) (hUsub hw) (by simpa [e] using hzw)
  have hderiv (z : ℝ × ℝ) (hz : z ∈ U) :
      ∃ L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates,
        HasStrictFDerivAt e (L : (ℝ × ℝ) →L[ℝ] AnnulusCoordinates) z := by
    rcases z with ⟨a, t⟩
    have ha : a ∈ Icc (0 : ℝ) rampPeriod :=
      ⟨le_of_lt hz.1.1, hz.1.2.le⟩
    have ht : t ∈ Icc (0 : ℝ) r :=
      ⟨le_of_lt hz.2.1, hz.2.2.le⟩
    have hi : Function.Injective (fderiv ℝ e (a, t)) := by
      simpa [e] using (hregular a ha t ht).1
    have hdim : Module.finrank ℝ (ℝ × ℝ) =
        Module.finrank ℝ AnnulusCoordinates := by simp
    have hs :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
    let A : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates :=
      (LinearEquiv.ofBijective (fderiv ℝ e (a, t)).toLinearMap
        ⟨hi, hs⟩).toContinuousLinearEquiv
    have hA : A.toContinuousLinearMap = fderiv ℝ e (a, t) := rfl
    refine ⟨A, ?_⟩
    rw [hA]
    exact he.contDiffAt.hasStrictFDerivAt (x := (a, t)) (by simp)
  have hopen : IsOpenMap (U.domRestrict e) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro z
    obtain ⟨L, hL⟩ := hderiv z z.property
    change 𝓝 (e z) ≤ Filter.map (e ∘ Subtype.val) (𝓝 z)
    rw [← Filter.map_map, hU.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hL.map_nhds_eq_of_equiv]
  let F := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (heinj.toPartialEquiv e U) he.continuous.continuousOn hopen hU
  have hFsource : U ⊆ F.source := by
    intro z hz
    exact hz
  have hF : ∀ z, F z = u z := by
    intro z
    rfl
  have hFdiff : ContDiffOn ℝ ∞ F F.source := by
    change ContDiffOn ℝ ∞ e F.source
    exact he.contDiffOn
  have hFinvdiff : ContDiffOn ℝ ∞ F.symm F.target := by
    intro y hy
    obtain ⟨L, hL⟩ := hderiv (F.symm y) (F.map_target hy)
    exact (F.contDiffAt_symm hy hL.hasFDerivAt he.contDiffAt).contDiffWithinAt
  refine ⟨normal, u, r, F, hr, hrone, ?_, ?_, hnormal, hboundary,
    hvelocity, ?_, hgeo, ?_, hF, hFdiff, hFinvdiff, ?_⟩
  · exact hnormal_smooth
  · exact hu
  · intro a ha t ht
    exact ⟨(hregular a ha t ht).1, (hregular a ha t ht).2.1⟩
  · exact hFsource
  · intro z hz
    exact ⟨by
      simpa [e] using (hregular z.1 ⟨le_of_lt hz.1.1, hz.1.2.le⟩ z.2
        ⟨le_of_lt hz.2.1, hz.2.2.le⟩).1,
      by
      simpa [e] using (hregular z.1 ⟨le_of_lt hz.1.1, hz.1.2.le⟩ z.2
        ⟨le_of_lt hz.2.1, hz.2.2.le⟩).2.1⟩

end PoincareConjecture
