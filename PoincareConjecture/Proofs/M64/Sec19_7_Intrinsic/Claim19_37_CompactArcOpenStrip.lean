import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_CollarImage
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalLocalChart
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Infimum
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_open_normal_strip_on_compact_arc
    (N : IntrinsicAnnulus) {a b : ℝ} (ha : 0 < a)
    (_hab : a ≤ b) (hb : b < rampPeriod) :
    ∃ (normal : ℝ → AnnulusCoordinates)
      (u : ℝ × ℝ → AnnulusCoordinates) (r : ℝ)
      (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates),
      0 < r ∧ r ≤ 1 ∧ ContDiff ℝ ∞ normal ∧ ContDiff ℝ ∞ u ∧
      (∀ s, N.metric.inner (intrinsicAnnulusBoundary 1 s) (normal s)
          (normal s) = 1 ∧
        N.metric.inner (intrinsicAnnulusBoundary 1 s) (normal s)
          (curveVelocity (n := 2) (intrinsicAnnulusBoundary 1) s) = 0 ∧
        0 < inner ℝ (intrinsicAnnulusBoundary 1 s) (normal s)) ∧
      (∀ s, u (s, 0) = intrinsicAnnulusBoundary 1 s) ∧
      (∀ s, HasDerivAt (fun t => u (s, t)) (normal s) 0) ∧
      (∀ x ∈ Icc a b, ∀ t ∈ Icc (0 : ℝ) r,
        Function.Injective (fderiv ℝ u (x, t)) ∧
        u (x, t) ∈ standardAnnulusDomain) ∧
      {z : AnnulusCoordinates | z 0 ∈ Icc a b ∧ z 1 ∈ Icc (0 : ℝ) r} ⊆
        F.source ∧
      (∀ z, F z = u (z 0, z 1)) ∧
      ContDiffOn ℝ ∞ F F.source ∧
      ContDiffOn ℝ ∞ F.symm F.target := by
  obtain ⟨normal, u, r, hr, hrone, hnormal, hu, hframe, hboundary,
      hvelocity, hinj, hregular, hgeo⟩ :=
    m64Intrinsic_exists_embedded_normal_collar N
  let e : AnnulusCoordinates → AnnulusCoordinates :=
    fun z => u (z 0, z 1)
  have he : ContDiff ℝ ∞ e := hu.comp (by fun_prop)
  let K : Set AnnulusCoordinates :=
    {z | z 0 ∈ Icc a b ∧ z 1 ∈ Icc (0 : ℝ) r}
  have hc0 : Continuous (fun z : AnnulusCoordinates => z 0) := by fun_prop
  have hc1 : Continuous (fun z : AnnulusCoordinates => z 1) := by fun_prop
  have hKclosed : IsClosed K := by
    exact (isClosed_Icc.preimage hc0).inter (isClosed_Icc.preimage hc1)
  have hKsub : K ⊆ m64AnnulusDomain := by
    intro z hz
    change 0 ≤ z 0 ∧ z 0 ≤ rampPeriod ∧ 0 ≤ z 1 ∧ z 1 ≤ 1
    exact ⟨le_trans (le_of_lt ha) hz.1.1, hz.1.2.trans (le_of_lt hb),
      hz.2.1, hz.2.2.trans hrone⟩
  have hK : IsCompact K :=
    IsCompact.of_isClosed_subset m64AnnulusDomain_isCompact hKclosed hKsub
  have heinj : InjOn e K := by
    intro z hz w hw hzw
    have hz0 : z 0 ∈ Ico (0 : ℝ) rampPeriod :=
      ⟨(le_of_lt ha).trans hz.1.1, hz.1.2.trans_lt hb⟩
    have hw0 : w 0 ∈ Ico (0 : ℝ) rampPeriod :=
      ⟨(le_of_lt ha).trans hw.1.1, hw.1.2.trans_lt hb⟩
    have h := hinj ⟨hz0, hz.2⟩ ⟨hw0, hw.2⟩ (by simpa [e] using hzw)
    ext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hlocal : ∀ z ∈ K, ∃ W ∈ 𝓝 z, InjOn e W := by
    intro z hz
    have hfd := (hregular (z 0)
      (show z 0 ∈ Icc (0 : ℝ) rampPeriod from
        ⟨(le_of_lt ha).trans hz.1.1, hz.1.2.trans hb.le⟩)
      (z 1) hz.2).1
    obtain ⟨Fz, hzF, hFz, _, _⟩ :=
      m64Intrinsic_exists_normal_local_chart hu hfd
    have hzcoord : !₂[z 0, z 1] = z := by
      ext i
      fin_cases i <;> rfl
    refine ⟨Fz.source, Fz.open_source.mem_nhds (by simpa [hzcoord] using hzF), ?_⟩
    intro p hp q hq hpq
    apply Fz.injOn hp hq
    simpa only [hFz] using hpq
  obtain ⟨W₀, hW₀, hKW₀, hWinj₀⟩ :=
    heinj.exists_isOpen_superset hK
      (fun z _ => he.continuous.continuousAt) hlocal
  let R : Set AnnulusCoordinates :=
    {z | ∃ L : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates,
      L.toContinuousLinearMap = fderiv ℝ e z}
  have hRopen : IsOpen R := by
    apply ContinuousLinearEquiv.isOpen.preimage
      (he.continuous_fderiv (by simp))
  have hKR : K ⊆ R := by
    intro z hz
    obtain ⟨hL, _, _⟩ := hregular (z 0)
      (show z 0 ∈ Icc (0 : ℝ) rampPeriod from
        ⟨(le_of_lt ha).trans hz.1.1, hz.1.2.trans hb.le⟩)
      (z 1) hz.2
    have hfd : Function.Injective (fderiv ℝ e z) := by
      intro v w hvw
      have hdu := hu.differentiable (by simp) (z 0, z 1)
      have hv := m64Intrinsic_normal_coordinate_differential hdu v
      have hw := m64Intrinsic_normal_coordinate_differential hdu w
      have hzcoord : !₂[z 0, z 1] = z := by
        ext i
        fin_cases i <;> rfl
      rw [hzcoord] at hv hw
      have hvw' : fderiv ℝ (fun z => u (z 0, z 1)) z v =
          fderiv ℝ (fun z => u (z 0, z 1)) z w := by
        simpa [e] using hvw
      rw [hv, hw] at hvw'
      have hcoords := hL hvw'
      ext i
      fin_cases i
      · exact congrArg Prod.fst hcoords
      · exact congrArg Prod.snd hcoords
    let A : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates :=
      (LinearEquiv.ofBijective (fderiv ℝ e z).toLinearMap
        ⟨hfd, (LinearMap.injective_iff_surjective
          (f := (fderiv ℝ e z).toLinearMap)).mp hfd⟩).toContinuousLinearEquiv
    exact ⟨A, rfl⟩
  let W := W₀ ∩ R
  have hW : IsOpen W := hW₀.inter hRopen
  have hKW : K ⊆ W := fun z hz => ⟨hKW₀ hz, hKR hz⟩
  have hWinj : InjOn e W := hWinj₀.mono inter_subset_left
  have hderiv (z : AnnulusCoordinates) (hz : z ∈ W) :
      ∃ L : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates,
        HasStrictFDerivAt e (L : AnnulusCoordinates →L[ℝ] AnnulusCoordinates) z := by
    obtain ⟨L, hL⟩ := hz.2
    refine ⟨L, ?_⟩
    rw [hL]
    simpa [hL] using he.contDiffAt.hasStrictFDerivAt (x := z) (by simp)
  have hopen : IsOpenMap (W.domRestrict e) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro z
    obtain ⟨L, hL⟩ := hderiv z z.property
    change 𝓝 (e z) ≤ Filter.map (e ∘ Subtype.val) (𝓝 z)
    rw [← Filter.map_map, hW.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hL.map_nhds_eq_of_equiv]
  let F := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hWinj.toPartialEquiv e W) he.continuous.continuousOn hopen hW
  refine ⟨normal, u, r, F, hr, hrone, hnormal, hu, hframe, hboundary,
    hvelocity, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx t ht
    exact ⟨(hregular x
        ⟨(le_of_lt ha).trans hx.1, hx.2.trans hb.le⟩ t ht).1,
      (hregular x ⟨(le_of_lt ha).trans hx.1, hx.2.trans hb.le⟩ t ht).2.1⟩
  · exact hKW
  · intro z
    rfl
  · exact he.contDiffOn
  · intro y hy
    obtain ⟨L, hL⟩ := hderiv (F.symm y) (F.map_target hy)
    exact (F.contDiffAt_symm hy hL.hasFDerivAt he.contDiffAt).contDiffWithinAt

end PoincareConjecture
