import PoincareConjecture.Proofs.M64.Mathlib.RadialDigonFirstExit
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactInverseRadius





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture






theorem m64Intrinsic_exists_earlier_radial_digon_contact
    (N : IntrinsicAnnulus)
    {e : AnnulusCoordinates → AnnulusCoordinates}
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (hFe : EqOn F e F.source) (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {v theta : AnnulusCoordinates} {R s T : ℝ} (hs : 0 < s) (hT : 0 < T) (hR : ‖v‖ ≤ R)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ F.source)
    (he0 : DifferentiableAt ℝ e 0) (hev : DifferentiableAt ℝ e v)
    {beta : ℝ → AnnulusCoordinates} (hb : ContDiff ℝ ∞ beta)
    (hi : InjOn beta (Icc 0 s)) (hbase : beta 0 = e 0) (hend : beta s = e v)
    {U : Set AnnulusCoordinates}
    (hfront : frontier U = (fun t : ℝ => e (t • v)) '' Icc 0 1 ∪ beta '' Icc 0 s)
    {phi0 phi1 : AnnulusCoordinates → ℝ × ℝ}
    (L0 L1 : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi0 : HasFDerivAt phi0 L0.toContinuousLinearMap (e 0)) (hzero0 : phi0 (e 0) = 0)
    (hcorner0 : ∀ᶠ z in 𝓝 (e 0), z ∈ closure U ↔ 0 ≤ (phi0 z).1 ∧ 0 ≤ (phi0 z).2)
    (hinitv : L0 (fderiv ℝ e 0 v) = (T, 0))
    (hinittheta : L0 (fderiv ℝ e 0 theta) = (0, 1))
    (hphi1 : HasFDerivAt phi1 L1.toContinuousLinearMap (e v)) (hzero1 : phi1 (e v) = 0)
    (hcorner1 : ∀ᶠ z in 𝓝 (e v), z ∈ closure U → 0 ≤ (phi1 z).1)
    (hterminal : (L1 (fderiv ℝ e v v)).1 < 0)
    (hgauss : ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e v v w = inner ℝ v w)
    (hangle : N.metric.cornerAngle (e v) (fderiv ℝ e v v) (deriv beta s) < Real.pi / 2) :
    ∃ b ∈ Ioo 0 s, ∃ z : AnnulusCoordinates,
      ‖z‖ ≤ R ∧ (∀ t ∈ Icc (0 : ℝ) 1, e (t • z) ∈ closure U) ∧
        e z = beta b ∧ z ≠ b • theta := by
  have h0F : (0 : AnnulusCoordinates) ∈ F.source := by
    simpa only [zero_smul] using hsegment 0 ⟨le_rfl, zero_le_one⟩
  have hvF : v ∈ F.source := by
    simpa only [one_smul] using hsegment 1 ⟨zero_le_one, le_rfl⟩
  let phi := phi0 ∘ e
  let J := L0.toContinuousLinearMap.comp (fderiv ℝ e 0)
  have hd : HasFDerivAt phi J 0 := hphi0.comp 0 he0.hasFDerivAt
  have hzero : phi 0 = 0 := hzero0
  have hcorner : ∀ᶠ z in 𝓝 (0 : AnnulusCoordinates),
      0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2 → F z ∈ closure U := by
    filter_upwards [he0.continuousAt.eventually hcorner0,
      F.open_source.mem_nhds h0F] with z hz hzs
    intro hpos
    rw [hFe hzs]
    exact hz.mpr hpos
  let f : AnnulusCoordinates → ℝ := fun z => (phi1 (e z)).1
  let D := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (L1.toContinuousLinearMap.comp (fderiv ℝ e v))
  have hdf : HasFDerivAt f D v :=
    hasFDerivAt_fst.comp v (hphi1.comp v hev.hasFDerivAt)
  have hfzero : f v = 0 := by simp only [f, hzero1, Prod.fst_zero]
  have hcorner' : ∀ᶠ z in 𝓝 v, F z ∈ closure U → 0 ≤ f z := by
    filter_upwards [hev.continuousAt.eventually hcorner1,
      F.open_source.mem_nhds hvF] with z hz hzs
    intro hmem
    exact hz (by simpa only [hFe hzs] using hmem)
  have hescape := m64_radial_leaves_terminal_corner hdf hfzero hterminal hcorner'
  have hshort := m64Intrinsic_compact_inverse_radius_decreases_left N F hFe hFi
    hvF hev hb.contDiffAt hend hgauss hangle
  have hside : (fun t : ℝ => F (t • v)) '' Icc 0 1 =
      (fun t : ℝ => e (t • v)) '' Icc 0 1 := by
    apply image_congr
    exact fun t ht => hFe (hsegment t ht)
  have hfront' : frontier U = (fun t : ℝ => F (t • v)) '' Icc 0 1 ∪ beta '' Icc 0 s := by
    rw [hside]
    exact hfront
  have hJv : J v = (T, 0) := hinitv
  have hJtheta : J theta = (0, 1) := hinittheta
  obtain ⟨b, hbI, z, hzF, hzR, hzconf, hzpoint, hzne⟩ :=
    m64_exists_earlier_radial_digon_contact F (theta := theta) hs hR hsegment
      hb.continuous.continuousOn hi
      (hbase.trans (hFe h0F).symm) (hend.trans (hFe hvF).symm) hfront' hd hzero hcorner
      (by simpa only [hJv] using hT) (by simp only [hJv])
      (by simp only [hJtheta]) (by simp only [hJtheta, zero_lt_one]) hescape hshort
  refine ⟨b, hbI, z, hzR, ?_, (hFe hzF).symm.trans hzpoint, hzne⟩
  intro t ht
  have h := hzconf t ht
  simpa only [hFe h.1] using h.2

end PoincareConjecture
