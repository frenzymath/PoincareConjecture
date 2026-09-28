import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace

theorem halfDisk_immersed_gradient_regular
    {n : ℕ} [Nonempty (Fin n)]
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (J : (Fin n → ℂ) ≃ₗᵢ[ℝ] (Fin n → ℂ))
    (hJ : ∀ (s : ℂ) v, J (s • v) = star s • J v) (hJJ : Function.Involutive J)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    {L : EuclideanSpace ℝ (Fin n) → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    (hL : ContDiffOn ℝ ∞ L V)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hHV : MapsTo H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) V)
    (hunit : ∀ z ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}, IsUnit (L (H z)))
    (heq : ∀ z ∈ ball (0 : ℂ) r ∩ {z | 0 < z.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z))
    (hreal : ∀ z ∈ closedBall (0 : ℂ) r, z.im = 0 →
      J (halfDiskFramedGradient H L r z) = halfDiskFramedGradient H L r z)
    (hzero : fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) 0 ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ d < r ∧
      ContDiffOn ℝ 1 (complexGradient H) (ball (0 : ℂ) d ∩ {z | 0 < z.im}) ∧
      MemLp (fun z => fderiv ℝ (complexGradient H) z 1)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      MemLp (fun z => fderiv ℝ (complexGradient H) z Complex.I)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
        ∀ w ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
          ‖halfDiskGradient H r z - halfDiskGradient H r w‖ ≤ C * Real.sqrt ‖z - w‖ := by
  have hUK : (ball (0 : ℂ) r ∩ {z | 0 < z.im}) ⊆
      (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) :=
    fun z hz => ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩
  obtain ⟨-, hAc⟩ := halfDiskFramed_fields_continuousOn D hr hV hL hH hHV hunit
  obtain ⟨-, hAi, hFeq⟩ := halfDiskFramed_fields_equation D hV hL hHi
    (hHV.mono hUK Subset.rfl) (fun z hz => hunit z (hUK hz)) heq
  have hnot : ¬∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0,
      fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) z = 0 := by
    intro h
    exact hzero (h.self_of_nhdsWithin (by simp))
  obtain ⟨d, m, q, hd, hdr, -, hqi, -, hfactor, hq1, hqI, C, hC, hholder⟩ :=
    halfDisk_differential_factor_holder J hJ hJJ hr hH hHi
      ((hL.of_le (by simp)).comp hH hHV) hunit hAc hAi
      (fun z hz hi => hFeq z ⟨hz, hi⟩) hreal hnot
  have hm : m = 0 := by
    by_contra hm
    have hf0 := hfactor 0 (by simp [hd.le])
    have hz : halfDiskGradient H r 0 = 0 := by
      simpa only [zero_pow hm, zero_smul] using hf0
    exact hzero ((halfDiskGradient_eq_zero_iff H r 0).mp hz)
  have hgrad (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) :
      halfDiskGradient H r z = q z := by simpa only [hm, pow_zero, one_smul] using hfactor z hz
  let U := ball (0 : ℂ) d ∩ {z | 0 < z.im}
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have he (z : ℂ) (hz : z ∈ U) : complexGradient H z = q z :=
    ((halfDisk_fields_eq D H ⟨ball_subset_ball hdr.le hz.1, hz.2⟩).1.symm).trans
      (hgrad z ⟨ball_subset_closedBall hz.1, (show 0 < z.im from hz.2).le⟩)
  have hder (z : ℂ) (hz : z ∈ U) : fderiv ℝ (complexGradient H) z = fderiv ℝ q z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hU.mem_nhds hz] with w hw
    exact he w hw
  have hmem (v : ℂ) (hv : MemLp (fun z => fderiv ℝ q z v) 2 (volume.restrict U)) :
      MemLp (fun z => fderiv ℝ (complexGradient H) z v) 2 (volume.restrict U) := by
    apply (memLp_congr_ae ?_).mp hv
    filter_upwards [ae_restrict_mem hU.measurableSet] with z hz
    rw [hder z hz]
  refine ⟨d, hd, hdr, hqi.congr he, hmem 1 hq1, hmem Complex.I hqI, C, hC, ?_⟩
  intro z hz w hw
  rw [hgrad z hz, hgrad w hw]
  exact hholder z hz w hw

end PoincareConjecture.M64
