import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryFrame

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace

theorem halfDiskGradient_restrict {n : ℕ} {H : ℂ → EuclideanSpace ℝ (Fin n)}
    {R d : ℝ} (hd : 0 < d) (hdR : d ≤ R)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) :
    halfDiskGradient H d z = halfDiskGradient H R z := by
  have hsub := inter_subset_inter (closedBall_subset_closedBall (x := (0 : ℂ)) hdR)
    (Subset.rfl (s := {z : ℂ | 0 ≤ z.im}))
  have hder := fderivWithin_subset hsub ((halfDisk_differential_domain hd).2.2.1 _ hz)
    ((hH _ (hsub hz)).differentiableWithinAt one_ne_zero)
  simp only [halfDiskGradient, hder]

theorem halfDisk_normalized_actual_frame {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {R d : ℝ} (hd : 0 < d) (hdR : d < R)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    (hconf : ∀ z ∈ closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T I) (T I) ∧
        g.inner (H z) (T 1) (T I) = 0)
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im},
      fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im}) z ≠ 0)
    (hgi : ContDiffOn ℝ 1 (complexGradient H) (ball (0 : ℂ) d ∩ {z | 0 < z.im}))
    (hg1 : MemLp (fun z => fderiv ℝ (complexGradient H) z 1)
      2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})))
    (hgI : MemLp (fun z => fderiv ℝ (complexGradient H) z I)
      2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})))
    {C : ℝ} (hC : 0 ≤ C)
    (hholder : ∀ z ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
      ∀ w ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
        ‖halfDiskGradient H R z - halfDiskGradient H R w‖ ≤ C * Real.sqrt ‖z - w‖) :
    let K := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
    let W := ball (0 : ℂ) d ∩ {z | 0 < z.im}
    let F := fun z => normalizedResidualFrame (g.euclideanCoefficients (H z))
      (halfDiskGradient H R z)
    ContinuousOn F K ∧ ContDiffOn ℝ 1 F W ∧
      (∀ z ∈ K, g.inner (H z) (F z).1 (F z).1 = 1 ∧
        g.inner (H z) (F z).1 (F z).2 = 0 ∧ g.inner (H z) (F z).2 (F z).2 = 1) ∧
      MemLp (fun z => fderiv ℝ F z 1) 2 (volume.restrict W) ∧
      MemLp (fun z => fderiv ℝ F z I) 2 (volume.restrict W) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ w ∈ K,
        ‖F z - F w‖ ≤ B * Real.sqrt ‖z - w‖ := by
  let KR := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  let K := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
  let W := ball (0 : ℂ) d ∩ {z | 0 < z.im}
  let Q := halfDiskGradient H R
  have hsub : K ⊆ KR := inter_subset_inter (closedBall_subset_closedBall hdR.le) Subset.rfl
  have hW : IsOpen W := (halfDisk_differential_domain hd).1
  have hUD : UniqueDiffOn ℝ K := (halfDisk_differential_domain hd).2.2.1
  have hder (z : ℂ) (hz : z ∈ K) : fderivWithin ℝ H K z = fderivWithin ℝ H KR z :=
    fderivWithin_subset hsub (hUD z hz) ((hH z (hsub hz)).differentiableWithinAt one_ne_zero)
  have hfactor (z : ℂ) (hz : z ∈ K) : halfDiskGradient H d z = z ^ (0 : ℕ) • Q z := by
    simpa only [pow_zero, one_smul] using halfDiskGradient_restrict hd hdR.le hH hz
  have hQeq (z : ℂ) (hz : z ∈ W) : Q z = complexGradient H z :=
    (halfDisk_fields_eq D H ⟨ball_subset_ball hdR.le hz.1, hz.2⟩).1
  have hQder (z : ℂ) (hz : z ∈ W) : fderiv ℝ Q z = fderiv ℝ (complexGradient H) z := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hW.mem_nhds hz] with w hw
    exact hQeq w hw
  have hmem (v : ℂ)
      (hv : MemLp (fun z => fderiv ℝ (complexGradient H) z v) 2 (volume.restrict W)) :
      MemLp (fun z => fderiv ℝ Q z v) 2 (volume.restrict W) := by
    apply (memLp_congr_ae ?_).mp hv
    filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
    rw [hQder z hz]
  apply halfDisk_normalizedResidualFrame g hd 0 (hH.mono hsub)
    ((halfDisk_fields_continuousOn D (hd.trans hdR) hH).1.mono hsub)
    (hgi.congr hQeq) (fun z hz hq => hzero z (hsub hz)
      ((halfDiskGradient_eq_zero_iff H R z).mp hq)) hfactor
  · intro z hz
    dsimp only
    rw [hder z hz]
    exact hconf z (hsub hz)
  · exact hmem 1 hg1
  · exact hmem I hgI
  · exact hC
  · exact hholder

end PoincareConjecture.M64
