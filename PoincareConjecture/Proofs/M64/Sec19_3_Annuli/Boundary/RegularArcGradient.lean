import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.HalfDiskLabelRegularity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.SmoothTangentExtension

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem halfDisk_regular_arc_gradient
    {g : RiemannianMetric n E} (D : LeviCivitaData g)
    {H : ℂ → E} {r : ℝ} (hr : 0 < r)
    {c : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hc : ContDiffOn ℝ ∞ c I)
    {sigma : ℝ → ℝ} (hsigma : ContDiff ℝ 1 sigma)
    (hs0 : sigma 0 ∈ I) (hc0 : deriv c (sigma 0) ≠ 0)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hboundary : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ r → H (s : ℂ) = c (sigma s))
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T Complex.I) (T Complex.I) ∧
        g.inner (H z) (T 1) (T Complex.I) = 0)
    (heq : ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z))
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
  obtain ⟨j, U, J, psi, V, hU, hJ, hcsU, hsJ, hJI, -, -, hV, hinv, hVeq⟩ :=
    exists_smooth_tangent_extension hI hs0 hc hc0
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  have h0 : (0 : ℂ) ∈ K := by simp [K, hr.le]
  have hH0 : H 0 = c (sigma 0) := by simpa using hboundary 0 (by simp [hr.le])
  have hHU : ∀ᶠ z in 𝓝[K] (0 : ℂ), H z ∈ U :=
    (hH.continuousOn 0 h0).eventually (hU.mem_nhds (hH0.symm ▸ hcsU))
  have hsigJ : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), sigma z.re ∈ J :=
    (hsigma.continuous.comp continuous_re).continuousAt.eventually
      (by simpa using hJ.mem_nhds hsJ)
  obtain ⟨e, he, hesub⟩ := (nhdsWithin_hasBasis nhds_basis_closedBall K).mem_iff.mp
    (hHU.and (mem_nhdsWithin_of_mem_nhds hsigJ))
  let R := min r e / 2
  have hR : 0 < R := half_pos (lt_min hr he)
  have hRr : R < r := by dsimp only [R]; linarith [min_le_left r e]
  have hRe : R ≤ e := by dsimp only [R]; linarith [min_le_right r e]
  let KR := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  have hKR : KR ⊆ K := inter_subset_inter (closedBall_subset_closedBall hRr.le) Subset.rfl
  have hsmall (z : ℂ) (hz : z ∈ KR) : H z ∈ U ∧ sigma z.re ∈ J :=
    hesub ⟨closedBall_subset_closedBall hRe hz.1, hKR hz⟩
  have hdiam (s : ℝ) (hs : ‖(s : ℂ)‖ ≤ R) : (s : ℂ) ∈ KR := by
    exact ⟨mem_closedBall_zero_iff.mpr hs, by simp⟩
  have hsJ' (s : ℝ) (hs : ‖(s : ℂ)‖ ≤ R) : sigma s ∈ J := by
    simpa only [ofReal_re] using (hsmall (s : ℂ) (hdiam s hs)).2
  have hb (s : ℝ) (hs : ‖(s : ℂ)‖ ≤ R) : H (s : ℂ) = c (sigma s) :=
    hboundary s (hs.trans hRr.le)
  have hcurve (s : ℝ) (hs : ‖(s : ℂ)‖ ≤ R) : V (H (s : ℂ)) = deriv c (sigma s) := by
    rw [(hVeq _ (hsmall _ (hdiam s hs)).1).2.1, hb s hs, hinv _ (hsJ' s hs)]
  have hder (z : ℂ) (hz : z ∈ KR) : fderivWithin ℝ H KR z = fderivWithin ℝ H K z :=
    fderivWithin_subset hKR ((halfDisk_differential_domain hR).2.2.1 z hz)
      ((hH z (hKR hz)).differentiableWithinAt one_ne_zero)
  have hconfR (z : ℂ) (hz : z ∈ KR) :
      let T := fderivWithin ℝ H KR z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T Complex.I) (T Complex.I) ∧
        g.inner (H z) (T 1) (T Complex.I) = 0 := by
    dsimp only
    rw [hder z hz]
    exact hconf z (hKR hz)
  have hzeroR : fderivWithin ℝ H KR 0 ≠ 0 := by
    rw [hder 0 (by simp [KR, hR.le])]
    exact hzero
  have hWR : (ball (0 : ℂ) R ∩ {z | 0 < z.im}) ⊆
      (ball (0 : ℂ) r ∩ {z | 0 < z.im}) :=
    inter_subset_inter (ball_subset_ball hRr.le) Subset.rfl
  obtain ⟨d, hd, hdR, hqi, hq1, hqI, C, hC, hholder⟩ :=
    halfDisk_label_gradient_regular D hR hsigma
      (fun s hs => ((hc _ (hJI (hsJ' s hs))).contDiffAt
        (hI.mem_nhds (hJI (hsJ' s hs)))).differentiableAt (by simp))
      j hU hV (fun q hq => (hVeq q hq).2.2)
      (hH.mono hKR) (hHi.mono hWR) (fun z hz => (hsmall z hz).1)
      hb hcurve hconfR (fun z hz => heq z (hWR hz)) hzeroR
  refine ⟨d, hd, hdR.trans hRr, hqi, hq1, hqI, C, hC, ?_⟩
  intro z hz w hw
  have hKsmall : (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) ⊆ KR :=
    inter_subset_inter (closedBall_subset_closedBall hdR.le) Subset.rfl
  have hgrad (p : ℂ) (hp : p ∈ KR) : halfDiskGradient H R p = halfDiskGradient H r p := by
    unfold halfDiskGradient
    rw [hder p hp]
  rw [← hgrad z (hKsmall hz), ← hgrad w (hKsmall hw)]
  exact hholder z hz w hw

end PoincareConjecture.M64
