import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RegularArcGradient
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.NormalizedGradientFrame
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetBoundaryCollar

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M64

open M65Branch M65StrictTrace M65Gauss

theorem halfDisk_regular_arc_frame {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {H : ℂ → EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    {c : ℝ → EuclideanSpace ℝ (Fin n)} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ ∞ c J) {sigma : ℝ → ℝ} (hsigma : ContDiff ℝ 1 sigma)
    (hmono : Monotone sigma ∨ Antitone sigma)
    (hs0 : sigma 0 ∈ J) (hc0 : deriv c (sigma 0) ≠ 0)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) R ∩ {z | 0 < z.im}))
    (hboundary : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ R → H (s : ℂ) = c (sigma s))
    (hconf : ∀ z ∈ closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T I) (T I) ∧
        g.inner (H z) (T 1) (T I) = 0)
    (heq : ∀ z ∈ ball (0 : ℂ) R ∩ {w | 0 < w.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z))
    (hzero : ∀ z ∈ closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im},
      fderivWithin ℝ H (closedBall (0 : ℂ) R ∩ {w | 0 ≤ w.im}) z ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ d < R ∧
      let K := closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}
      let W := ball (0 : ℂ) d ∩ {z | 0 < z.im}
      let F := fun z => normalizedResidualFrame (g.euclideanCoefficients (H z))
        (halfDiskGradient H R z)
      ContinuousOn F K ∧ ContDiffOn ℝ 1 F W ∧
        (∀ z ∈ K, g.inner (H z) (F z).1 (F z).1 = 1 ∧
          g.inner (H z) (F z).1 (F z).2 = 0 ∧ g.inner (H z) (F z).2 (F z).2 = 1) ∧
        MemLp (fun z => fderiv ℝ F z 1) 2 (volume.restrict W) ∧
        MemLp (fun z => fderiv ℝ F z I) 2 (volume.restrict W) ∧
        (∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K, ∀ w ∈ K,
          ‖F z - F w‖ ≤ B * Real.sqrt ‖z - w‖) ∧
        ContDiffAt ℝ 1 (fun t : ℝ => (F (t : ℂ)).1) 0 := by
  have h00 := hzero 0 (by simp [hR.le])
  obtain ⟨d, hd, hdR, hgi, hg1, hgI, C, hC, hholder⟩ :=
    halfDisk_regular_arc_gradient D hR hJ hc hsigma hs0 hc0 hH hHi hboundary hconf heq h00
  obtain ⟨hF, hF1, hunit, hDF1, hDFI, hFholder⟩ :=
    halfDisk_normalized_actual_frame D hd hdR hH hconf hzero hgi hg1 hgI hC hholder
  have hsub := inter_subset_inter (closedBall_subset_closedBall (x := (0 : ℂ)) hdR.le)
    (Subset.rfl (s := {z : ℂ | 0 ≤ z.im}))
  have hfactor (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) d ∩ {w | 0 ≤ w.im}) :
      halfDiskGradient H d z = z ^ (0 : ℕ) • halfDiskGradient H R z := by
    simpa only [pow_zero, one_smul] using halfDiskGradient_restrict hd hdR.le hH hz
  have hcurve : ∀ᶠ t : ℝ in 𝓝 0, H (t : ℂ) = c (sigma t) := by
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, ‖(t : ℂ)‖ < R :=
      continuous_ofReal.norm.continuousAt.eventually (gt_mem_nhds (by simpa using hR))
    exact hnear.mono (fun t ht => hboundary t ht.le)
  obtain ⟨-, -, -, hT⟩ := halfDisk_boundary_tangent g hd (show Even (0 : ℕ) from ⟨0, rfl⟩)
    (hH.mono hsub) hfactor hF (fun z hz => (hunit z hz).1)
    ((hc.contDiffAt (hJ.mem_nhds hs0)).of_le (WithTop.coe_le_coe.mpr le_top))
    hc0 hsigma hmono hcurve
  exact ⟨d, hd, hdR, hF, hF1, hunit, hDF1, hDFI, hFholder, hT⟩

end PoincareConjecture.M64
