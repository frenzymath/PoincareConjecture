import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.HalfDiskGradientRegularity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.HalfDiskBoundaryFrame

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

theorem halfDisk_label_gradient_regular
    {g : RiemannianMetric n E} (D : LeviCivitaData g)
    {H : ℂ → E} {r : ℝ} (hr : 0 < r)
    {c : ℝ → E} {sigma : ℝ → ℝ} (hsigma : ContDiff ℝ 1 sigma)
    (hc : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ r → DifferentiableAt ℝ c (sigma s))
    {V : E → E} {U : Set E} (j : Fin n) (hU : IsOpen U)
    (hV : ContDiffOn ℝ ∞ V U) (hj : ∀ q ∈ U, V q j ≠ 0)
    (hH : ContDiffOn ℝ 1 H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hHi : ContDiffOn ℝ ∞ H (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hHU : MapsTo H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) U)
    (hboundary : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ r → H (s : ℂ) = c (sigma s))
    (hVcurve : ∀ s : ℝ, ‖(s : ℂ)‖ ≤ r → V (H (s : ℂ)) = deriv c (sigma s))
    (hconf : ∀ z ∈ closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im},
      let T := fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {w | 0 ≤ w.im}) z
      g.inner (H z) (T 1) (T 1) = g.inner (H z) (T I) (T I) ∧
        g.inner (H z) (T 1) (T I) = 0)
    (heq : ∀ z ∈ ball (0 : ℂ) r ∩ {w | 0 < w.im},
      dbar (complexGradient H) z = harmonicMatrix D H z (complexGradient H z))
    (hzero : fderivWithin ℝ H (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) 0 ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ d < r ∧
      ContDiffOn ℝ 1 (complexGradient H) (ball (0 : ℂ) d ∩ {z | 0 < z.im}) ∧
      MemLp (fun z => fderiv ℝ (complexGradient H) z 1)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      MemLp (fun z => fderiv ℝ (complexGradient H) z I)
        2 (volume.restrict (ball (0 : ℂ) d ∩ {z | 0 < z.im})) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
        ∀ w ∈ closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im},
          ‖halfDiskGradient H r z - halfDiskGradient H r w‖ ≤ C * Real.sqrt ‖z - w‖ := by
  let : Nonempty (Fin n) := ⟨j⟩
  let K := closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}
  let K2 := closedBall (0 : ℂ) (r / 2) ∩ {z | 0 ≤ z.im}
  have hr2 : 0 < r / 2 := half_pos hr
  have hK2 : K2 ⊆ K := inter_subset_inter (closedBall_subset_closedBall (by linarith)) Subset.rfl
  have hW2 : (ball (0 : ℂ) (r / 2) ∩ {z | 0 < z.im}) ⊆
      (ball (0 : ℂ) r ∩ {z | 0 < z.im}) :=
    inter_subset_inter (ball_subset_ball (by linarith)) Subset.rfl
  have hder (z : ℂ) (hz : z ∈ K2) : fderivWithin ℝ H K2 z = fderivWithin ℝ H K z :=
    fderivWithin_subset hK2 ((halfDisk_differential_domain hr2).2.2.1 z hz)
      ((hH z (hK2 hz)).differentiableWithinAt one_ne_zero)
  have hgrad (z : ℂ) (hz : z ∈ K2) : halfDiskGradient H (r / 2) z = halfDiskGradient H r z := by
    unfold halfDiskGradient
    rw [hder z hz]
  let L := fun q => complexifyOperator (metricRowFrame (g.inner q) (V q) j)
  have hG : ContDiffOn ℝ ∞ g.euclideanCoefficients U :=
    (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).contDiffOn
  have hL : ContDiffOn ℝ ∞ L U :=
    complexifyOperator.contDiff.comp_contDiffOn (metricRowFrame_contDiffOn j hG hV hj)
  have hunit (z : ℂ) (hz : z ∈ K2) : IsUnit (L (H z)) :=
    metricRowFrame_complex_isUnit _ _ j (hj _ (hHU (hK2 hz))) (g.pos _)
  have hreal (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (r / 2)) (hi : z.im = 0) :
      metricBoundaryReflection j (halfDiskFramedGradient H L (r / 2) z) =
        halfDiskFramedGradient H L (r / 2) z := by
    have hzlt : ‖z‖ < r := (mem_closedBall_zero_iff.mp hz).trans_lt (by linarith)
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    have hz2 : z ∈ K2 := ⟨hz, by simp [hi]⟩
    have hzK : (z.re : ℂ) ∈ K := he.symm ▸ hK2 hz2
    have hnorm : ‖(z.re : ℂ)‖ < r := by rwa [he]
    have hh := halfDisk_metricFrame_reality_of_label (hc z.re hnorm.le)
      hsigma j hH hboundary hnorm
      (hVcurve z.re hnorm.le) (hj _ (hHU hzK)) (hconf _ hzK).1 (hconf _ hzK).2
    have hh' : metricBoundaryReflection j (halfDiskFramedGradient H L r z) =
        halfDiskFramedGradient H L r z := by simpa only [he] using hh
    simpa only [halfDiskFramedGradient, hgrad z hz2] using hh'
  have hzero2 : fderivWithin ℝ H K2 0 ≠ 0 := by
    rw [hder 0 (by simp [K2, hr2.le])]
    exact hzero
  obtain ⟨d, hd, hdr, hqi, hq1, hqI, C, hC, hholder⟩ :=
    halfDisk_immersed_gradient_regular D (metricBoundaryReflection j)
      (metricBoundaryReflection_smul j) (metricBoundaryReflection_involutive j)
      hr2 hU hL (hH.mono hK2) (hHi.mono hW2) (hHU.mono hK2 Subset.rfl)
      hunit (fun z hz => heq z (hW2 hz)) hreal hzero2
  refine ⟨d, hd, hdr.trans (by linarith), hqi, hq1, hqI, C, hC, ?_⟩
  intro z hz w hw
  have hsmall : (closedBall (0 : ℂ) d ∩ {z | 0 ≤ z.im}) ⊆ K2 :=
    inter_subset_inter (closedBall_subset_closedBall hdr.le) Subset.rfl
  rw [← hgrad z (hsmall hz), ← hgrad w (hsmall hw)]
  exact hholder z hz w hw

end PoincareConjecture.M64
