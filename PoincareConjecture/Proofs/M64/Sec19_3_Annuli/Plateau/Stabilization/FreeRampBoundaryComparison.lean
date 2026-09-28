import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryAngularComparison
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseBoundaryTargetChart
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryParameterWindow
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.BoundaryRampRegularity

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "S" => interior m64AnnulusDomain

theorem auxiliaryCircle_free_ramp_boundary_angular_comparison
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hramp0 : M63IsRampAt P gamma0 time) (q0 : Q.circle.Point)
    {e : Q.charts.Point → EuclideanSpace ℝ (Fin m)}
    (he : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e) (hei : IsClosedEmbedding e)
    (hread : M60.SUChartReadable (n := (n + 1) + 1) e)
    {Robs : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane}
    (hRobs : ∀ q, Robs (e q) = planarCircleObservation q.1.2)
    {c1 : ℝ → Q.charts.Point} {H0 H1 : ℝ ≃o ℝ} {D : ℝ}
    (A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1) e Robs
      (auxiliaryCircleSection Q q0 ∘ gamma0) c1 H0 H1 (curvePeriod / circumference) D)
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.annulus.map S)
    (hc1 : Continuous (e ∘ c1))
    (hH0 : ∀ y, H0 (y + curvePeriod) = H0 y + D)
    (hH1 : ∀ y, H1 (y + curvePeriod) = H1 y + D)
    (hquot : ∀ y, P.circle.quotient (H0 y) = (gamma0 y).2)
    (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hB : Continuous B) {bound : ℝ} (hb : ∀ q, ‖B q‖ ≤ bound)
    (hpos : ∀ q v, 0 ≤ B q v v) {modulus : ℝ} (hmod : 0 < modulus)
    (hminimum : ∀ C : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1) e Robs
        (auxiliaryCircleSection Q q0 ∘ gamma0) c1 H0 H1 (curvePeriod / circumference) D,
      A.annulus.weightedEnergy B modulus ≤ C.annulus.weightedEnergy B modulus)
    {x0 : ℝ} (hx0 : x0 ∈ Ioo (0 : ℝ) curvePeriod) :
    ∃ width C : ℝ, 0 < width ∧ 0 < C ∧
      (∀ x ∈ Icc (x0 - width) (x0 + width), width < x ∧ x + width < curvePeriod) ∧
      width < 1 ∧ ∀ x ∈ Icc (x0 - width) (x0 + width),
        ∀ epsilon R : ℝ, 0 < epsilon → R ≤ width →
        ∀ᵐ r ∂volume.restrict (Icc epsilon R),
          let angular := fun theta =>
            (-r * Real.sin theta) • A.annulus.column 0
              (r • angularPoint theta + annulusPoint x 0) +
            (r * Real.cos theta) • A.annulus.column 1
              (r • angularPoint theta + annulusPoint x 0)
          (∫ z in closedBall (annulusPoint x 0) r ∩ S,
            (B (A.annulus.map z) (A.annulus.column 0 z) (A.annulus.column 0 z) +
              B (A.annulus.map z) (A.annulus.column 1 z) (A.annulus.column 1 z)) / 2) ≤
            C * ∫ theta in Icc (0 : ℝ) Real.pi, ‖angular theta‖ ^ 2 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let c0 := auxiliaryCircleSection Q q0 ∘ gamma0
  let p := A.label0 x0
  have hc0 : Continuous (e ∘ c0) := he.continuous.comp
    ((auxiliaryCircle_section_contMDiff Q q0).continuous.comp hgamma0.continuous)
  have hreg := auxiliaryCircle_shifted_ramp_regular P Q time gamma0 hgamma0 hramp0 q0 p
  obtain ⟨H, Reconstruct, beta, Lip, rho, delta, eta, K, hrho, hdelta, heta, _, hK,
      _, _, hH, hLip, hHD, hP, hbeta, hPobs, hPD, hcap, haxis⟩ :=
    auxiliaryCircle_bounded_boundary_phase_chart P Q e he hei.isEmbedding hread Robs hRobs
      (fun t => c0 (t + p)) (hreg.1.of_le (by norm_num)) (hreg.2 0)
  obtain ⟨epsilon0, hepsilon0, hwindow⟩ := m64Boundary_parameter_window
    (A.labels_continuous hH0 hH1).1 hc0 x0 heta hdelta
  let width := min (epsilon0 / 4) (min (x0 / 4) (min ((curvePeriod - x0) / 4) (1 / 4)))
  have hw : 0 < width := by
    dsimp only [width]
    exact lt_min (by positivity) (lt_min (by linarith [hx0.1])
      (lt_min (by linarith [hx0.2]) (by norm_num)))
  have hwe : width ≤ epsilon0 / 4 := min_le_left _ _
  have hwx : width ≤ x0 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hwP : width ≤ (curvePeriod - x0) / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hw1 : width ≤ 1 / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbounds (x : ℝ) (hx : x ∈ Icc (x0 - width) (x0 + width)) :
      width < x ∧ x + width < curvePeriod := by
    constructor <;> linarith [hx.1, hx.2, hx0.1, hx0.2]
  have hcurveobs (t : ℝ) : Robs (e (c0 t)) =
      angularPoint ((curvePeriod / circumference) * H0 t) := by
    rw [hRobs]
    change planarCircleObservation (gamma0 t).2 = _
    rw [← hquot t, planarCircleObservation_quotient]
  have hk : curvePeriod / circumference ≠ 0 :=
    div_ne_zero (by unfold curvePeriod; positivity) P.circle.positive.ne'
  let C := (max modulus modulus⁻¹) ^ 2 * bound * K ^ 4 / 4 * (1 + 4 * Real.pi ^ 2) +
    1 + Real.pi * A.annulus.energy B / (delta / 2) ^ 2
  have hC : 0 < C := by
    have hb0 := (norm_nonneg (B (A.annulus.map 0))).trans (hb _)
    have hE := A.annulus.energy_nonneg B hpos
    dsimp only [C]
    positivity
  refine ⟨width, C, hw, hC, hbounds, by linarith, ?_⟩
  intro x hx epsilon R hepsilon hR
  exact (A.lower_halfDisk_angular_energy_comparison (he.of_le (by simp)) hei hA B hB hb
    hpos hmod hminimum hc0 hc1 hH0 hH1 H Reconstruct beta hrho hdelta hK.le hk
    hH hLip hHD hP hbeta
    (fun y hy => hPobs y ((closedBall_subset_ball (by linarith : rho < 2 * rho)) hy)) hPD
    (by simpa only [zero_add] using hcap) haxis hcurveobs
    (fun y hy => hwindow y (abs_lt.mpr ⟨by linarith [hy.1, hx.1],
      by linarith [hy.2, hx.2]⟩)) hw (hbounds x hx).1 (hbounds x hx).2
    (by linarith) hepsilon hR).2

end PoincareConjecture.M64
