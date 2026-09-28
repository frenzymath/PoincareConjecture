import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RampLabelOscillation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.LogarithmicContinuity

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

theorem normalizedDegreeOneLift_equicontinuousAt
    (sigma : ℕ → M64PeriodicDegreeOneLift) {x : ℝ}
    (h : EquicontinuousAt (fun j => (sigma j).map) x) :
    EquicontinuousAt (fun j => (normalizedDegreeOneLift (sigma j)).map) x := by
  apply Metric.equicontinuousAt_iff.mpr
  intro eps heps
  obtain ⟨d, hd, hdist⟩ := Metric.equicontinuousAt_iff.mp h eps heps
  refine ⟨d, hd, ?_⟩
  intro y hy j
  convert hdist y hy j using 1
  simp only [Real.dist_eq, normalizedDegreeOneLift]
  congr 1
  ring

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "S" => interior m64AnnulusDomain

theorem free_ramp_lower_labels_locally_equicontinuous
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    {lo hi : ℝ} (hlo : 0 < lo)
    (sigma : ℕ → M64PeriodicDegreeOneLift) (c1 : ℕ → ℝ → P.charts.Point)
    (A : ∀ j, M64Annulus (P.flow.metric t) (gamma ∘ (sigma j).map) (c1 j))
    (hA : ∀ j, ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (A j).map S)
    (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi)
    (hE : ∀ j, IntegrableOn (fun p =>
      (r j * m60AreaGram (P.flow.metric t) (A j).map p 0 0 +
        (r j)⁻¹ * m60AreaGram (P.flow.metric t) (A j).map p 1 1) / 2) m64AnnulusDomain)
    (K : ℝ) (hK : ∀ j, m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤ K) :
    ∀ x ∈ Ioo (0 : ℝ) curvePeriod, EquicontinuousAt (fun j => (sigma j).map) x := by
  obtain ⟨C, hC, hosc⟩ := free_ramp_lower_label_logarithmic_constant P t gamma
    hgamma hperiod hramp (hi := hi) hlo
  intro x hx
  obtain ⟨rho, hrho, hsmall⟩ := exists_between
    (lt_min hx.1 (lt_min (sub_pos.mpr hx.2) zero_lt_one))
  have hxl := (lt_min_iff.mp hsmall).1
  have hPr := (lt_min_iff.mp (lt_min_iff.mp hsmall).2).1
  have hradius := (lt_min_iff.mp (lt_min_iff.mp hsmall).2).2
  apply equicontinuousAt_of_monotone_logarithmic_gap (fun j => (sigma j).map)
    (fun j => (sigma j).monotone.monotoneOn _) hrho hxl (by linarith) (C * K)
  intro j N hN
  exact (hosc (sigma j) (c1 j) (A j) (hA j) (r j) (hr j) (hE j)
    x rho hrho hxl (by linarith) hradius N hN).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hK j) hC.le)
      (by positivity : (0 : ℝ) ≤ N))

theorem free_ramp_lower_labels_continuous_local_limit
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    {lo hi : ℝ} (hlo : 0 < lo)
    (sigma : ℕ → M64PeriodicDegreeOneLift) (c1 : ℕ → ℝ → P.charts.Point)
    (A : ∀ j, M64Annulus (P.flow.metric t) (gamma ∘ (sigma j).map) (c1 j))
    (hA : ∀ j, ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (A j).map S)
    (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi)
    (hE : ∀ j, IntegrableOn (fun p =>
      (r j * m60AreaGram (P.flow.metric t) (A j).map p 0 0 +
        (r j)⁻¹ * m60AreaGram (P.flow.metric t) (A j).map p 1 1) / 2) m64AnnulusDomain)
    (K : ℝ) (hK : ∀ j, m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤ K) :
    ∃ (k : ℕ → ℕ) (L : ℝ → ℝ), StrictMono k ∧ Monotone L ∧
      (∀ x, L (x + curvePeriod) = L x + curvePeriod) ∧
      (∀ x ∈ Ioo (0 : ℝ) curvePeriod, ContinuousAt L x) ∧
      (∀ x ∈ Ioo (0 : ℝ) curvePeriod,
        Tendsto (fun j => (normalizedDegreeOneLift (sigma (k j))).map x) atTop (𝓝 (L x))) ∧
      ∀ᵐ x ∂volume,
        Tendsto (fun j => (normalizedDegreeOneLift (sigma (k j))).map x) atTop (𝓝 (L x)) := by
  let f := fun j => (normalizedDegreeOneLift (sigma j)).map
  have hbounded (x : ℝ) : ∃ lo hi : ℝ, ∀ j, f j x ∈ Icc lo hi :=
    ⟨x - curvePeriod, x + 2 * curvePeriod, fun j => normalizedDegreeOneLift_bounds (sigma j) x⟩
  obtain ⟨k, L, hk, hL, hliminf, hcontlim, hae⟩ := monotone_sequence_subsequence_ae f
    (fun j => (normalizedDegreeOneLift (sigma j)).monotone) hbounded
  have hequi := free_ramp_lower_labels_locally_equicontinuous P t gamma hgamma hperiod hramp
    hlo sigma c1 A hA r hr hE K hK
  have hcont (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) curvePeriod) : ContinuousAt L x := by
    rw [show L = (fun y => liminf (fun j => f (k j) y) atTop) from funext hliminf]
    exact continuousAt_liminf_of_equicontinuousAt (fun j => f (k j))
      (fun y => ⟨y - curvePeriod, y + 2 * curvePeriod,
        fun j => normalizedDegreeOneLift_bounds (sigma (k j)) y⟩)
      ((normalizedDegreeOneLift_equicontinuousAt sigma (hequi x hx)).comp k)
  refine ⟨k, L, hk, hL, ?_, hcont, fun x hx => hcontlim x (hcont x hx), hae⟩
  intro x
  rw [hliminf, hliminf]
  exact liminf_period_shift (fun j => f (k j))
    (fun j => (normalizedDegreeOneLift (sigma (k j))).period_shift)
    (fun y => ⟨y - curvePeriod, y + 2 * curvePeriod,
      fun j => normalizedDegreeOneLift_bounds (sigma (k j)) y⟩) x

end PoincareConjecture.M64
