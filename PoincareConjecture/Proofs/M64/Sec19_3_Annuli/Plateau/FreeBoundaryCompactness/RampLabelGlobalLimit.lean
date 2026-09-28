import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FullStripOscillation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RampLabelLocalLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.UniformLogarithmicContinuity









set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)




theorem free_ramp_global_lower_label_logarithmic_constant
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    {lo hi : ℝ} (hlo : 0 < lo) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (sigma : M64PeriodicDegreeOneLift) (c1 : ℝ → P.charts.Point)
        (A : M64Annulus (P.flow.metric t) (gamma ∘ sigma.map) c1),
        ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map Strip →
        ∀ r ∈ Icc lo hi,
        IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2) m64AnnulusDomain →
        ∀ x rho : ℝ, 0 < rho → rho < curvePeriod / 2 → rho < 1 →
        ∀ N : ℕ, 0 < N →
          (sigma.map (x + rho * Real.exp (-(N : ℝ))) -
            sigma.map (x - rho * Real.exp (-(N : ℝ)))) ^ 2 ≤
              C * m64ClassicalWeightedGramEnergy (P.flow.metric t) A r / N := by
  obtain ⟨L⟩ := m63PositiveDegreeLift_nonempty P gamma hperiod hgamma hramp
  obtain ⟨alpha, halpha, hlower⟩ := positive_ramp_lift_uniform_lower_slope P gamma L
  let K := 2 * Real.pi * max lo⁻¹ hi
  have hK : 0 < K := mul_pos (by positivity)
    ((inv_pos.mpr hlo).trans_le (le_max_left _ _))
  refine ⟨K / alpha ^ 2, div_pos hK (sq_pos_of_pos halpha), ?_⟩
  intro sigma c1 A hA r hr hE x rho hrho hwidth hradius N hN
  let L0 := L.lift ∘ sigma.map
  have hL0 : Continuous L0 := L.regular.continuous.comp (degreeOneLift_continuous sigma)
  have hmono : Monotone L0 := (strictMono_of_deriv_pos L.derivative_positive).monotone.comp
    sigma.monotone
  have hzero (y : ℝ) : P.circle.quotient (L0 y) = ((gamma ∘ sigma.map) y).2 :=
    L.quotient_eq (sigma.map y)
  have hshift (y : ℝ) : L0 (y + curvePeriod) = L0 y + (L.degree : ℝ) * circumference := by
    dsimp only [L0, Function.comp_apply]
    rw [sigma.period_shift, L.period_shift]
  have hphase := annulus_full_strip_lower_phase_bound P t A hA L0 hL0 hzero
    hshift hmono hlo hr hE x hrho hwidth hradius hN
  have hrad : 0 ≤ rho * Real.exp (-(N : ℝ)) := by positivity
  have hlabel := sigma.monotone
    (show x - rho * Real.exp (-(N : ℝ)) ≤ x + rho * Real.exp (-(N : ℝ)) by linarith)
  have hlow := hlower _ _ hlabel
  have hscale : 0 ≤ alpha * (sigma.map (x + rho * Real.exp (-(N : ℝ))) -
      sigma.map (x - rho * Real.exp (-(N : ℝ)))) :=
    mul_nonneg halpha.le (sub_nonneg.mpr hlabel)
  have hsquare := (sq_le_sq₀ hscale (hscale.trans hlow)).mpr hlow
  have hcombined := hsquare.trans hphase
  have hdivide : (sigma.map (x + rho * Real.exp (-(N : ℝ))) -
      sigma.map (x - rho * Real.exp (-(N : ℝ)))) ^ 2 ≤
        (K * m64ClassicalWeightedGramEnergy (P.flow.metric t) A r / N) / alpha ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos halpha)).mpr
    simpa only [mul_pow, mul_comm, K] using hcombined
  exact hdivide.trans_eq (by ring)




theorem free_ramp_lower_labels_uniformEquicontinuous
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    {lo hi : ℝ} (hlo : 0 < lo)
    (sigma : ℕ → M64PeriodicDegreeOneLift) (c1 : ℕ → ℝ → P.charts.Point)
    (A : ∀ j, M64Annulus (P.flow.metric t) (gamma ∘ (sigma j).map) (c1 j))
    (hA : ∀ j, ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (A j).map Strip)
    (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi)
    (hE : ∀ j, IntegrableOn (fun p =>
      (r j * m60AreaGram (P.flow.metric t) (A j).map p 0 0 +
        (r j)⁻¹ * m60AreaGram (P.flow.metric t) (A j).map p 1 1) / 2) m64AnnulusDomain)
    (K : ℝ) (hK : ∀ j, m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤ K) :
    UniformEquicontinuous (fun j => (sigma j).map) := by
  obtain ⟨C, hC, hosc⟩ := free_ramp_global_lower_label_logarithmic_constant P t gamma
    hgamma hperiod hramp (hi := hi) hlo
  obtain ⟨rho, hrho, hsmall⟩ := exists_between
    (lt_min (by unfold curvePeriod; positivity : (0 : ℝ) < curvePeriod / 2) zero_lt_one)
  apply uniformEquicontinuous_of_monotone_logarithmic_gap (fun j => (sigma j).map)
    (fun j => (sigma j).monotone) hrho (C * K)
  intro j x N hN
  exact (hosc (sigma j) (c1 j) (A j) (hA j) (r j) (hr j) (hE j)
    x rho hrho (lt_min_iff.mp hsmall).1 (lt_min_iff.mp hsmall).2 N hN).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hK j) hC.le)
      (by positivity : (0 : ℝ) ≤ N))




theorem free_ramp_lower_labels_continuous_limit
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    {lo hi : ℝ} (hlo : 0 < lo)
    (sigma : ℕ → M64PeriodicDegreeOneLift) (c1 : ℕ → ℝ → P.charts.Point)
    (A : ∀ j, M64Annulus (P.flow.metric t) (gamma ∘ (sigma j).map) (c1 j))
    (hA : ∀ j, ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (A j).map Strip)
    (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi)
    (hE : ∀ j, IntegrableOn (fun p =>
      (r j * m60AreaGram (P.flow.metric t) (A j).map p 0 0 +
        (r j)⁻¹ * m60AreaGram (P.flow.metric t) (A j).map p 1 1) / 2) m64AnnulusDomain)
    (K : ℝ) (hK : ∀ j, m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤ K) :
    ∃ (k : ℕ → ℕ) (L : ℝ → ℝ), StrictMono k ∧ Continuous L ∧ Monotone L ∧
      (∀ x, L (x + curvePeriod) = L x + curvePeriod) ∧ L 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      ∀ x, Tendsto (fun j => (normalizedDegreeOneLift (sigma (k j))).map x) atTop (𝓝 (L x)) := by
  let f := fun j => (normalizedDegreeOneLift (sigma j)).map
  have hbounded (x : ℝ) : ∃ lo hi : ℝ, ∀ j, f j x ∈ Icc lo hi :=
    ⟨x - curvePeriod, x + 2 * curvePeriod, fun j => normalizedDegreeOneLift_bounds (sigma j) x⟩
  obtain ⟨k, L, hk, hL, hliminf, hcontlim, -⟩ := monotone_sequence_subsequence_ae f
    (fun j => (normalizedDegreeOneLift (sigma j)).monotone) hbounded
  have hequi := free_ramp_lower_labels_uniformEquicontinuous P t gamma hgamma hperiod hramp
    hlo sigma c1 A hA r hr hE K hK
  have hcont : Continuous L := by
    apply continuous_iff_continuousAt.mpr
    intro x
    rw [show L = (fun y => liminf (fun j => f (k j) y) atTop) from funext hliminf]
    exact continuousAt_liminf_of_equicontinuousAt (fun j => f (k j))
      (fun y => ⟨y - curvePeriod, y + 2 * curvePeriod,
        fun j => normalizedDegreeOneLift_bounds (sigma (k j)) y⟩)
      ((normalizedDegreeOneLift_equicontinuousAt sigma (hequi.equicontinuous x)).comp k)
  have hlim (x : ℝ) := hcontlim x (hcont.continuousAt (x := x))
  refine ⟨k, L, hk, hcont, hL, ?_, ?_, hlim⟩
  · intro x
    rw [hliminf, hliminf]
    exact liminf_period_shift (fun j => f (k j))
      (fun j => (normalizedDegreeOneLift (sigma (k j))).period_shift)
      (fun y => ⟨y - curvePeriod, y + 2 * curvePeriod,
        fun j => normalizedDegreeOneLift_bounds (sigma (k j)) y⟩) x
  · exact isClosed_Icc.mem_of_tendsto (hlim 0)
      (Eventually.of_forall fun j =>
        Ico_subset_Icc_self (normalizedDegreeOneLift_zero (sigma (k j))))

end PoincareConjecture.M64
