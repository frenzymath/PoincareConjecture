import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.FreeTraceSubsequence
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Def19_12_PositiveDegree










set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "S" => interior m64AnnulusDomain




theorem positive_ramp_lift_uniform_lower_slope
    (P : M62.CircleProductData F circumference) (gamma : ℝ → P.charts.Point)
    (L : M63PositiveDegreeLift P gamma) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∀ x y : ℝ, x ≤ y → alpha * (y - x) ≤ L.lift y - L.lift x := by
  have hperiod : Function.Periodic (deriv L.lift) curvePeriod := by
    intro x
    have heq : (fun y => L.lift (y + curvePeriod)) =
        (fun y => L.lift y + (L.degree : ℝ) * circumference) := funext L.period_shift
    have hh := congrArg (fun f : ℝ → ℝ => deriv f x) heq
    simpa only [deriv_comp_add_const, deriv_add_const] using hh
  have hcont : Continuous (deriv L.lift) := L.regular.continuous_deriv (by norm_num)
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  obtain ⟨x0, -, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) curvePeriod).Nonempty from ⟨0, le_rfl, hP.le⟩) hcont.continuousOn
  refine ⟨deriv L.lift x0, L.derivative_positive x0, ?_⟩
  have hbound (x : ℝ) : deriv L.lift x0 ≤ deriv L.lift x := by
    obtain ⟨y, hy, hxy⟩ := hperiod.exists_mem_Ico₀ hP x
    rw [hxy]
    exact hmin (Ico_subset_Icc_self hy)
  intro x y hxy
  exact mul_sub_le_image_sub_of_le_deriv (L.regular.differentiable (by norm_num)) hbound hxy




theorem free_ramp_lower_label_logarithmic_constant
    (P : M62.CircleProductData F circumference) (t : ℝ) (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma t)
    {lo hi : ℝ} (hlo : 0 < lo) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (sigma : M64PeriodicDegreeOneLift) (c1 : ℝ → P.charts.Point)
        (A : M64Annulus (P.flow.metric t) (gamma ∘ sigma.map) c1),
        ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map S →
        ∀ r ∈ Icc lo hi,
        IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
          r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2) m64AnnulusDomain →
        ∀ x rho : ℝ, 0 < rho → rho < x → x + rho < curvePeriod → rho < 1 →
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
  intro sigma c1 A hA r hr hE x rho hrho hx hP hradius N hN
  let L0 := L.lift ∘ sigma.map
  have hL0 : Continuous L0 := L.regular.continuous.comp (degreeOneLift_continuous sigma)
  have hmono : Monotone L0 := (strictMono_of_deriv_pos L.derivative_positive).monotone.comp
    sigma.monotone
  have hzero (y : ℝ) (_hy : y ∈ Icc (0 : ℝ) curvePeriod) :
      P.circle.quotient (L0 y) = ((gamma ∘ sigma.map) y).2 := L.quotient_eq (sigma.map y)
  have hphase := annulus_lower_phase_logarithmic_bound P t A hA L0 hL0 hzero
    (hmono.monotoneOn _) hlo hr hE hrho hx hP hradius hN
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

end PoincareConjecture.M64
