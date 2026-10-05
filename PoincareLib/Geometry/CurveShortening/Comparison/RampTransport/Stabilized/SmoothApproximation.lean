import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Smooth.PairApproximation
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Stabilization.Free.RampImmersedMinimum
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Stabilization.Area.Convergence
import PoincareLib.Geometry.RicciFlow.Product.Circle.Flow

/-!
# Actual separated minima of smooth ramp approximations

The auxiliary offset is chosen after the smooth pair and its connecting
annulus, so the lifted competitor and its attained immersed minimum fit
the prescribed area budget. Only closed C1 and open-strip smoothness are
asserted for the minimum. Source: MT2007 Lemmas 19.15 and 19.31,
pp. 447-449 and 464-466; ramp transport approximation derivation.

Morgan--Tian context: the annulus in Lemma 19.31, printed pp. 464-466, and its intrinsic
comparison in Proposition 19.35, printed pp. 467-478.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareMT.M64.RampTransport

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

/-- The literal separated competitor and attained immersed minimum, with the regularity
currently proved by the minimum construction. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
structure SeparatedRampMinimum
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (source : M64Annulus (P.flow.metric time) gamma0 gamma1) (epsilon : ℝ) where
  offset : ℝ
  offset_pos : 0 < offset
  offset_lt_period : offset < auxiliary
  competitor : M64Annulus (Q.flow.metric time)
    (auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0)
    (auxiliaryCircleSection Q (Q.circle.quotient offset) ∘ gamma1)
  competitor_map : competitor.map = auxiliaryCircleRadialLift Q source.map offset
  competitor_area_error : competitor.area < source.area + epsilon
  modulus : ℝ
  modulus_pos : 0 < modulus
  first_label : M64PeriodicDegreeOneLift
  second_label : M64PeriodicDegreeOneLift
  minimum : M64Annulus (Q.flow.metric time)
    ((auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0) ∘ first_label.map)
    ((auxiliaryCircleSection Q (Q.circle.quotient offset) ∘ gamma1) ∘ second_label.map)
  closed_c1 : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 minimum.map
    {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1}
  interior_smooth : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ minimum.map
    m64AnnulusOpenStrip
  first_label_c1 : ContDiff ℝ 1 first_label.map
  second_label_c1 : ContDiff ℝ 1 second_label.map
  area_minimizing : minimum.area = m64LeastAnnulusArea (Q.flow.metric time)
    (auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0)
    (auxiliaryCircleSection Q (Q.circle.quotient offset) ∘ gamma1)
  conformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
    modulus * m60AreaGram (Q.flow.metric time) minimum.map p 0 0 =
      modulus⁻¹ * m60AreaGram (Q.flow.metric time) minimum.map p 1 1 ∧
    m60AreaGram (Q.flow.metric time) minimum.map p 0 1 = 0
  affine_phase : ∃ c : ℝ, c ≠ 0 ∧ Q.circle.quotient c = Q.circle.quotient offset ∧
    ∀ p, p 1 ∈ Icc (0 : ℝ) 1 → (minimum.map p).2 = Q.circle.quotient (c * p 1)
  within_immersion : ∀ p ∈ m64AnnulusDomain,
    0 < m64AnnulusWithinGram (Q.flow.metric time) minimum.map p 0 0 ∧
    0 < m64AnnulusWithinGram (Q.flow.metric time) minimum.map p 1 1 ∧
    Function.Injective
      (mfderivWithin (𝓡 2) (𝓡 ((n + 1) + 1)) minimum.map m64AnnulusDomain p)

namespace SeparatedRampMinimum

variable {P : M62.CircleProductData F circumference}
  {Q : M62.CircleProductData P.flow auxiliary} {time : ℝ}
  {gamma0 gamma1 : ℝ → P.charts.Point}
  {A : M64Annulus (P.flow.metric time) gamma0 gamma1} {epsilon : ℝ}

/-- The attained least area is at most the actual separated competitor's area.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem area_le_competitor (R : SeparatedRampMinimum P Q time gamma0 gamma1 A epsilon) :
    R.minimum.area ≤ R.competitor.area := by
  rw [R.area_minimizing]
  exact m64LeastAnnulusArea_le_annulus R.competitor

/-- The separated minimum inherits the competitor's area error.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem area_error (R : SeparatedRampMinimum P Q time gamma0 gamma1 A epsilon) :
    R.minimum.area < A.area + epsilon :=
  R.area_le_competitor.trans_lt R.competitor_area_error

end SeparatedRampMinimum

/-- A sufficiently small positive auxiliary separation constructs an actual immersed minimum
within any given area budget. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466; project
derivation `proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem exists_separated_ramp_minimum [T2Space M] [CompactSpace M]
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    {gamma0 gamma1 : ℝ → P.charts.Point}
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod) (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (A : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Nonempty (SeparatedRampMinimum P Q time gamma0 gamma1 A epsilon) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let K := volume.real m64AnnulusDomain +
    ∫ z in m64AnnulusDomain, m60EnergyDensity (P.flow.metric time) A.map z
  have hK : 0 ≤ K := add_nonneg ENNReal.toReal_nonneg
    (integral_nonneg (fun z => m60EnergyDensity_nonneg (P.flow.metric time) A.map z))
  have hK1 : 0 < K + 1 := by linarith
  let delta := min (auxiliary / 2) (epsilon / (2 * (K + 1)))
  have hdelta : 0 < delta := lt_min (half_pos Q.circle.positive)
    (div_pos hepsilon (mul_pos (by norm_num) hK1))
  have hsmall : delta < auxiliary :=
    (min_le_left _ _).trans_lt (by linarith [Q.circle.positive])
  have herror : delta * K < epsilon := by
    have hbound : delta * (2 * (K + 1)) ≤ epsilon :=
      (le_div_iff₀ (mul_pos (by norm_num) hK1)).mp (min_le_right _ _)
    nlinarith [mul_nonneg hdelta.le hK]
  obtain ⟨C, hCmap, hCarea⟩ := auxiliaryCircle_radial_annulus_area_bound Q time A delta
  have hCsmall : C.area < A.area + epsilon := by
    rw [abs_of_pos hdelta] at hCarea
    change C.area ≤ A.area + delta * K at hCarea
    linarith
  obtain ⟨m, hm, sigma0, sigma1, B, hBc, hBi, hs0, hs1, hmin, hconf, hphase, himm⟩ :=
    auxiliaryCircle_free_ramp_immersed_minimum P Q time gamma0 gamma1 hgamma0 hgamma1
      hp0 hp1 hramp0 hramp1 A hdelta hsmall
  exact ⟨{
    offset := delta
    offset_pos := hdelta
    offset_lt_period := hsmall
    competitor := C
    competitor_map := hCmap
    competitor_area_error := hCsmall
    modulus := m
    modulus_pos := hm
    first_label := sigma0
    second_label := sigma1
    minimum := B
    closed_c1 := hBc
    interior_smooth := hBi
    first_label_c1 := hs0
    second_label_c1 := hs1
    area_minimizing := hmin
    conformal := hconf
    affine_phase := hphase
    within_immersion := himm }⟩

/-- Smooth approximation and separated minimization, each with half the final area error.
The first turning margin remains 3/400 at r/2. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
structure StabilizedSmoothRampApproximation
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (A : M64Annulus (P.flow.metric time) gamma0 gamma1) (r epsilon : ℝ) where
  approximation : SmoothRampAnnulusApproximation P time gamma0 gamma1 A r (epsilon / 2)
  separated : SeparatedRampMinimum P Q time approximation.first approximation.second
    approximation.annulus (epsilon / 2)

namespace StabilizedSmoothRampApproximation

variable {P : M62.CircleProductData F circumference}
  {Q : M62.CircleProductData P.flow auxiliary} {time : ℝ}
  {gamma0 gamma1 : ℝ → P.charts.Point}
  {A : M64Annulus (P.flow.metric time) gamma0 gamma1} {r epsilon : ℝ}

/-- The two half-errors bound the stabilized competitor's total area error.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem competitor_area_error
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    S.separated.competitor.area < A.area + epsilon := by
  have h0 := S.approximation.area_error
  have h1 := S.separated.competitor_area_error
  linarith

/-- The actual stabilized minimum lies below original area plus epsilon.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem minimum_area_error
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    S.separated.minimum.area < A.area + epsilon :=
  S.separated.area_le_competitor.trans_lt S.competitor_area_error

/-- The lower constant lift of the smooth approximant is smooth.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem lower_smooth
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) ∞
      (auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ S.approximation.first) :=
  (auxiliaryCircle_section_contMDiff Q _).comp S.approximation.first_smooth

/-- The upper constant lift of the smooth approximant is smooth.
Source: MT Lemma 19.31, pp. 464-466; stabilized approximation derivation. -/
theorem upper_smooth
    (S : StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) ∞
      (auxiliaryCircleSection Q (Q.circle.quotient S.separated.offset) ∘
        S.approximation.second) :=
  (auxiliaryCircle_section_contMDiff Q _).comp S.approximation.second_smooth

end StabilizedSmoothRampApproximation

variable [T2Space M] [CompactSpace M]

/-- Every original admissible C2 ramp annulus has actual smooth approximants and an attained
separated minimum below its area plus epsilon. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem exists_stabilized_smooth_ramp_approximation
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary)
    {time : ℝ} (htime : time ∈ Icc a b)
    {gamma0 gamma1 : ℝ → P.charts.Point}
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod) (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (A : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {r : ℝ} (hr : 0 < r)
    (hlength : r ≤ m62Length P.flow (fun y _ => gamma0 y) time)
    (hturn : ∀ alpha beta : ℝ, alpha ≤ beta → beta ≤ alpha + curvePeriod →
      m63ArcLength P.flow (fun y _ => gamma0 y) time alpha beta ≤ r →
      m63ArcTotalCurvature P.flow (fun y _ => gamma0 y) time alpha beta < (1 / 200 : ℝ))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Nonempty (StabilizedSmoothRampApproximation P Q time gamma0 gamma1 A r epsilon) := by
  obtain ⟨S⟩ := exists_smooth_ramp_annulus_approximation P htime hgamma0 hgamma1 hp0 hp1
    hramp0 hramp1 A hr hlength hturn (half_pos hepsilon)
  obtain ⟨R⟩ := exists_separated_ramp_minimum P Q time
    (S.first_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (S.second_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    S.first_periodic S.second_periodic S.first_ramp S.second_ramp S.annulus
    (half_pos hepsilon)
  exact ⟨⟨S, R⟩⟩

/-- Compactness supplies an actual auxiliary product of unit circumference. Source:
Morgan--Tian Lemma 19.31, printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-trimmed-intrinsic-transport.md`. -/
theorem nonempty_auxiliary_unit_product (P : M62.CircleProductData F circumference) :
    Nonempty (M62.CircleProductData P.flow 1) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : SecondCountableTopology P.charts.Point :=
    ChartedSpace.secondCountable_of_sigmaCompact
      (EuclideanSpace ℝ (Fin (n + 1))) P.charts.Point
  exact M62.nonempty_circleProductData P.flow 1 (by norm_num)

end PoincareMT.M64.RampTransport
