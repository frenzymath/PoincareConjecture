import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreePhaseSeed
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRampPhaseInverse
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseDegreeAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_ramp_phase_data
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (q0 q1 : Q.circle.Point) (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (A : M64Annulus (Q.flow.metric time)
      ((auxiliaryCircleSection Q q0 ∘ gamma0) ∘ sigma0.map)
      ((auxiliaryCircleSection Q q1 ∘ gamma1) ∘ sigma1.map))
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.map (interior m64AnnulusDomain)) :
    ∃ (H0 H1 : ℝ ≃o ℝ) (D : ℝ), 0 < D ∧
      (∀ x, H0 (x + curvePeriod) = H0 x + D) ∧
      (∀ x, H1 (x + curvePeriod) = H1 x + D) ∧
      (∀ x, P.circle.quotient (H0 x) = (gamma0 x).2) ∧
      ∀ x, P.circle.quotient (H1 x) = (gamma1 x).2 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let := Q.charts.chartedSpace
  obtain ⟨L0⟩ := m63PositiveDegreeLift_nonempty P gamma0 hp0 hgamma0 hramp0
  obtain ⟨L1⟩ := m63PositiveDegreeLift_nonempty P gamma1 hp1 hgamma1 hramp1
  obtain ⟨H0, hH0⟩ := positive_ramp_lift_orderIso P gamma0 L0
  obtain ⟨H1, hH1⟩ := positive_ramp_lift_orderIso P gamma1 L1
  obtain ⟨-, B, hBmap, -, -, -⟩ := m64ProjectedAnnulus_of_annulus Q time _ _ A
  have hfst : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 (n + 1)) 1
      (Prod.fst : Q.charts.Point → P.charts.Point) :=
    (contMDiff_fst.comp Q.charts.to_product_smooth).of_le (by simp)
  have hB : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 B.map (interior m64AnnulusDomain) := by
    rw [hBmap]
    exact hfst.comp_contMDiffOn hA
  have hinc (sigma : M64PeriodicDegreeOneLift) (L : ℝ → ℝ) (D : ℝ)
      (hL : ∀ x, L (x + curvePeriod) = L x + D) :
      (L ∘ sigma.map) curvePeriod = (L ∘ sigma.map) 0 + D := by
    have hp := sigma.period_shift 0
    rw [zero_add] at hp
    change L (sigma.map curvePeriod) = L (sigma.map 0) + D
    rw [hp, hL]
  have hdegree : (L0.degree : ℝ) * circumference = (L1.degree : ℝ) * circumference :=
    annulus_boundary_phase_increment_eq P time B hB
      (L0.lift ∘ sigma0.map) (L1.lift ∘ sigma1.map)
      (L0.regular.continuous.comp (degreeOneLift_continuous sigma0))
      (L1.regular.continuous.comp (degreeOneLift_continuous sigma1))
      (fun x _ => L0.quotient_eq (sigma0.map x))
      (fun x _ => L1.quotient_eq (sigma1.map x))
      (hinc sigma0 L0.lift _ L0.period_shift) (hinc sigma1 L1.lift _ L1.period_shift)
  refine ⟨H0, H1, (L0.degree : ℝ) * circumference,
    mul_pos (by exact_mod_cast L0.degree_positive) P.circle.positive, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [hH0] using L0.period_shift x
  · intro x
    simpa only [hH1, hdegree] using L1.period_shift x
  · intro x
    rw [hH0]
    exact L0.quotient_eq x
  · intro x
    rw [hH1]
    exact L1.quotient_eq x

end PoincareConjecture.M64
