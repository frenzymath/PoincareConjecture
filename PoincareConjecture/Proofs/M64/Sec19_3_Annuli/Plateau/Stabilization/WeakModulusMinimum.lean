import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.MinimizingSequence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ContinuousEnergyLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.OriginalCircleObservation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusMinimizer

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_exists_weak_modulus_minimizer
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (A0 : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta < auxiliary) :
    let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
    let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
    ∃ (m : ℕ) (e : Q.charts.Point → EuclideanSpace ℝ (Fin m))
      (R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
      (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (lo hi r : ℝ) (L0 L1 : ℝ → ℝ)
      (L : M64ObservedWeakAnnulus (n := (n + 1) + 1) e (c0 ∘ L0) (c1 ∘ L1)),
      ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := (n + 1) + 1) e ∧
      (∀ q, R (e q) = planarCircleObservation q.1.2) ∧ (∀ q, ‖R (e q)‖ = 1) ∧
      Continuous B ∧
      (∀ q v, 0 ≤ B q v v) ∧ (∀ q v w, B q v w = B q w v) ∧
      (∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
        B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
          (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = (Q.flow.metric time).inner q v v) ∧
      0 < lo ∧ lo ≤ hi ∧ r ∈ Icc lo hi ∧
      Continuous L0 ∧ Continuous L1 ∧ Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      (∀ s ∈ Icc lo hi, ∀ W : M64ObservedWeakAnnulus (n := (n + 1) + 1) e
        (c0 ∘ L0) (c1 ∘ L1), L.weightedEnergy B r ≤ W.weightedEnergy B s) ∧
      L.weightedEnergy B r ≤ m64LeastAnnulusArea (Q.flow.metric time) c0 c1 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
  let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
  obtain ⟨m, e, R, he, hei, hread, hR, hnorm⟩ :=
    auxiliaryCircle_observation_with_original_current P Q
  have he1 : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨B, K, hB, hK, hb, hpos, hsymm, hgram⟩ :=
    m64ChartReadable_observed_metric (g := Q.flow.metric time) e he1 hread
  obtain ⟨C, hC, hcoercive⟩ :=
    m64ObservedMetric_tangent_coercivity (g := Q.flow.metric time) e he1 B hgram
  have hdiag := m64ObservedMetric_tangent_diagonal (g := Q.flow.metric time) e he1 B hgram
  obtain ⟨lo, hi, hlo, hlohi, r, sigma0, sigma1, A, hr, -, -, -, hA, -, henergy⟩ :=
    auxiliaryCircle_free_minimizing_sequence P Q time gamma0 gamma1 hgamma0 hgamma1
      hp0 hp1 hramp0 A0 hdelta hsmall
  obtain ⟨r0, L0, L1, L, hr0, hc0, hc1, hm0, hm1, hP0, hP1, henergyL⟩ :=
    auxiliaryCircle_observed_continuous_energy_limit P Q time e he1 hei hread B hB hK hb
      hpos hsymm hdiag hC hcoercive gamma0 gamma1 hgamma0 hgamma1 hp0 hp1 hramp0 hramp1
      (Q.circle.quotient 0) (Q.circle.quotient delta) hlo sigma0 sigma1 A hA r hr henergy
  obtain ⟨rmin, hrmin, Lmin, hmin⟩ :=
    m64ObservedWeakAnnulus_weightedEnergy_attained e he1 hei hread B hB hK hb
      hpos hsymm hC hcoercive hlo hlohi L
  exact ⟨m, e, R, B, lo, hi, rmin, L0, L1, Lmin, he, hei, hread, hR, hnorm,
    hB, hpos, hsymm, hdiag,
    hlo, hlohi, hrmin, hc0, hc1, hm0, hm1, hP0, hP1, hmin,
    (hmin r0 hr0 L).trans henergyL⟩

end PoincareConjecture.M64
