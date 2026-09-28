import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampWeakMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

theorem auxiliaryCircle_free_ramp_continuous_minimum
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
      (R T : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane)
      (H0 H1 : ℝ ≃o ℝ) (D : ℝ)
      (B : Q.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ),
      ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 m) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := (n + 1) + 1) e ∧
      (∀ q, R (e q) = planarCircleObservation q.1.2) ∧
      (∀ q, T (e q) = planarCircleObservation q.2) ∧
      0 < D ∧
      (∀ x, H0 (x + curvePeriod) = H0 x + D) ∧
      (∀ x, H1 (x + curvePeriod) = H1 x + D) ∧
      (∀ x, P.circle.quotient (H0 x) = (gamma0 x).2) ∧
      (∀ x, P.circle.quotient (H1 x) = (gamma1 x).2) ∧
      Continuous B ∧ (∀ q v, 0 ≤ B q v v) ∧
      (∀ q v w, B q v w = B q w v) ∧
      (∀ (q : Q.charts.Point) (v : TangentSpace (𝓡 ((n + 1) + 1)) q),
        B q (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v)
          (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) = (Q.flow.metric time).inner q v v) ∧
      ∃ r : ℝ, 0 < r ∧
        ∃ L : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
            e R c0 c1 H0 H1 (curvePeriod / circumference) D,
          ContinuousOn L.annulus.map (interior m64AnnulusDomain) ∧
          L.annulus.weightedEnergy B r ≤ m64LeastAnnulusArea (Q.flow.metric time) c0 c1 ∧
          ∀ s : ℝ, 0 < s →
            ∀ A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
                e R c0 c1 H0 H1 (curvePeriod / circumference) D,
              L.annulus.weightedEnergy B r ≤ A.annulus.weightedEnergy B s := by
  obtain ⟨m, e, R, T, H0, H1, D, B, he, hei, hread, hR, hT, hD, hH0, hH1,
      hzero, hone, hB, hpos, hsymm, hdiag, r, hr, A, harea, hminimum⟩ :=
    auxiliaryCircle_free_ramp_weak_minimum P Q time gamma0 gamma1 hgamma0 hgamma1
      hp0 hp1 hramp0 hramp1 A0 hdelta hsmall
  obtain ⟨L, -, -, hL, -, -, -, -, henergy, hmin⟩ :=
    auxiliaryCircle_free_phase_continuous_minimum P Q (he.of_le (by simp)) hei hread
      hR A (Q.flow.metric time) B hB hpos hdiag hr hminimum
  refine ⟨m, e, R, T, H0, H1, D, B, he, hei, hread, hR, hT, hD, hH0, hH1,
    hzero, hone, hB, hpos, hsymm, hdiag, r, hr, L, hL, ?_, hmin⟩
  rw [henergy]
  exact harea

end PoincareConjecture.M64
