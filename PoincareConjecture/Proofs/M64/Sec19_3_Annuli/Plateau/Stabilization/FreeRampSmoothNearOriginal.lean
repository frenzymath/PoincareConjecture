import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.AreaConvergence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampSmoothMinimum








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}




theorem auxiliaryCircle_free_ramp_smooth_minimum_near_original_area
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (A0 : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ delta < auxiliary ∧
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
            (mfderiv (𝓡 ((n + 1) + 1)) (𝓡 m) e q v) =
            (Q.flow.metric time).inner q v v) ∧
        ∃ r : ℝ, 0 < r ∧
          ∃ L : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
              e R c0 c1 H0 H1 (curvePeriod / circumference) D,
            ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ L.annulus.map
              (interior m64AnnulusDomain) ∧
            L.annulus.weightedEnergy B r ≤
              m64LeastAnnulusArea (P.flow.metric time) gamma0 gamma1 + epsilon ∧
            ∀ s : ℝ, 0 < s →
      ∀ A : M64FreeWeakPhaseAnnulus (n := (n + 1) + 1)
                  e R c0 c1 H0 H1 (curvePeriod / circumference) D,
                L.annulus.weightedEnergy B r ≤ A.annulus.weightedEnergy B s := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let hlim := auxiliaryCircle_lifted_leastArea_tendsto Q time A0
  have hnear0 := (Metric.tendsto_nhds.1 hlim) epsilon hepsilon
  have hnear : ∀ᶠ delta : ℝ in 𝓝[>] 0,
      m64LeastAnnulusArea (Q.flow.metric time)
          (auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0)
          (auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1) <
        m64LeastAnnulusArea (P.flow.metric time) gamma0 gamma1 + epsilon := by
    filter_upwards [hnear0.filter_mono nhdsWithin_le_nhds] with delta hdist
    have hdist' :
        |m64LeastAnnulusArea (Q.flow.metric time)
            (auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0)
            (auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1) -
          m64LeastAnnulusArea (P.flow.metric time) gamma0 gamma1| < epsilon := by
      simpa only [Real.dist_eq] using hdist
    have hle := le_abs_self
      (m64LeastAnnulusArea (Q.flow.metric time)
          (auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0)
          (auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1) -
        m64LeastAnnulusArea (P.flow.metric time) gamma0 gamma1)
    linarith
  have hgood : ∀ᶠ delta : ℝ in 𝓝[>] 0,
      delta ∈ Ioo (0 : ℝ) auxiliary ∧
        m64LeastAnnulusArea (Q.flow.metric time)
            (auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0)
            (auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1) <
          m64LeastAnnulusArea (P.flow.metric time) gamma0 gamma1 + epsilon := by
    filter_upwards [Ioo_mem_nhdsGT (show 0 < auxiliary from Q.circle.positive), hnear]
      with delta hdelta harea
    exact ⟨hdelta, harea⟩
  obtain ⟨delta, hdelta, harea⟩ := hgood.exists
  let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
  let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
  obtain ⟨m, e, R, T, H0, H1, D, B, he, hei, hread, hR, hT, hD, hH0, hH1,
      hzero, hone, hB, hpos, hsymm, hdiag, r, hr, L, hsm, hLarea, hminimum⟩ :=
    auxiliaryCircle_free_ramp_smooth_minimum P Q time gamma0 gamma1 hgamma0 hgamma1
      hp0 hp1 hramp0 hramp1 A0 hdelta.1 hdelta.2
  have hLarea' : L.annulus.weightedEnergy B r ≤
      m64LeastAnnulusArea (P.flow.metric time) gamma0 gamma1 + epsilon := by
    exact hLarea.trans harea.le
  exact ⟨delta, hdelta.1, hdelta.2, m, e, R, T, H0, H1, D, B, he, hei, hread,
    hR, hT, hD, hH0, hH1, hzero, hone, hB, hpos, hsymm, hdiag, r, hr, L, hsm,
    hLarea', hminimum⟩

end PoincareConjecture.M64
