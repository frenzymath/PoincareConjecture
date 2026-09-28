import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusMinimizingSequence
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RampContinuousWeakLimit

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)

theorem free_ramp_exists_continuous_weak_minimizing_limit
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hperiod0 : Function.Periodic gamma0 curvePeriod)
    (hperiod1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 t)
    (hramp1 : M63IsRampAt P gamma1 t)
    (hdisjoint : Disjoint (range gamma0) (range gamma1))
    (A0 : M64Annulus (P.flow.metric t) gamma0 gamma1) :
    ∃ (m : ℕ) (e : P.charts.Point → EuclideanSpace ℝ (Fin m))
      (B : P.charts.Point → EuclideanSpace ℝ (Fin m) →L[ℝ]
        EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
      (r0 : ℝ) (L0 L1 : ℝ → ℝ)
      (L : M64ObservedWeakAnnulus (n := n + 1) e
        (gamma0 ∘ L0) (gamma1 ∘ L1)),
      ContMDiff (𝓡 (n + 1)) (𝓡 m) ∞ e ∧
      IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n + 1) e ∧
      Continuous B ∧
      (∀ q v, 0 ≤ B q v v) ∧
      (∀ q v w, B q v w = B q w v) ∧
      (∀ (q : P.charts.Point) (v : TangentSpace (𝓡 (n + 1)) q),
        B q (mfderiv (𝓡 (n + 1)) (𝓡 m) e q v)
          (mfderiv (𝓡 (n + 1)) (𝓡 m) e q v) =
          (P.flow.metric t).inner q v v) ∧
      0 < r0 ∧
      Continuous L0 ∧ Continuous L1 ∧
      Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L.weightedEnergy B r0 ≤
        m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  obtain ⟨m, e, he, hei, hread⟩ :=
    M60.suCompactObservation_exists (n := n + 1) (M := P.charts.Point)
  have he1 : ContMDiff (𝓡 (n + 1)) (𝓡 m) 1 e := he.of_le (by simp)
  obtain ⟨B, K, hB, hK, hb, hpos, hsymm, hgram⟩ :=
    m64ChartReadable_observed_metric (g := P.flow.metric t) e he1 hread
  obtain ⟨C, hC, hcoercive⟩ :=
    m64ObservedMetric_tangent_coercivity (g := P.flow.metric t) e he1 B hgram
  obtain ⟨W0, -, -⟩ :=
    m64ObservedWeakAnnulus_of_annulus A0 e he1
  obtain ⟨lo, hi, hlo, hlohi, r, sigma0, sigma1, A, hr, hsigma, hmono,
      hderiv, hA, hbound, henergy⟩ :=
    free_ramp_minimizing_sequence_of_disjoint_images P t gamma0 gamma1 hgamma0
      hgamma1 hperiod0 hperiod1 hramp0 hdisjoint A0
  obtain ⟨k, r0, L0, L1, L, hk, hr0, hc0, hc1, hm0, hm1, hp0, hp1,
      h00, h10, hrlim, hlabel0, hlabel1, hmap, henergyL⟩ :=
    free_ramp_observed_continuous_energy_limit P t e he1 hei hread B hB hK hb
      hpos hsymm (m64ObservedMetric_tangent_diagonal (g := P.flow.metric t)
        e he1 B hgram) hC hcoercive gamma0 gamma1 hgamma0 hgamma1 hperiod0
      hperiod1 hramp0 hramp1 hlo (fun j => sigma0 j) (fun j => sigma1 j)
      (fun j => A j) hA r hr (show Tendsto
        (fun j => m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j)
          (r j)) atTop (𝓝 (m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1))
        from henergy)
  refine ⟨m, e, B, r0, L0, L1, L, he, hei, hread, hB, hpos, hsymm,
    m64ObservedMetric_tangent_diagonal (g := P.flow.metric t) e he1 B hgram,
    ?_, hc0, hc1, hm0, hm1, hp0, hp1, ?_⟩
  · exact hlo.trans_le hr0.1
  · exact henergyL

end PoincareConjecture.M64
