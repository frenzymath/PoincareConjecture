import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ProjectedWeightedEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RampLabelPairLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "Strip" => preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)

theorem auxiliaryCircle_free_labels_continuous_limit
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (q0 q1 : Q.circle.Point)
    {lo hi : ℝ} (hlo : 0 < lo) (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
    (A : ∀ j, M64Annulus (Q.flow.metric time)
      ((auxiliaryCircleSection Q q0 ∘ gamma0) ∘ (sigma0 j).map)
      ((auxiliaryCircleSection Q q1 ∘ gamma1) ∘ (sigma1 j).map))
    (hA : ∀ j, ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 (A j).map Strip)
    (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi)
    (K : ℝ) (hK : ∀ j, m64ClassicalWeightedGramEnergy (Q.flow.metric time) (A j) (r j) ≤ K) :
    ∃ (k : ℕ → ℕ) (L0 L1 : ℝ → ℝ), StrictMono k ∧ Continuous L0 ∧ Continuous L1 ∧
      Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L0 0 ∈ Icc (0 : ℝ) curvePeriod ∧ L1 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      (∀ x, Tendsto (fun j => (normalizedDegreeOneLift (sigma0 (k j))).map x)
        atTop (𝓝 (L0 x))) ∧
      ∀ x, Tendsto (fun j => (normalizedDegreeOneLift (sigma1 (k j))).map x)
        atTop (𝓝 (L1 x)) := by
  classical
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let := Q.charts.chartedSpace
  choose D hmap henergy using fun j =>
    auxiliaryCircle_projected_weightedEnergy Q time (A j) (hlo.trans_le (hr j).1)
  have hfst : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 (n + 1)) 1
      (Prod.fst : Q.charts.Point → P.charts.Point) :=
    (contMDiff_fst.comp Q.charts.to_product_smooth).of_le (by simp)
  have hD (j : ℕ) : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (D j).map Strip := by
    rw [hmap j]
    exact hfst.comp_contMDiffOn (hA j)
  exact free_ramp_labels_continuous_limit P time gamma0 gamma1 hgamma0 hgamma1 hp0 hp1
    hramp0 hramp1 hlo sigma0 sigma1 D hD r hr
    (fun j => (D j).weightedGramEnergy_integrable (r j)) K
    (fun j => (henergy j).trans (hK j))

end PoincareConjecture.M64
