import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Stabilization.Projected.WeightedEnergy
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Free.ModulusPhaseEnergy

/-!
# Winding bounds from the original ramp circle

Projection of an actual stabilized annulus retains the original ramp
boundary. Its weighted energy decreases, so the original positive circle
degree gives the upper modulus bound in the twice enlarged target.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "Strip" => preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)

/-- Retain the original positive winding lower bound for stabilized weighted energy. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem auxiliaryCircle_free_annulus_weighted_energy_ge_original_winding
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma time)
    (q : Q.circle.Point) (sigma : M64PeriodicDegreeOneLift)
    {c1 : ℝ → Q.charts.Point}
    (A : M64Annulus (Q.flow.metric time)
      ((auxiliaryCircleSection Q q ∘ gamma) ∘ sigma.map) c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.map Strip)
    {r : ℝ} (hr : 0 < r) :
    r * circumference ^ 2 / (2 * curvePeriod) ≤
      m64ClassicalWeightedGramEnergy (Q.flow.metric time) A r := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let := Q.charts.chartedSpace
  obtain ⟨D, hmap, henergy⟩ := auxiliaryCircle_projected_weightedEnergy Q time A hr
  have hfst : ContMDiff (𝓡 ((n + 1) + 1)) (𝓡 (n + 1)) 1
      (Prod.fst : Q.charts.Point → P.charts.Point) :=
    (contMDiff_fst.comp Q.charts.to_product_smooth).of_le (by simp)
  have hD : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 D.map Strip := by
    rw [hmap]
    exact hfst.comp_contMDiffOn hA
  exact (free_ramp_annulus_weighted_energy_ge_winding P time gamma hgamma hperiod
    hramp sigma D hD hr (D.weightedGramEnergy_integrable r)).trans henergy

/-- Bound the stabilized modulus above using the retained original winding. Proof expansion
for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem auxiliaryCircle_free_annulus_modulus_le_original_winding
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hperiod : Function.Periodic gamma curvePeriod) (hramp : M63IsRampAt P gamma time)
    (q : Q.circle.Point) (sigma : M64PeriodicDegreeOneLift)
    {c1 : ℝ → Q.charts.Point}
    (A : M64Annulus (Q.flow.metric time)
      ((auxiliaryCircleSection Q q ∘ gamma) ∘ sigma.map) c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.map Strip)
    {r E : ℝ} (hr : 0 < r)
    (hbound : m64ClassicalWeightedGramEnergy (Q.flow.metric time) A r ≤ E) :
    r ≤ (2 * curvePeriod * E) / circumference ^ 2 := by
  have hh := (auxiliaryCircle_free_annulus_weighted_energy_ge_original_winding P Q time
    gamma hgamma hperiod hramp q sigma A hA hr).trans hbound
  have hP : 0 < 2 * curvePeriod := by unfold curvePeriod; positivity
  have hi := (div_le_iff₀ hP).mp hh
  apply (le_div_iff₀ (sq_pos_of_pos P.circle.positive)).mpr
  nlinarith

end PoincareMT.M64
