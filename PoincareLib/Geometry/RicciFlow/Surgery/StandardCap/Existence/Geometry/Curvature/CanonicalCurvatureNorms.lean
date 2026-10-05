import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Coordinates.FiniteCoordinateOperatorBounds
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Energy.CanonicalDifferenceJetFluxParameters

/-!
# Uniform operator norms for canonical curvature backgrounds

The actual scalar curvature components control the nested tensor operator
norm. Compact elliptic metric-jet boxes also control the inverse bilinear
operator, before any open domain or geometry is chosen. These are the
background norms used for the curvature reaction in Morgan-Tian
Section 12.5, pp. 309-319; see raw-curvature-operator-norm.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The curvature tensor has three nested continuous-linear-map fibers.
set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareMT.M34

open DifferenceEnergy SpacetimeBounds SpacetimeBounds.Bootstrap

/-- Scalar bounds on all raised curvature entries control its actual
nested operator norm, including dimension zero
(Section 12.5, pp. 309-319). -/
theorem norm_curvature_le_of_raw_bound {n : ℕ} (R : FS n) {C : ℝ}
    (hC : ∀ l j k m, |raw R l j k m| ≤ C) : ‖R‖ ≤ (n : ℝ) ^ 4 * C := by
  let e := fun i : Fin n => EuclideanSpace.single i (1 : ℝ)
  have hv (j k m : Fin n) : ‖R (e j) (e k) (e m)‖ ≤ n * C := by
    simpa only [Fintype.card_fin] using
      PiLp.norm_le_card_mul_of_coordinates (R (e j) (e k) (e m))
        (fun l => hC l j k m)
  have h1 (j k : Fin n) : ‖R (e j) (e k)‖ ≤ n * (n * C) := by
    simpa only [Fintype.card_fin] using
      (R (e j) (e k)).opNorm_le_card_mul_of_coordinates (hv j k)
  have h2 (j : Fin n) : ‖R (e j)‖ ≤ n * (n * (n * C)) := by
    simpa only [Fintype.card_fin] using
      (R (e j)).opNorm_le_card_mul_of_coordinates (h1 j)
  have h3 : ‖R‖ ≤ n * (n * (n * (n * C))) := by
    simpa only [Fintype.card_fin] using R.opNorm_le_card_mul_of_coordinates h2
  convert h3 using 1
  ring

/-- The full inverse bilinear operator has a common norm bound on every
elliptic metric three-jet box (Section 12.5, pp. 309-319). -/
theorem inverseMetricThreeJet_bound (n : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ J : Jet (V n) (MetricCoefficient n) 3,
      ‖J‖ ≤ H →
      (∀ v, a * ‖v‖ ^ 2 ≤
        (continuousMultilinearCurryFin0 ℝ (V n) (MetricCoefficient n) (J 0)) v v) →
      ‖inverseMetricThreeJet n J‖ ≤ C := by
  obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box n 1 ha H
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((contDiffOn_inverseMetricThreeJet n).continuousOn.mono hKU)
  exact ⟨max C 1, le_max_right _ _, fun J hJ hell =>
    (hC J (hbox J hJ hell)).trans (le_max_left _ _)⟩

/-- One bound controls the actual inverse metric and every tensor with the
actual canonical curvature entries, before all domains and geometry
(Section 12.5, pp. 309-319). -/
theorem canonicalDomain_background_operatorNorm_bound
    (n : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
      letI := hNE
      letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ (g : RiemannianMetric n U) (D : LeviCivitaData g) (p : U) (x : V n), x ∈ U →
        (∀ j ≤ 3, ‖iteratedFDeriv ℝ j
          (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm) x‖ ≤ H) →
        (∀ v, a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x v v) →
        ∀ R : FS n, raw R = canonicalDomain_curvatureArray U hU g D p x →
          ‖(g.pullbackCoefficients (extChartAt (𝓡 n) p).symm x).inverse‖ ≤ C ∧ ‖R‖ ≤ C := by
  obtain ⟨CI, hCI, hI⟩ := inverseMetricThreeJet_bound n ha H
  obtain ⟨CB, hCB, hB⟩ := canonicalDomain_differenceEnergyBackground_bound n ha H
  refine ⟨max CI ((n : ℝ) ^ 4 * CB), hCI.trans (le_max_left _ _), ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro g D p x hx hjets hell R hR
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  let J := spatialJet 3 (fun z : ℝ × V n => B z.2) (0, x)
  have hH : 0 ≤ H := (norm_nonneg (iteratedFDeriv ℝ 0 B x)).trans (hjets 0 (by omega))
  have hJ : ‖J‖ ≤ H := by
    apply (pi_norm_le_iff_of_nonneg hH).mpr
    intro j
    exact hjets j (by omega)
  constructor
  · have hi := hI J hJ hell
    dsimp only [J, B] at hi
    rw [canonicalDomain_inverseMetricThreeJet U hU g p x] at hi
    exact hi.trans (le_max_left _ _)
  · have hb := hB U hU hNE g D p x hx hjets hell
    have hr : ‖canonicalDomain_curvatureArray U hU g D p x‖ ≤ CB := by
      exact (norm_fst_le _).trans ((norm_snd_le _).trans hb)
    apply (norm_curvature_le_of_raw_bound R (C := CB) ?_).trans (le_max_right _ _)
    intro l j k m
    rw [congrFun (congrFun (congrFun (congrFun hR l) j) k) m]
    have h0 := (pi_norm_le_iff_of_nonneg (zero_le_one.trans hCB)).mp hr l
    have h1 := (pi_norm_le_iff_of_nonneg (zero_le_one.trans hCB)).mp h0 j
    have h2 := (pi_norm_le_iff_of_nonneg (zero_le_one.trans hCB)).mp h1 k
    simpa only [Real.norm_eq_abs] using
      (pi_norm_le_iff_of_nonneg (zero_le_one.trans hCB)).mp h2 m

end PoincareMT.M34
