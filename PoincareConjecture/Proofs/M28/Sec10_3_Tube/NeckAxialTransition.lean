import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckBalancedScale
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckRicciComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.ProjectionDerivative

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

open Proofs.M28.NeckLengthComparison

private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)

private theorem axial_component_bounds {s t Y G R a : ℝ}
    (hs : 0 < s) (ht : 0 < t)
    (hscaleLower : (999 / 1000 : ℝ) * t < s)
    (hscaleUpper : s < (1001 / 1000 : ℝ) * t)
    (haxis : a ^ 2 ≤ Y)
    (hGlo : (999 / 1000 : ℝ) * s ^ 2 ≤ G)
    (hGhi : G ≤ (1001 / 1000 : ℝ) * s ^ 2)
    (hYlo : (999 / 1000 : ℝ) * t ^ 2 * Y ≤ G)
    (hYhi : G ≤ (1001 / 1000 : ℝ) * t ^ 2 * Y)
    (hRhi : R ≤ (1 / 100 : ℝ))
    (hRlo : (49 / 100 : ℝ) * Y - (1 / 2 : ℝ) * a ^ 2 ≤ R) :
    (9 / 10 : ℝ) < |a| ∧ |a| < (11 / 10 : ℝ) := by
  have hsLower : (999 / 1000 : ℝ) ^ 2 * t ^ 2 < s ^ 2 := by
    nlinarith only [hs, ht, hscaleLower]
  have hsUpper : s ^ 2 < (1001 / 1000 : ℝ) ^ 2 * t ^ 2 := by
    nlinarith only [hs, ht, hscaleUpper]
  have hYlower : (99 / 100 : ℝ) < Y := by
    by_contra h
    have hbad : t ^ 2 * Y ≤ t ^ 2 * (99 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left (le_of_not_gt h) (sq_nonneg t)
    nlinarith only [hbad, hsLower, hGlo, hYhi, sq_pos_of_pos ht]
  have hYupper : Y < (101 / 100 : ℝ) := by
    by_contra h
    have hbad : t ^ 2 * (101 / 100 : ℝ) ≤ t ^ 2 * Y :=
      mul_le_mul_of_nonneg_left (le_of_not_gt h) (sq_nonneg t)
    nlinarith only [hbad, hsUpper, hGhi, hYlo, sq_pos_of_pos ht]
  constructor
  · nlinarith only [hYlower, hRlo, hRhi, sq_abs a, abs_nonneg a]
  · nlinarith only [hYupper, haxis, sq_abs a, abs_nonneg a]

theorem exists_neck_axial_transition_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N N' : EpsilonNeck g), N.epsilon ≤ epsilon₀ → N'.epsilon ≤ epsilon₀ →
        ∀ z ∈ N.cylinderDomain, N.coordinate_map z ∈ N'.carrier →
          let w := mfderiv CI (𝓡 3) N.coordinate_map z (0, 1)
          let v := mfderiv (𝓡 3) CI N'.coordinate_inverse (N.coordinate_map z) w
          (9 / 10 : ℝ) < |v.2| ∧ |v.2| < (11 / 10 : ℝ) := by
  obtain ⟨epsilonS, hSpos, hSsmall, hscales⟩ := exists_neck_balanced_scale_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hricci⟩ := tube.exists_neck_ricci_accuracy.{u}
  let epsilon₀ := min epsilonS (min epsilonR (1 / 1000))
  refine ⟨epsilon₀, lt_min hSpos (lt_min hRpos (by norm_num)),
    (min_le_left _ _).trans hSsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D N N' hN hN' z hz hx
  let x := N.coordinate_map z
  let w := mfderiv CI (𝓡 3) N.coordinate_map z (0, 1)
  let z' := N'.coordinate_inverse x
  let v := mfderiv (𝓡 3) CI N'.coordinate_inverse x w
  let Y := EvolvingRoundCylinderMetric 0 z' v v
  let G := g.inner x w w
  let R := D.ricci x w w
  have hz' : z' ∈ N'.cylinderDomain := N'.coordinate_inverse_mem x hx
  have hmap : mfderiv CI (𝓡 3) N'.coordinate_map z' v = w :=
    N'.coordinate_map_mfderiv_inverse_prod hx w
  have hxmap : N'.coordinate_map z' = x := N'.coordinate_map_coordinate_inverse hx
  have hmodel : EvolvingRoundCylinderMetric 0 z (0, 1) (0, 1) = 1 := by
    change RoundCylinderMetric z (0, 1) (0, 1) = 1
    rw [roundCylinderMetric_self_eq]
    norm_num
  have haxis : v.2 ^ 2 ≤ Y := by
    change v.2 ^ 2 ≤ RoundCylinderMetric z' v v
    rw [roundCylinderMetric_self_eq]
    nlinarith only [sq_nonneg ‖v.1‖]
  have hY : 0 ≤ Y := (sq_nonneg v.2).trans haxis
  have hmetN := N.pullback_metric_bounds hz.2 (0, 1)
  have hmetN' := N'.pullback_metric_bounds hz'.2 v
  change (1 - N.epsilon) * N.scale ^ 2 *
      EvolvingRoundCylinderMetric 0 z (0, 1) (0, 1) ≤ G ∧
    G ≤ (1 + N.epsilon) * N.scale ^ 2 *
      EvolvingRoundCylinderMetric 0 z (0, 1) (0, 1) at hmetN
  rw [hmodel, mul_one, mul_one] at hmetN
  change (1 - N'.epsilon) * N'.scale ^ 2 * Y ≤
      g.inner (N'.coordinate_map z')
        (mfderiv CI (𝓡 3) N'.coordinate_map z' v)
        (mfderiv CI (𝓡 3) N'.coordinate_map z' v) ∧
    g.inner (N'.coordinate_map z')
        (mfderiv CI (𝓡 3) N'.coordinate_map z' v)
        (mfderiv CI (𝓡 3) N'.coordinate_map z' v) ≤
      (1 + N'.epsilon) * N'.scale ^ 2 * Y at hmetN'
  rw [hmap, hxmap] at hmetN'
  have hRN := hricci M g D N
    ((hN.trans (min_le_right _ _)).trans (min_le_left _ _)) z hz (0, 1)
  have hRN' := hricci M g D N'
    ((hN'.trans (min_le_right _ _)).trans (min_le_left _ _)) z' hz' v
  rw [hmap, hxmap] at hRN'
  have hRhi : R ≤ (1 / 100 : ℝ) := by
    change |R - (1 / 2 : ℝ) *
      (EvolvingRoundCylinderMetric 0 z (0, 1) (0, 1) - (1 : ℝ) ^ 2)| ≤
        (1 / 100 : ℝ) * EvolvingRoundCylinderMetric 0 z (0, 1) (0, 1) at hRN
    rw [hmodel] at hRN
    norm_num at hRN
    exact (le_abs_self R).trans hRN
  have hRlo : (49 / 100 : ℝ) * Y - (1 / 2 : ℝ) * v.2 ^ 2 ≤ R := by
    change |R - (1 / 2 : ℝ) * (Y - v.2 ^ 2)| ≤ (1 / 100 : ℝ) * Y at hRN'
    linarith only [(abs_le.mp hRN').1]
  obtain ⟨hslo, hshi⟩ := hscales M g D N N'
    (hN.trans (min_le_left _ _)) (hN'.trans (min_le_left _ _))
    ⟨x, N.coordinate_map_mem hz, hx⟩
  have heps := (hN.trans (min_le_right _ _)).trans (min_le_right _ _)
  have heps' := (hN'.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hsq := sq_nonneg N.scale
  have hsqY := mul_nonneg (sq_nonneg N'.scale) hY
  apply axial_component_bounds N.scale_pos N'.scale_pos hslo hshi haxis
    (G := G) (R := R) _ _ _ _ hRhi hRlo
  · nlinarith only [hmetN.1, mul_nonneg (sub_nonneg.mpr heps) hsq]
  · nlinarith only [hmetN.2, mul_nonneg (sub_nonneg.mpr heps) hsq]
  · nlinarith only [hmetN'.1, mul_nonneg (sub_nonneg.mpr heps') hsqY]
  · nlinarith only [hmetN'.2, mul_nonneg (sub_nonneg.mpr heps') hsqY]

end PoincareConjecture.M28
