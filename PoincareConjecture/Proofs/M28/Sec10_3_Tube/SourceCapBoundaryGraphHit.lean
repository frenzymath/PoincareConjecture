import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSphereProjection
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckMinimizerTraversal

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_cap_boundary_minimizer_hit_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (K : CapCertificate g) (W : EpsilonNeck g),
        K.epsilon ≤ epsilon₀ → W.epsilon ≤ epsilon₀ →
        ∀ U : Set M, W.carrier ⊆ U →
        ∀ {γ : ℝ → M} {a b t : ℝ}, a < t → t < b →
          ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b) →
          MapsTo γ (Icc a b) U →
          g.pathELength γ a b = intrinsicEDist g U (γ a) (γ b) →
          γ t = W.center → γ a ∉ W.carrier → γ b ∉ W.carrier →
          ∀ z ∈ K.boundary_sphere, z ∈ W.carrier →
            |(W.coordinate_inverse z).2| ≤ 3 * W.epsilon⁻¹ / 4 →
            ∃ v ∈ Ioo a b, γ v ∈ K.boundary_sphere := by
  obtain ⟨epsilonG, hGpos, _, hgraph⟩ := exists_buffered_neck_sphere_graph_accuracy.{u}
  refine ⟨min epsilonG (1 / 1000), lt_min hGpos (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g D K W hK hW U hWU γ a b t hat htb
    hγ hγU hmin hcenter haout hbout z hzboundary hzW haxis
  have hboundary : K.boundary_sphere =
      range (fun p : UnitTwoSphere => K.boundary_neck.coordinate_map (p, 0)) := by
    rw [K.boundary_eq_neck_sphere, K.boundary_neck.central_sphere_eq]
    ext y
    constructor
    · rintro ⟨⟨p, s⟩, ⟨_, hs⟩, hpoint⟩
      have hs0 : s = 0 := mem_singleton_iff.mp hs
      subst s
      exact ⟨p, hpoint⟩
    · rintro ⟨p, rfl⟩
      exact ⟨(p, 0), ⟨mem_univ _, mem_singleton _⟩, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : UnitTwoSphere,
      K.boundary_neck.coordinate_map (q, 0) = z := by
    rw [hboundary] at hzboundary
    exact hzboundary
  have hKgraph : K.boundary_neck.epsilon ≤ epsilonG := by
    rw [K.boundary_neck_epsilon]
    exact hK.trans (min_le_left _ _)
  have hzero : (0 : ℝ) ∈ Ioo (-K.boundary_neck.epsilon⁻¹)
      K.boundary_neck.epsilon⁻¹ := by
    have hpos := inv_pos.mpr K.boundary_neck.epsilon_pos
    exact ⟨neg_lt_zero.mpr hpos, hpos⟩
  have hqW : K.boundary_neck.coordinate_map (q, 0) ∈ W.carrier := by
    simpa only [hq] using hzW
  have hqaxis : |(W.coordinate_inverse (K.boundary_neck.coordinate_map (q, 0))).2| ≤
      3 * W.epsilon⁻¹ / 4 := by
    simpa only [hq] using haxis
  obtain ⟨_, _, f, hf, hfb, _, hrange⟩ := hgraph M g D W K.boundary_neck
    (hW.trans (min_le_left _ _)) hKgraph 0 hzero q hqW hqaxis
  obtain ⟨v, hv, hvgraph⟩ := exists_neck_minimizer_graph_crossing W
    (hW.trans (min_le_right _ _)) hWU hat htb hγ hγU hmin
    hcenter haout hbout hf hfb
  refine ⟨v, hv, ?_⟩
  rw [hboundary, hrange]
  exact hvgraph

end PoincareConjecture.M28
