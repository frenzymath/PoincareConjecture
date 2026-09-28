import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Acceleration.Hessian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Acceleration.AlongGeodesic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Threshold

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

theorem long_neck_geodesics_are_almost_axial {α : ℝ} (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}
        (N : EpsilonNeck g),
        N.epsilon ≤ ε₀ → ∀ {γ : ℝ → M} {L : ℝ},
        N.scale / (100 * N.epsilon) < L →
        g.IsGeodesicOn γ (Icc 0 L) →
        (∀ t ∈ Icc 0 L, γ t ∈ N.carrier) →
        (∀ t ∈ Icc 0 L,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1) →
        (∀ a ∈ Icc (0 : ℝ) L, ∀ b ∈ Icc (0 : ℝ) L,
          a ≤ b → ENNReal.ofReal (b - a) ≤
            intrinsicEDist g N.carrier (γ a) (γ b)) →
        (N.coordinate_inverse (γ 0)).2 < (N.coordinate_inverse (γ L)).2 →
        ∀ t ∈ Icc 0 L,
        let a : TangentSpace (𝓡 3) (γ t) := N.scale⁻¹ •
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
            N.coordinate_map (N.coordinate_inverse (γ t)) (0, 1)
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1 - a) < α := by
  obtain ⟨K, hK⟩ := exists_axial_hessian_bound.{u}
  let C := Real.sqrt 2 * (Real.pi + 1)
  obtain ⟨β, ε₀, _, hε₀, _, hwindow⟩ :=
    exists_axial_alignment_window_threshold K C (half_pos hα)
  refine ⟨ε₀, hε₀, ?_⟩
  intro M _ _ _ _ _ _ _ g N hN γ L hL hγ hcarrier hunit hsegment horient t ht
  let f := N.axialCoordinate ∘ γ
  let acc := fun t => N.connection.hessian N.axialCoordinate (γ t)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
  have hf (t : ℝ) (ht : t ∈ Icc 0 L) : HasDerivAt f (deriv f t) t :=
    (N.hasDerivAt_axialCoordinate_comp_geodesic hγ hcarrier ht).differentiableAt.hasDerivAt
  have hv (t : ℝ) (ht : t ∈ Icc 0 L) : HasDerivAt (deriv f) (acc t) t :=
    hasDerivAt_deriv_axialCoordinate_comp_geodesic N.connection N hγ hcarrier ht
  have hacc (t : ℝ) (ht : t ∈ Icc 0 L) : |acc t| ≤ K * N.epsilon / N.scale ^ 2 :=
    hK N (hcarrier t ht) _ (hunit t ht)
  have hc (a : ℝ) (ha : a ∈ Icc 0 L) (b : ℝ) (hb : b ∈ Icc 0 L) (_ : a ≤ b) :
      intrinsicEDist g N.carrier (γ a) (γ b) ≤
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * (|f b - f a| + C)) :=
    N.intrinsicEDist_le_axial_add (hcarrier a ha) (hcarrier b hb)
  have h := hwindow N.epsilon N.epsilon_pos hN N.scale N.scale_pos
  have hvel := N.long_neck_axial_speed_of_intrinsic_minimality hL h.1 h.2.1
    hf hv hacc (show 0 ≤ C by dsimp [C]; positivity) hsegment hc horient t ht
  rw [(N.hasDerivAt_axialCoordinate_comp_geodesic hγ hcarrier ht).deriv] at hvel
  exact (N.tangentNorm_sub_scaled_axial_le_of_velocity (hcarrier t ht)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) (hunit t ht) (half_pos hα).le hvel
    h.2.2.le).trans_lt (half_lt_self hα)

end PoincareConjecture.EpsilonNeck
