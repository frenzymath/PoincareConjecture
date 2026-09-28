import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckFrontierSphere

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

theorem exists_frontier_entry_below_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M]
        (g : RiemannianMetric 3 M) (_D : LeviCivitaData g)
        (N W : EpsilonNeck g),
        N.epsilon = W.epsilon → N.epsilon ≤ epsilon₀ →
        ∀ (γ : ℝ → M) (s c : ℝ), s < c →
          ContinuousOn γ (Icc s c) → γ s = N.center → γ c = W.center →
          MapsTo γ (Ico s c) N.carrier → W.center ∈ frontier N.carrier →
          ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
            ∃ v ∈ Ioo s c,
              sigma * (N.coordinate_inverse (γ v)).2 =
                509 * N.epsilon⁻¹ / 512 ∧
              (∀ t ∈ Ioo v c,
                509 * N.epsilon⁻¹ / 512 <
                  sigma * (N.coordinate_inverse (γ t)).2) ∧
              ∃ f : UnitTwoSphere → ℝ,
                ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
                (∀ p, |f p| < 7 * W.epsilon⁻¹ / 8) ∧
                range (fun p : UnitTwoSphere =>
                  N.coordinate_map (p, sigma * (255 * N.epsilon⁻¹ / 256))) =
                  range (fun p : UnitTwoSphere => W.coordinate_map (p, f p)) ∧
                ∃ kappa : ℝ, (kappa = 1 ∨ kappa = -1) ∧
                  MapsTo γ (Icc v c) W.carrier ∧
                  kappa * neckGraphHeight W f (γ v) < 0 ∧
                  0 < kappa * neckGraphHeight W f (γ c) := by
  obtain ⟨epsilon₀, hpos, hsmall, hfront⟩ :=
    exists_frontier_neck_sphere_sides_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D N W heq hN γ s c hsc hγ hγs hγc hinside hfrontier
  obtain ⟨sigma, hsigma, v, hv, hvlevel, hvafter, _hclose127, _hclose255,
      _hcap, _phi, _hphi, f, hf, hbuffer, _hpoint, hrange, _hiso, _hiso',
      _hcontinuous, _hzero, _hminus, _hplus, _hdisjoint, _hunion, kappa,
      hkappa, _hcenter, _halign, hγW, hvneg, hcpos, _hcross⟩ :=
    hfront M g D N W heq hN γ s c hsc hγ hγs hγc hinside hfrontier
  refine ⟨sigma, hsigma, v, hv, hvlevel, hvafter, f, hf, hbuffer, hrange,
    kappa, hkappa, hγW, hvneg, hcpos⟩

end PoincareConjecture.M28
