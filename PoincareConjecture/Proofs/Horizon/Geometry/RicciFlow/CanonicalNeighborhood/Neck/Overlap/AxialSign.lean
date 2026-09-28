import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.AxialMonotonicity












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_transition_axis_signed_deriv_bounds :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon ≤ ε₀ →
        ∀ (q : UnitTwoSphere) (S : Set ℝ), IsPreconnected S →
        S ⊆ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ →
        (∀ s ∈ S, P.coordinate_map (q, s) ∈ N.carrier) →
          let f := fun t : ℝ => (N.coordinate_inverse (P.coordinate_map (q, t))).2
          ∀ a ∈ S, ∀ b ∈ S, a < b → ∀ σ : ℝ,
            (σ = 1 ∨ σ = -1) → 0 < σ * (f b - f a) →
            ∀ s ∈ S, (0.9 : ℝ) ≤ σ * deriv f s ∧ σ * deriv f s ≤ (1.1 : ℝ) := by
  obtain ⟨ε₀, hε₀, hsmall, hbounds⟩ := exists_transition_axis_deriv_bounds.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hN hP q S hS hdom hcarrier
  let f := fun t : ℝ => (N.coordinate_inverse (P.coordinate_map (q, t))).2
  dsimp only
  intro a ha b hb hab σ hσ hseed
  have hsmooth (s : ℝ) (hs : s ∈ S) : ContDiffAt ℝ ∞ f s :=
    N.transition_axis_contDiffAt P q (hdom hs) (hcarrier s hs)
  have hcont : ContinuousOn f S :=
    fun s hs => (hsmooth s hs).continuousAt.continuousWithinAt
  have hcont' : ContinuousOn (deriv f) S := by
    intro s hs
    exact ((hsmooth s hs).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hderiv (s : ℝ) (hs : s ∈ S) :
      (0.9 : ℝ) ≤ |deriv f s| ∧ |deriv f s| ≤ (1.1 : ℝ) :=
    hbounds N P hN hP q (hdom hs) (hcarrier s hs)
  have hne (s : ℝ) (hs : s ∈ S) : deriv f s ≠ 0 := by
    intro heq
    have h := (hderiv s hs).1
    rw [heq, abs_zero] at h
    norm_num at h
  rcases hS.mapsTo_Ioi_or_Iio hcont' hne with hpos | hneg
  · have hmono := strictMonoOn_of_deriv_pos hS.ordConnected.convex hcont
      (fun s hs => hpos (interior_subset hs))
    rcases hσ with rfl | rfl
    · intro s hs
      have hp : 0 < deriv f s := hpos hs
      simpa only [one_mul, abs_of_pos hp] using hderiv s hs
    · have h := hmono ha hb hab
      simp only [neg_one_mul] at hseed
      linarith
  · have hanti := strictAntiOn_of_deriv_neg hS.ordConnected.convex hcont
      (fun s hs => hneg (interior_subset hs))
    rcases hσ with rfl | rfl
    · have h := hanti ha hb hab
      simp only [one_mul] at hseed
      linarith
    · intro s hs
      have hn : deriv f s < 0 := hneg hs
      simpa only [neg_one_mul, abs_of_neg hn] using hderiv s hs

end PoincareConjecture.EpsilonNeck
