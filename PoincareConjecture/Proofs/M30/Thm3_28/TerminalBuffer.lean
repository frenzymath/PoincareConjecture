import PoincareConjecture.Proofs.M30.Thm3_28.FiniteCylinder
import PoincareConjecture.Proofs.M30.Thm3_28.CompactBuffer

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

theorem exists_uniform_curvatureDerivativeNorm_bound_on_terminal_buffer
    (hShi : LocalCurvatureDerivativeEstimates.{u}) (n m : ℕ) (B T A R : ℝ)
    (hT : 0 < T) (hA : 0 < A) (hAR : A < R) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ (g : RiemannianMetric n M) (p : M) (U : TopologicalSpace.Opens M),
        (U : Set M) = g.ball p R →
      ∀ (G : RicciFlow n U (Icc (-T) 0)),
        (∀ (x : U) (v w : TangentSpace (𝓡 n) x),
          (G.metric 0).inner x v w = g.inner x.val
            (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x v)
            (mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → M) x w)) →
        (∀ s ∈ Icc (-T) 0, ∀ y : U, (G.connection s).curvatureTensorNorm y ≤ B) →
        IsCompact (closure (g.ball p ((A + R) / 2))) →
        ∀ s ∈ Icc (-(T / 2)) 0, ∀ x : U, x.val ∈ g.ball p A →
          (G.connection s).curvatureDerivativeNorm m x ≤ D := by
  let r : ℝ := (R - A) / (2 * Real.exp ((n : ℝ) ^ 3 * max B 1 * T))
  have hr : 0 < r := div_pos (sub_pos.mpr hAR) (by positivity)
  obtain ⟨D, hD, hbound⟩ :=
    exists_uniform_curvatureDerivativeNorm_bound_on_buffered_cylinders
      hShi n m B T r (T / 2) hT hr (half_pos hT)
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ _ _ g p U hU G hmetric hcurv hcompact
  let V : Set U := (Subtype.val : U → M) ⁻¹' g.ball p A
  have hprecompact (x : U) (hx : x ∈ V) :
      IsCompact (closure ((G.metric (-T)).ball x r)) :=
    isCompact_closure_initial_ball_of_terminal_buffer g p U hT hA hAR hU
      G hmetric hcurv hcompact x hx
  intro s hs x hx
  exact hbound U G V hprecompact hcurv s
    ⟨by linarith [hs.1], hs.2⟩ x hx

end PoincareConjecture.M30
