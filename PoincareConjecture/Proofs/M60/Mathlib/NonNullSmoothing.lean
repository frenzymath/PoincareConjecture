import PoincareConjecture.Proofs.M60.Mathlib.NonNullSmoothingChart
import PoincareConjecture.Proofs.M40.Mathlib.SmoothingCharts
import Mathlib.Geometry.Manifold.Metrizable









set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M60




theorem exists_smooth_homotopic_of_compact
    {E F M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [MetricSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    (f₀ : C(M, N)) :
    ∃ g : C(M, N), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g ∧ g.Homotopic f₀ := by
  classical
  obtain ⟨n, c, rho, margin, hmargin, hsupp, hrho, hcover, hvalid⟩ :=
    M40.exists_finite_smoothing_charts (E := E) (F := F) f₀
  let W : Fin n → Set M := fun i => {x | (rho i : M → ℝ) =ᶠ[𝓝 x] 1}
  have hstep (i : Fin n) (f : C(M, N))
      (hclose : ∀ x, dist (f x) (f₀ x) < margin)
      (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      ∃ g : C(M, N),
        (∀ x ∈ W i, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g x) ∧
        (∀ x, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x →
          ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g x) ∧
        g.Homotopic f ∧ ∀ x, dist (g x) (f x) < epsilon := by
    apply exists_homotopic_chart_smoothing (chartAt E (c i)) (chartAt F (f₀ (c i)))
      contMDiffOn_chart contMDiffOn_chart contMDiffOn_chart_symm
      (rho i) (hrho i) (fun _ => (rho i).mem_Icc) (isClosed_tsupport _).isCompact
      (hsupp i) f ?_ hepsilon
    exact hvalid f (fun x => by
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff hmargin).mpr (hclose x)) i
  have hfinite : ∀ A : Finset (Fin n), ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ margin →
      ∃ g : C(M, N),
        (∀ i ∈ A, ∀ x ∈ W i, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g x) ∧
        g.Homotopic f₀ ∧ ∀ x, dist (g x) (f₀ x) < epsilon := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro epsilon hepsilon _
      exact ⟨f₀, by simp, .refl f₀, fun _ => by simpa using hepsilon⟩
    | @insert i A _ ih =>
      intro epsilon hepsilon hemargin
      obtain ⟨f, hfsmooth, hfhom, hfclose⟩ :=
        ih (epsilon / 2) (half_pos hepsilon) (by linarith)
      obtain ⟨g, hgsmooth, hgpreserve, hghom, hgclose⟩ := hstep i f
        (fun x => (hfclose x).trans_le (by linarith)) (epsilon / 2) (half_pos hepsilon)
      refine ⟨g, ?_, hghom.trans hfhom, ?_⟩
      · intro j hj x hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hgsmooth x hx
        · exact hgpreserve x (hfsmooth j hj x hx)
      · intro x
        exact (dist_triangle (g x) (f x) (f₀ x)).trans_lt
          ((add_lt_add (hgclose x) (hfclose x)).trans_eq (add_halves epsilon))
  obtain ⟨g, hg, hhom, _⟩ := hfinite Finset.univ margin hmargin le_rfl
  refine ⟨g, ?_, hhom⟩
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact hg i (Finset.mem_univ i) x hi

end PoincareConjecture.M60
