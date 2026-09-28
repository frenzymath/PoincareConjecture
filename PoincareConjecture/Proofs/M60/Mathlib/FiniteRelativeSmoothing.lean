import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M60

variable {E H F K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  [TopologicalSpace M] [ChartedSpace H M]
  [PseudoMetricSpace N] [ChartedSpace K N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}

theorem exists_c1_of_finite_relative_smoothing
    {ι : Type*} [Finite ι] (W : ι → Set M) (S : Set M) (f₀ : C(M, N))
    (hcover : ∀ x, ContMDiffAt I J 1 f₀ x ∨ ∃ i, x ∈ W i)
    {margin : ℝ} (hmargin : 0 < margin)
    (hstep : ∀ (i : ι) (f : C(M, N)),
      (∀ x, dist (f x) (f₀ x) < margin) → ∀ epsilon : ℝ, 0 < epsilon →
        ∃ g : C(M, N),
          (∀ x ∈ W i, ContMDiffAt I J 1 g x) ∧
          (∀ x, ContMDiffAt I J 1 f x → ContMDiffAt I J 1 g x) ∧
          EqOn g f S ∧ (∀ x, dist (g x) (f x) < epsilon)) :
    ∃ g : C(M, N), ContMDiff I J 1 g ∧ EqOn g f₀ S ∧
      ∀ x, dist (g x) (f₀ x) < margin := by
  classical
  let := Fintype.ofFinite ι
  have hfinite : ∀ A : Finset ι, ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ margin →
      ∃ g : C(M, N),
        (∀ i ∈ A, ∀ x ∈ W i, ContMDiffAt I J 1 g x) ∧
        (∀ x, ContMDiffAt I J 1 f₀ x → ContMDiffAt I J 1 g x) ∧
        EqOn g f₀ S ∧ (∀ x, dist (g x) (f₀ x) < epsilon) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro epsilon hepsilon _
      exact ⟨f₀, by simp, fun _ hx => hx, fun _ _ => rfl, fun _ => by simpa using hepsilon⟩
    | @insert i A _ ih =>
      intro epsilon hepsilon hemargin
      obtain ⟨f, hfsmooth, hfpreserve, hfS, hfclose⟩ :=
        ih (epsilon / 2) (half_pos hepsilon) (by linarith)
      obtain ⟨g, hgsmooth, hgpreserve, hgS, hgclose⟩ := hstep i f
        (fun x => (hfclose x).trans_le (by linarith)) (epsilon / 2) (half_pos hepsilon)
      refine ⟨g, ?_, (fun x hx => hgpreserve x (hfpreserve x hx)), hgS.trans hfS, ?_⟩
      · intro j hj x hx
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hgsmooth x hx
        · exact hgpreserve x (hfsmooth j hj x hx)
      · intro x
        exact (dist_triangle (g x) (f x) (f₀ x)).trans_lt
          ((add_lt_add (hgclose x) (hfclose x)).trans_eq (add_halves epsilon))
  obtain ⟨g, hgsmooth, hgpreserve, hgS, hgclose⟩ :=
    hfinite Finset.univ margin hmargin le_rfl
  refine ⟨g, ?_, hgS, hgclose⟩
  intro x
  rcases hcover x with hx | ⟨i, hi⟩
  · exact hgpreserve x hx
  · exact hgsmooth i (Finset.mem_univ i) x hi

end PoincareConjecture.M60
