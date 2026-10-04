import PoincareLib.Geometry.Manifold.SmoothDomain.Exhaustion
import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Kernel.Construction
import PoincareLib.Geometry.Riemannian.Measure.Exhaustion

/-!
# Dirichlet kernels on a smooth exhaustion

The retained metric supplies second countability. The smooth-domain exhaustion
and the Dirichlet kernel construction then give a pointwise monotone family of
nonnegative kernels on the entire ambient manifold, extended by zero.

This is the domain-construction step in Chow et al., Part III, Proposition
26.49, Step 1, printed pp. 378-381 (PDF pp. 399-402).
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.LeviCivitaData

/-- Smooth exhaustion domains and their monotone Dirichlet kernels are
constructed from the metric; no domain or kernel family is assumed. -/
theorem exists_dirichletHeatKernel_exhaustion
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    [PreconnectedSpace M] [NoncompactSpace M]
    {g : RiemannianMetric (n + 1) M} (D : LeviCivitaData g) :
    ∃ (Ω : ℕ → Set M) (_S : ∀ j, Poincare.Manifold.SmoothDomain (n + 1) (Ω j))
      (K : ℕ → ℝ → M → M → ℝ),
      (∀ j, closure (Ω j) ⊆ Ω (j + 1)) ∧ (⋃ j, Ω j) = univ ∧
      (∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j)) ∧
      (∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y)) := by
  classical
  let : SecondCountableTopology M := g.secondCountableTopology
  obtain ⟨Ω, hΩ, hnest, hcover⟩ :=
    Poincare.Manifold.exists_smoothDomain_exhaustion (n := n) (M := M)
  let S := fun j => (hΩ j).some
  obtain ⟨K, hK, hmono⟩ := Dirichlet.exists_dirichletHeatKernels D
  refine ⟨Ω, S, fun j => K (Ω j) (S j), hnest, hcover, fun j => hK _ _, ?_⟩
  have hΩmono : Monotone Ω := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hnest j)
  intro t ht x y i j hij
  change K (Ω i) (S i) t x y ≤ K (Ω j) (S j) t x y
  by_cases hx : x ∈ Ω i
  · by_cases hy : y ∈ Ω i
    · exact hmono _ _ _ _ (hΩmono hij) t ht x hx y hy
    · rw [(hK (Ω i) (S i)).zero_outside t ht x y (Or.inr hy)]
      exact (hK (Ω j) (S j)).nonneg t ht x y
  · rw [(hK (Ω i) (S i)).zero_outside t ht x y (Or.inl hx)]
    exact (hK (Ω j) (S j)).nonneg t ht x y

end PoincareMT.LeviCivitaData
