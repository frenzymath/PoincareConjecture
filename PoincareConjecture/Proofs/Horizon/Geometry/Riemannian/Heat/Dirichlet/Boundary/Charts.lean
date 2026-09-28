import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.Cutoffs







set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.SmoothDomain

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {Ω : Set M}


theorem exists_flattening_parametrization_cutoff (S : SmoothDomain n Ω) (x : closure Ω) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) (χ : M → ℝ),
      (x : M) ∈ e.target ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      (∀ z ∈ e.source,
        (e z ∈ closure Ω ↔ 0 ≤ z 0) ∧
        (e z ∈ Ω ↔ 0 < z 0) ∧
        (e z ∈ frontier Ω ↔ z 0 = 0)) ∧
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ e.target ∧
      (∀ y, χ y ∈ Icc (0 : ℝ) 1) ∧
      χ =ᶠ[𝓝 (x : M)] 1 := by
  obtain ⟨e, hx, he, hei, hflat⟩ := S.exists_flattening_parametrization x
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) (x : M)).mem_iff.mp
    (e.open_target.mem_nhds hx)
  exact ⟨e, χ, hx, he, hei, hflat, χ.contMDiff, χ.hasCompactSupport,
    hχ, fun y => χ.mem_Icc, χ.eventuallyEq_one⟩

end Poincare.Manifold.SmoothDomain
