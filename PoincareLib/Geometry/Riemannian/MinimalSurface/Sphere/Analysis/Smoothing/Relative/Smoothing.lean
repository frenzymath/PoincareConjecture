import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Smoothing.Relative.ChartSmoothing
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Smoothing.FiniteRelative.Smoothing
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Smoothing.FiniteRelative.Charts

/-!
# Relative C1 smoothing on a compact region

Morgan-Tian Definition 18.17, printed p. 430. A continuous map from a
finite-dimensional vector space, already C1 outside a compact set, can
be made C1 everywhere by changes supported in any open neighborhood of
that set. This supplies the relative smoothing needed for null loop
extensions while keeping their boundary values exactly fixed.
-/

set_option autoImplicit false

open Set Function Filter
open scoped Topology Manifold ContDiff

namespace PoincareMT.M60

/-- A continuous map that is C1 outside a compact set has a C1 replacement
equal to it outside any chosen open neighborhood. Source: MT Definition
18.17, p. 430, relative disk-smoothing derivation. -/
theorem exists_c1_eqOn_compl_of_compact
    {E F N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MetricSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    (f₀ : C(E, N)) {K O : Set E} (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hf : ∀ x, x ∉ K → ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 f₀ x) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) 1 g ∧ EqOn g f₀ Oᶜ := by
  obtain ⟨n, c, rho, margin, hmargin, hrho, hrho01, hcompact, hsupport, hcover, hvalid⟩ :=
    exists_finite_relative_charts (F := F) f₀ hK hO hKO
  let W : Fin n → Set E := fun i => {x | rho i =ᶠ[𝓝 x] 1}
  have hW (x : E) : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) 1 f₀ x ∨ ∃ i, x ∈ W i := by
    by_cases hx : x ∈ K
    · exact Or.inr (hcover x hx)
    · exact Or.inl (hf x hx)
  obtain ⟨g, hg, hEq, -⟩ := exists_c1_of_finite_relative_smoothing W Oᶜ f₀ hW hmargin (by
    intro i f hclose epsilon hepsilon
    obtain ⟨g, hgclose, hgfixed, hgpreserve, hgnew⟩ :=
      exists_relative_chart_smoothing (chartAt F (c i)) contMDiffOn_chart
        contMDiffOn_chart_symm (rho i) (hrho i) (hrho01 i) (hcompact i)
        f (hvalid f hclose i) hepsilon
    refine ⟨g, (fun x hx => (hgnew x hx).of_le (by simp)), hgpreserve, ?_, hgclose⟩
    intro x hx
    exact hgfixed x (fun hxs => hx (hsupport i hxs)))
  exact ⟨g, hg, hEq⟩

end PoincareMT.M60
