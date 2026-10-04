import PoincareLib.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Basic
import PoincareLib.Analysis.Parabolic.Dirichlet.SpectralSemigroup

/-!
# The spectral Dirichlet L2 heat semigroup

The Hilbert eigenbasis of the domain resolvent gives a self-adjoint,
contractive, strongly continuous semigroup. The compactness input is proved
by local Rellich and finite chart localization. Pointwise kernel
representation, boundary regularity and positivity require further analysis.

Reference: Chow et al., Part III, Theorem 24.30, Section 24.5.1, p. 290.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace NNReal

namespace PoincareMT.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

variable (D : LeviCivitaData g) (Ω : Set M) (hn : 0 < n)
  (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))

/-- The nonnegative spectral rates of the retained Dirichlet Laplacian. -/
def eigenvalueNN (i : EigenIndex D Ω) : ℝ≥0 :=
  ⟨eigenvalue D Ω i, eigenvalue_nonneg D Ω hn hΩ hc i⟩

/-- The spectral heat operator constructed from the domain and geometry. -/
def heatSemigroup (t : ℝ≥0) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] Lp ℝ 2 (g.volumeMeasure.restrict Ω) :=
  Poincare.Analysis.Dirichlet.Spectral.heat (eigenbasis D Ω hn hΩ hc)
    (eigenvalueNN D Ω hn hΩ hc) t

set_option backward.isDefEq.respectTransparency false in
theorem heatSemigroup_hasSum (t : ℝ≥0) (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    HasSum (fun i : EigenIndex D Ω =>
      (Real.exp (-eigenvalue D Ω i * (t : ℝ)) * (eigenbasis D Ω hn hΩ hc).repr f i) •
        eigenbasis D Ω hn hΩ hc i) (heatSemigroup D Ω hn hΩ hc t f) := by
  convert!
    Poincare.Analysis.Dirichlet.Spectral.heat_hasSum (eigenbasis D Ω hn hΩ hc)
      (eigenvalueNN D Ω hn hΩ hc) t f using 1

@[simp] theorem heatSemigroup_zero :
    heatSemigroup D Ω hn hΩ hc 0 = ContinuousLinearMap.id ℝ _ :=
  Poincare.Analysis.Dirichlet.Spectral.heat_zero _ _

theorem heatSemigroup_add (s t : ℝ≥0) :
    heatSemigroup D Ω hn hΩ hc (s + t) =
      (heatSemigroup D Ω hn hΩ hc s).comp (heatSemigroup D Ω hn hΩ hc t) :=
  Poincare.Analysis.Dirichlet.Spectral.heat_add _ _ _ _

theorem norm_heatSemigroup_le (t : ℝ≥0) : ‖heatSemigroup D Ω hn hΩ hc t‖ ≤ 1 :=
  Poincare.Analysis.Dirichlet.Spectral.norm_heat_le _ _ _

theorem heatSemigroup_isSelfAdjoint (t : ℝ≥0) :
    IsSelfAdjoint (heatSemigroup D Ω hn hΩ hc t) :=
  Poincare.Analysis.Dirichlet.Spectral.heat_isSelfAdjoint _ _ _

theorem continuous_heatSemigroup (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    Continuous (fun t : ℝ≥0 => heatSemigroup D Ω hn hΩ hc t f) :=
  Poincare.Analysis.Dirichlet.Spectral.continuous_heat _ _ _

end PoincareMT.LeviCivitaData.Dirichlet
