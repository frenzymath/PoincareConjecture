import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.AdaptedFields.AdaptedGlobal
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian.MetricBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual orthonormal frames along square-root paths

Initialize an orthonormal horizontal basis and apply actual adapted
transport to each vector. Metric conservation preserves its Gram
matrix; finite-dimensional linear independence makes it a basis at
every time. Morgan-Tian Lemma 6.36 and Proposition 6.43, pp. 122, 127-128.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_t2Space {q : G.Point} : T2Space (G.Horizontal q) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal q

attribute [local instance] horizontal_t2Space

/-- Every orthonormal family of n actual horizontal vectors is an
actual basis, including dimension zero, Proposition 6.43, pp. 127-128. -/
theorem horizontalBasis_of_orthonormal (q : G.Point) (v : Fin n → G.Horizontal q)
    (hv : ∀ i j, G.spacetime.horizontalMetric.inner q (v i) (v j) = if i = j then 1 else 0) :
    ∃ b : Module.Basis (Fin n) ℝ (G.Horizontal q), ∀ i, b i = v i := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (G.Horizontal q) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal q
  have ho : Orthonormal ℝ v := orthonormal_iff_ite.mpr hv
  have hdim : Fintype.card (Fin n) = Module.finrank ℝ (G.Horizontal q) := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal q]
    simp
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v ho.linearIndependent hdim, ?_⟩
  intro i
  exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' v ho.linearIndependent hdim) i

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)

/-- A smooth actual unit-adapted orthonormal frame exists on the full
closed square interval and is a basis at every time, Lemma 6.36 and
Proposition 6.43, pp. 122, 127-128. -/
theorem exists_horizontalUnitAdaptedFrame
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    ∃ P : Fin n → ∀ s, G.Horizontal (R.curve s),
      (∀ i, IsHorizontalUnitAdaptedFieldOn R (Real.sqrt τ₁) (Real.sqrt τ₂) (P i)) ∧
      (∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, ∀ i j,
        G.spacetime.horizontalMetric.inner (R.curve s) (P i s) (P j s) =
          if i = j then 1 else 0) ∧
      ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
        ∃ b : Module.Basis (Fin n) ℝ (G.Horizontal (R.curve s)), ∀ i, b i = P i s := by
  classical
  obtain ⟨b₀, hb₀⟩ := exists_orthonormal_horizontalBasis G (R.curve (Real.sqrt τ₁))
  choose P hP hP₀ using fun i => exists_horizontalUnitAdaptedField R hM04 hM12 (b₀ i)
  have hpair (s : ℝ) (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) (i j : Fin n) :
      G.spacetime.horizontalMetric.inner (R.curve s) (P i s) (P j s) =
        if i = j then 1 else 0 := by
    rw [horizontalUnitAdapted_pair_eq hM12 (hP i) (hP j)
      (left_mem_Icc.mpr (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt).le) hs, hP₀ i, hP₀ j]
    exact hb₀ i j
  exact ⟨P, hP, hpair, fun s hs => horizontalBasis_of_orthonormal (R.curve s)
    (fun i => P i s) (hpair s hs)⟩

end PoincareMT.M14
