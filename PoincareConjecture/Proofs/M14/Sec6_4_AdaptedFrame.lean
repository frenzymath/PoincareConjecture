import PoincareConjecture.Proofs.M14.Sec6_4_AdaptedGlobal
import PoincareConjecture.Proofs.M14.Sec6_7_MetricBases
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_t2Space {q : G.Point} : T2Space (G.Horizontal q) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal q

attribute [local instance] horizontal_t2Space



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

end PoincareConjecture.M14
