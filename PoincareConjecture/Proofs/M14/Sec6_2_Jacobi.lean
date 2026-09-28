import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGlobalPair
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiPackaging
import PoincareConjecture.Statements.M14PathCalculus

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)

theorem exists_jacobiField_unique
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (Y₀ P₀ : G.Horizontal (R.curve (Real.sqrt τ₁))) :
    ∃ Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval τ₁ τ₂),
      Q.field (Real.sqrt τ₁) = Y₀ ∧ M14JacobiFirstDerivative Q (Real.sqrt τ₁) = P₀ ∧
      (∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
        ∀ Z : G.Horizontal (R.curve s), M14JacobiResidual G R Q s Z = 0) ∧
      ∀ Q' : M14JacobiFieldData G R.curve (M14SqrtParameterInterval τ₁ τ₂),
        Q'.field (Real.sqrt τ₁) = Y₀ → M14JacobiFirstDerivative Q' (Real.sqrt τ₁) = P₀ →
        (∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
          ∀ Z : G.Horizontal (R.curve s), M14JacobiResidual G R Q' s Z = 0) →
        ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, Q'.field s = Q.field s := by
  obtain ⟨z, hz, hz₀⟩ := exists_horizontalJacobiPair R hM04 hM12 (Y₀, P₀)
  obtain ⟨Q, hfield, hderiv, hres⟩ := hz.exists_jacobiField
  have ha : Real.sqrt τ₁ ∈ M14SqrtParameterInterval τ₁ τ₂ :=
    ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩
  have hY₀ : Q.field (Real.sqrt τ₁) = Y₀ := by
    rw [hfield]
    exact congrArg Prod.fst hz₀
  have hP₀ : M14JacobiFirstDerivative Q (Real.sqrt τ₁) = P₀ :=
    (hderiv _ ha).trans (congrArg Prod.snd hz₀)
  refine ⟨Q, hY₀, hP₀, hres, ?_⟩
  intro Q' hY' hP' hres' s hs
  have heq := horizontalJacobiPair_unique R hM04 hM12
    (jacobiField_isHorizontalJacobiPair Q' hres') (jacobiField_isHorizontalJacobiPair Q hres)
    (Prod.ext (hY'.trans hY₀.symm) (hP'.trans hP₀.symm)) s hs
  exact congrArg Prod.fst heq

theorem jacobiStatement
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    M14JacobiStatement G := by
  intro T τ₁ τ₂ x y p R W E₀ heuler
  obtain ⟨Q, hzero, hW, hres, _⟩ := exists_jacobiField_unique R hM04 hM12 0 W
  exact ⟨Q, hzero, hW, hres⟩

theorem initialJacobiStatement
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n) :
    M14InitialJacobiStatement G := by
  intro T τ₁ τ₂ x y p R W E₀ heuler
  exact exists_jacobiField_unique R hM04 hM12 0 W

end PoincareConjecture.M14
