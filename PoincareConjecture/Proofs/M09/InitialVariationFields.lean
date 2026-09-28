import PoincareConjecture.Proofs.M09.InitialVectorVariation
import PoincareConjecture.Proofs.M09.FamilySlices
import PoincareConjecture.Proofs.M09.VelocityChainRules









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

@[simp] theorem initialVectorVariation_baseSquareCurve (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    (initialVectorVariation A Z W b hb hmax).toLVariation.baseSquareCurve =
      A.squareFamily Z := by
  funext s
  simp only [LVariation.baseSquareCurve, initialVectorVariation_squareFamily, zero_smul, add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem initialVectorVariation_squareField_zero (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    (squareVariationField (initialVectorVariation A Z W b hb hmax).toLVariation 0 :
      EuclideanSpace ℝ (Fin n)) = 0 := by
  have heq : (fun u : ℝ ↦ A.squareFamily (Z + u • W) 0) = fun _ : ℝ ↦ p :=
    funext fun u ↦ A.square_at_zero (Z + u • W)
  have hvelocity := congrArg (fun α : ℝ → M ↦
    (curveVelocity (n := n) α 0 : EuclideanSpace ℝ (Fin n))) heq
  exact hvelocity.trans (by simp [curveVelocity])

set_option backward.isDefEq.respectTransparency false in
theorem initialVectorVariation_squareField_terminal (A : LExponentialFamily F T τmax p)
    (Z W : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    (squareVariationField (initialVectorVariation A Z W b hb hmax).toLVariation
        (Real.sqrt b) : EuclideanSpace ℝ (Fin n)) = A.sliceDifferential Z b W := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  have heq : (fun u : ℝ ↦ A.squareFamily (Z + u • W) (Real.sqrt b)) =
      (fun u : ℝ ↦ A.gamma (Z + u • W) b) := by
    funext u
    simpa only [Real.sq_sqrt hb.le] using A.square_agrees (Z + u • W) (Real.sqrt b)
      ⟨Real.sqrt_nonneg b, Real.sqrt_lt_sqrt hb.le hmax⟩
  have hvelocity := congrArg (fun α : ℝ → M ↦
    (curveVelocity (n := n) α 0 : EuclideanSpace ℝ (Fin n))) heq
  have hdiff := (lExponentialFamily_initialSlice_contMDiffAt A Z b hb hmax).mdifferentiableAt
    (by simp)
  have hchain := curveVelocity_comp_initial_line (fun V ↦ A.gamma V b) Z W hdiff
  exact hvelocity.trans hchain

end PoincareConjecture.Proofs.M09
