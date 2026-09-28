import PoincareConjecture.Proofs.M09.ExponentialActionTime



set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem lExponentialFamily_normalizedAction_hasDerivAt {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hwindow : Set.Icc (T - τmax) T ⊆ J) {p : M}
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    HasDerivAt (fun t ↦ A.action Z t / (2 * Real.sqrt t))
      (((F.connection (T - b)).scalarCurvature (A.gamma Z b) +
          (F.metric (T - b)).inner (A.gamma Z b)
            (curveVelocity (A.gamma Z) b) (curveVelocity (A.gamma Z) b)) / 2 -
        (A.action Z b / (2 * Real.sqrt b)) / (2 * b)) b := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have h := (lExponentialFamily_action_hasDerivAt hM04 hwindow A Z b hb hmax).div
    ((Real.hasDerivAt_sqrt hb.ne').const_mul 2) (mul_pos zero_lt_two hs).ne'
  apply h.congr_deriv
  dsimp only [backwardLIntegrand]
  rw [show 2 * b = 2 * (Real.sqrt b) ^ 2 by rw [Real.sq_sqrt hb.le]]
  field_simp [hs.ne']
  <;> ring

set_option backward.isDefEq.respectTransparency false in
theorem reducedLengthGradientNormSq_eq_of_differential {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (B : M × ℝ → ℝ) (q : M) (X : TangentSpace (𝓡 n) q)
    (hB : ∀ v : TangentSpace (𝓡 n) q,
      mvfderiv (𝓡 n) (fun x ↦ B (x, b)) q v = (F.metric (T - b)).inner q X v) :
    reducedLengthGradientNormSq F T B b q = (F.metric (T - b)).inner q X X := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - b)).toRiemannianMetric⟩
  unfold reducedLengthGradientNormSq
  simp only [hB]
  change (∑ i, (inner ℝ X ((F.metric (T - b)).orthonormalBasis q i)) ^ 2) = inner ℝ X X
  rw [OrthonormalBasis.sum_sq_inner_left, real_inner_self_eq_norm_sq]

end PoincareConjecture.Proofs.M09
