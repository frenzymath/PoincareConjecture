
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.OperatorReaction.Diagonal











namespace Poincare.HamiltonIvey

noncomputable section

local instance : NormedAddCommGroup ThreeMatrix := Matrix.normedAddCommGroup
local instance : NormedSpace ℝ ThreeMatrix := Matrix.normedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]



noncomputable def endomorphismReaction
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  4 • (A * A) - (2 * LinearMap.trace ℝ E A) • A +
    ((LinearMap.trace ℝ E A) ^ 2 - LinearMap.trace ℝ E (A * A)) • 1

theorem toMatrix_endomorphismReaction (e : OrthonormalBasis (Fin 3) ℝ E)
    (A : E →ₗ[ℝ] E) :
    LinearMap.toMatrix e.toBasis e.toBasis (endomorphismReaction A) =
      operatorReaction (LinearMap.toMatrix e.toBasis e.toBasis A) := by
  rw [operatorReaction_eq_trace_polynomial]
  simp [endomorphismReaction, LinearMap.trace_eq_matrix_trace ℝ e.toBasis,
    LinearMap.toMatrix_mul, ← Nat.cast_smul_eq_nsmul ℝ]

omit [FiniteDimensional ℝ E] in
theorem continuousOn_operatorMatrix {a b : ℝ} {A : ℝ → E →ₗ[ℝ] E}
    (e : OrthonormalBasis (Fin 3) ℝ E)
    (hA : ∀ v : E, ContinuousOn (fun t => A t v) (Set.Icc a b)) :
    ContinuousOn (fun t => LinearMap.toMatrix e.toBasis e.toBasis (A t)) (Set.Icc a b) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  simpa [LinearMap.toMatrix_apply, e.coe_toBasis_repr_apply, e.repr_apply_apply] using
    continuousOn_const.inner (hA (e j))

omit [FiniteDimensional ℝ E] in
theorem hasDerivAt_operatorMatrix {A : ℝ → E →ₗ[ℝ] E} {D : E →ₗ[ℝ] E}
    (e : OrthonormalBasis (Fin 3) ℝ E) {t : ℝ}
    (hd : ∀ v : E, HasDerivAt (fun s => A s v) (D v) t) :
    HasDerivAt (fun s => LinearMap.toMatrix e.toBasis e.toBasis (A s))
      (LinearMap.toMatrix e.toBasis e.toBasis D) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  simpa [LinearMap.toMatrix_apply, e.coe_toBasis_repr_apply, e.repr_apply_apply] using
    (hasDerivAt_const t (e i)).inner ℝ (hd (e j))

end

end Poincare.HamiltonIvey
