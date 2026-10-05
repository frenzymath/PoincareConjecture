import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Operator coordinates given by a finite basis

Evaluation on a finite basis identifies continuous linear maps with
their tuples of vertex values in the actual operator and product
topologies. This is the linear-coordinate calculation in Cairns 1940,
pp. 799, 801; see M76 derivation 25.
-/

set_option autoImplicit false

namespace Module.Basis

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear map is continuously determined by its values
on a finite basis. See Cairns pp. 799, 801 and M76 derivation 25. -/
noncomputable def evaluationContinuousLinearEquiv (b : Basis ι 𝕜 E) :
    (E →L[𝕜] F) ≃L[𝕜] (ι → F) :=
  (b.equivFunL.arrowCongr (ContinuousLinearEquiv.refl 𝕜 F)).trans
    (ContinuousLinearEquiv.piRing ι)

/-- The operator coordinate indexed by `i` is evaluation at `b i`.
See Cairns p. 799 and M76 derivation 25. -/
@[simp] theorem evaluationContinuousLinearEquiv_apply (b : Basis ι 𝕜 E)
    (Q : E →L[𝕜] F) (i : ι) : b.evaluationContinuousLinearEquiv Q i = Q (b i) := by
  change Q (b.equivFunL.symm (Pi.single i 1)) = Q (b i)
  congr 1
  apply b.equivFunL.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext j
  simp only [equivFunL_apply, repr_self_apply, Pi.single_apply, eq_comm]

/-- The inverse operator has exactly the prescribed basis values.
See Cairns p. 799 and M76 derivation 25. -/
@[simp] theorem evaluationContinuousLinearEquiv_symm_apply_basis (b : Basis ι 𝕜 E)
    (v : ι → F) (i : ι) : b.evaluationContinuousLinearEquiv.symm v (b i) = v i := by
  rw [← evaluationContinuousLinearEquiv_apply]
  exact congrFun (b.evaluationContinuousLinearEquiv.apply_symm_apply v) i

end Module.Basis
