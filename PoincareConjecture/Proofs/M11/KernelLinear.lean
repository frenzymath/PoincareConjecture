import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.Algebra.Module.Equiv





set_option autoImplicit false

namespace PoincareConjecture.Proofs.M11

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable def spatialKernelEquiv (e : (E × F) ≃L[ℝ] G) (dt : G →L[ℝ] ℝ)
    (a : E ≃L[ℝ] ℝ) (h : ∀ v, dt (e v) = a v.1) : F ≃L[ℝ] dt.ker := by
  let f : F →L[ℝ] dt.ker :=
    (e.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ E F)).codRestrict dt.ker
      (fun v ↦ by
        change dt (e (0, v)) = 0
        rw [h, map_zero])
  let g : dt.ker →L[ℝ] F :=
    (ContinuousLinearMap.snd ℝ E F).comp (e.symm.toContinuousLinearMap.comp dt.ker.subtypeL)
  refine ContinuousLinearEquiv.equivOfInverse f g ?_ ?_
  · intro v
    change (e.symm (e (0, v))).2 = v
    rw [e.symm_apply_apply]
  · intro v
    apply Subtype.ext
    have hzero : (e.symm v.val).1 = 0 := by
      apply a.injective
      rw [map_zero, ← h, e.apply_symm_apply]
      exact v.property
    change e (0, (e.symm v.val).2) = v.val
    rw [← hzero]
    exact e.apply_symm_apply v.val

theorem spatialKernelEquiv_apply (e : (E × F) ≃L[ℝ] G) (dt : G →L[ℝ] ℝ)
    (a : E ≃L[ℝ] ℝ) (h : ∀ v, dt (e v) = a v.1) (v : F) :
    (spatialKernelEquiv e dt a h v).val = e (0, v) := rfl

theorem spatialKernelEquiv_symm_apply (e : (E × F) ≃L[ℝ] G) (dt : G →L[ℝ] ℝ)
    (a : E ≃L[ℝ] ℝ) (h : ∀ v, dt (e v) = a v.1) (v : dt.ker) :
    (spatialKernelEquiv e dt a h).symm v = (e.symm v.val).2 := rfl

noncomputable def normalizedKernelProjection (dt : G →L[ℝ] ℝ) (v : G) (hv : dt v = 1) :
    G →L[ℝ] dt.ker :=
  dt.projKerOfRightInverse ((ContinuousLinearMap.id ℝ ℝ).smulRight v) (by
    intro t
    change dt (t • v) = t
    rw [map_smul, hv, smul_eq_mul, mul_one])

theorem normalizedKernelProjection_apply (dt : G →L[ℝ] ℝ) (v : G) (hv : dt v = 1)
    (w : G) : (normalizedKernelProjection dt v hv w).val = w - dt w • v := rfl

theorem normalizedKernelProjection_identity (dt : G →L[ℝ] ℝ) (v : G) (hv : dt v = 1)
    (w : dt.ker) : normalizedKernelProjection dt v hv w.val = w := by
  apply ContinuousLinearMap.projKerOfRightInverse_apply_idem

theorem normalizedKernelProjection_decomposition (dt : G →L[ℝ] ℝ) (v : G) (hv : dt v = 1)
    (w : G) : w = dt w • v + (normalizedKernelProjection dt v hv w).val := by
  rw [normalizedKernelProjection_apply, add_sub_cancel]

end PoincareConjecture.Proofs.M11
