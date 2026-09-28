import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.ParametrizedCoefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.DomainChange










set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Calculus

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']


noncomputable def parameterBilinearEquiv (L : E' ≃L[ℝ] E) :
    (E →L[ℝ] E →L[ℝ] ℝ) ≃L[ℝ] (E' →L[ℝ] E' →L[ℝ] ℝ) :=
  L.symm.arrowCongr (L.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))

@[simp] theorem parameterBilinearEquiv_apply
    (L : E' ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] ℝ) (v w : E') :
    parameterBilinearEquiv L B v w = B (L v) (L w) := rfl

theorem parameterBilinearEquiv_eq_bilinearComp
    (L : E' ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    parameterBilinearEquiv L B = B.bilinearComp L.toContinuousLinearMap L.toContinuousLinearMap := by
  ext v w
  rfl

theorem norm_parameterBilinearEquiv_le (L : E' ≃L[ℝ] E) :
    ‖(parameterBilinearEquiv L).toContinuousLinearMap‖ ≤ ‖L.toContinuousLinearMap‖ ^ 2 := by
  apply (parameterBilinearEquiv L).toContinuousLinearMap.opNorm_le_bound (sq_nonneg _)
  intro B
  apply (parameterBilinearEquiv L B).opNorm_le_bound₂ (by positivity)
  intro v w
  simp only [parameterBilinearEquiv_apply]
  calc
    ‖B (L v) (L w)‖ ≤ ‖B‖ * ‖L v‖ * ‖L w‖ := B.le_opNorm₂ _ _
    _ ≤ ‖B‖ * (‖L.toContinuousLinearMap‖ * ‖v‖) *
        (‖L.toContinuousLinearMap‖ * ‖w‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (L.toContinuousLinearMap.le_opNorm v) (norm_nonneg _)
      · exact L.toContinuousLinearMap.le_opNorm w
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

theorem iteratedFDeriv_parameterBilinearEquiv_comp
    (L : E' ≃L[ℝ] E) (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℕ) (x : E') :
    iteratedFDeriv ℝ m (fun y => parameterBilinearEquiv L (B (L y))) x =
      (parameterBilinearEquiv L).toContinuousLinearMap.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m B (L x)).compContinuousLinearMap
          (fun _ => L.toContinuousLinearMap)) := by
  change iteratedFDeriv ℝ m ((parameterBilinearEquiv L) ∘ (B ∘ L)) x = _
  rw [ContinuousLinearEquiv.iteratedFDeriv_comp_left,
    iteratedFDeriv_comp_continuousLinearEquiv]

private theorem norm_parameterJet_le
    (L : E' ≃L[ℝ] E) (m : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => E) (E →L[ℝ] E →L[ℝ] ℝ)) :
    ‖(parameterBilinearEquiv L).toContinuousLinearMap.compContinuousMultilinearMap
      (T.compContinuousLinearMap (fun _ => L.toContinuousLinearMap))‖ ≤
      ‖L.toContinuousLinearMap‖ ^ (m + 2) * ‖T‖ := by
  calc
    _ ≤ ‖(parameterBilinearEquiv L).toContinuousLinearMap‖ *
        ‖T.compContinuousLinearMap (fun _ => L.toContinuousLinearMap)‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖L.toContinuousLinearMap‖ ^ 2 *
        (‖T‖ * ‖L.toContinuousLinearMap‖ ^ m) := by
      apply mul_le_mul (norm_parameterBilinearEquiv_le L)
      · simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          T.norm_compContinuousLinearMap_le (fun _ : Fin m => L.toContinuousLinearMap)
      · exact norm_nonneg _
      · positivity
    _ = _ := by rw [pow_add]; ring

theorem norm_iteratedFDeriv_parameterBilinearEquiv_comp_le
    (L : E' ≃L[ℝ] E) (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m (fun y => parameterBilinearEquiv L (B (L y))) x‖ ≤
      ‖L.toContinuousLinearMap‖ ^ (m + 2) * ‖iteratedFDeriv ℝ m B (L x)‖ := by
  rw [iteratedFDeriv_parameterBilinearEquiv_comp]
  exact norm_parameterJet_le L m _

theorem norm_iteratedFDeriv_parameterBilinearEquiv_comp_sub_le
    (L : E' ≃L[ℝ] E) (B C : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m (fun y => parameterBilinearEquiv L (B (L y))) x -
      iteratedFDeriv ℝ m (fun y => parameterBilinearEquiv L (C (L y))) x‖ ≤
      ‖L.toContinuousLinearMap‖ ^ (m + 2) *
        ‖iteratedFDeriv ℝ m B (L x) - iteratedFDeriv ℝ m C (L x)‖ := by
  rw [iteratedFDeriv_parameterBilinearEquiv_comp,
    iteratedFDeriv_parameterBilinearEquiv_comp]
  have heq :
      (parameterBilinearEquiv L).toContinuousLinearMap.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m B (L x)).compContinuousLinearMap (fun _ => L.toContinuousLinearMap)) -
      (parameterBilinearEquiv L).toContinuousLinearMap.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m C (L x)).compContinuousLinearMap (fun _ => L.toContinuousLinearMap)) =
      (parameterBilinearEquiv L).toContinuousLinearMap.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m B (L x) - iteratedFDeriv ℝ m C (L x)).compContinuousLinearMap
          (fun _ => L.toContinuousLinearMap)) := by
    ext v a b
    rfl
  rw [heq]
  exact norm_parameterJet_le L m _

@[simp] theorem parameterBilinearEquiv_symm_apply_apply
    (L : E' ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    parameterBilinearEquiv L.symm (parameterBilinearEquiv L B) = B := by
  ext v w
  simp only [parameterBilinearEquiv_apply, L.apply_symm_apply]

theorem norm_iteratedFDeriv_le_parameterBilinearEquiv_comp
    (L : E' ≃L[ℝ] E) (B : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m B (L x)‖ ≤
      ‖L.symm.toContinuousLinearMap‖ ^ (m + 2) *
        ‖iteratedFDeriv ℝ m (fun y => parameterBilinearEquiv L (B (L y))) x‖ := by
  have h := norm_iteratedFDeriv_parameterBilinearEquiv_comp_le L.symm
    (fun y => parameterBilinearEquiv L (B (L y))) m (L x)
  simpa only [L.symm_apply_apply, L.apply_symm_apply,
    parameterBilinearEquiv_symm_apply_apply] using h

theorem norm_iteratedFDeriv_sub_le_parameterBilinearEquiv_comp
    (L : E' ≃L[ℝ] E) (B C : E → E →L[ℝ] E →L[ℝ] ℝ) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m B (L x) - iteratedFDeriv ℝ m C (L x)‖ ≤
      ‖L.symm.toContinuousLinearMap‖ ^ (m + 2) *
        ‖iteratedFDeriv ℝ m (fun y => parameterBilinearEquiv L (B (L y))) x -
          iteratedFDeriv ℝ m (fun y => parameterBilinearEquiv L (C (L y))) x‖ := by
  have h := norm_iteratedFDeriv_parameterBilinearEquiv_comp_sub_le L.symm
    (fun y => parameterBilinearEquiv L (B (L y)))
    (fun y => parameterBilinearEquiv L (C (L y))) m (L x)
  simpa only [L.symm_apply_apply, L.apply_symm_apply,
    parameterBilinearEquiv_symm_apply_apply] using h

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
private theorem mdifferentiableAt_comp_parameterEquiv_iff
    (L : E' ≃L[ℝ] E) (f : E → M) (x : E') :
    MDifferentiableAt 𝓘(ℝ, E') (𝓡 n) (f ∘ L) x ↔
      MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) f (L x) := by
  constructor
  · intro h
    have hh := (show MDifferentiableAt 𝓘(ℝ, E') (𝓡 n) (f ∘ L) (L.symm (L x)) by simpa using h).comp
      (L x) L.symm.differentiableAt.mdifferentiableAt
    simpa only [Function.comp_def, L.symm_apply_apply, L.apply_symm_apply] using hh
  · intro h
    exact h.comp x L.differentiableAt.mdifferentiableAt

omit [IsManifold (𝓡 n) ∞ M] in
theorem mfderiv_comp_parameterEquiv
    (L : E' ≃L[ℝ] E) (f : E → M) (x : E') :
    mfderiv 𝓘(ℝ, E') (𝓡 n) (f ∘ L) x =
      (mfderiv 𝓘(ℝ, E) (𝓡 n) f (L x)).comp L.toContinuousLinearMap := by
  by_cases hf : MDifferentiableAt 𝓘(ℝ, E) (𝓡 n) f (L x)
  · have h := mfderiv_comp x hf L.differentiableAt.mdifferentiableAt
    simpa only [mfderiv_eq_fderiv, L.fderiv] using h
  · have hcomp := mt (mdifferentiableAt_comp_parameterEquiv_iff L f x).mp hf
    rw [mfderiv_zero_of_not_mdifferentiableAt hcomp,
      mfderiv_zero_of_not_mdifferentiableAt hf, ContinuousLinearMap.zero_comp]

theorem parametrizedCoefficients_comp_parameterEquiv
    (g : RiemannianMetric n M) (L : E' ≃L[ℝ] E) (f : E → M) :
    g.parametrizedCoefficients (f ∘ L) =
      fun x => parameterBilinearEquiv L (g.parametrizedCoefficients f (L x)) := by
  funext x
  ext v w
  simp only [parameterBilinearEquiv_apply, parametrizedCoefficients_apply,
    mfderiv_comp_parameterEquiv, ContinuousLinearMap.comp_apply,
    Function.comp_apply]
  rfl

theorem norm_iteratedFDeriv_parametrizedCoefficients_comp_parameterEquiv_le
    (g : RiemannianMetric n M) (L : E' ≃L[ℝ] E) (f : E → M) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m (g.parametrizedCoefficients (f ∘ L)) x‖ ≤
      ‖L.toContinuousLinearMap‖ ^ (m + 2) *
        ‖iteratedFDeriv ℝ m (g.parametrizedCoefficients f) (L x)‖ := by
  rw [parametrizedCoefficients_comp_parameterEquiv]
  exact norm_iteratedFDeriv_parameterBilinearEquiv_comp_le L _ m x

theorem norm_iteratedFDeriv_parametrizedCoefficients_le_comp_parameterEquiv
    (g : RiemannianMetric n M) (L : E' ≃L[ℝ] E) (f : E → M) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m (g.parametrizedCoefficients f) (L x)‖ ≤
      ‖L.symm.toContinuousLinearMap‖ ^ (m + 2) *
        ‖iteratedFDeriv ℝ m (g.parametrizedCoefficients (f ∘ L)) x‖ := by
  rw [parametrizedCoefficients_comp_parameterEquiv]
  exact norm_iteratedFDeriv_le_parameterBilinearEquiv_comp L _ m x

theorem norm_iteratedFDeriv_parametrizedCoefficients_comp_sub_le
    (g h : RiemannianMetric n M) (L : E' ≃L[ℝ] E) (f : E → M) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m (g.parametrizedCoefficients (f ∘ L)) x -
      iteratedFDeriv ℝ m (h.parametrizedCoefficients (f ∘ L)) x‖ ≤
      ‖L.toContinuousLinearMap‖ ^ (m + 2) *
        ‖iteratedFDeriv ℝ m (g.parametrizedCoefficients f) (L x) -
          iteratedFDeriv ℝ m (h.parametrizedCoefficients f) (L x)‖ := by
  rw [parametrizedCoefficients_comp_parameterEquiv,
    parametrizedCoefficients_comp_parameterEquiv]
  exact norm_iteratedFDeriv_parameterBilinearEquiv_comp_sub_le L _ _ m x

theorem norm_iteratedFDeriv_parametrizedCoefficients_sub_le_comp
    (g h : RiemannianMetric n M) (L : E' ≃L[ℝ] E) (f : E → M) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m (g.parametrizedCoefficients f) (L x) -
      iteratedFDeriv ℝ m (h.parametrizedCoefficients f) (L x)‖ ≤
      ‖L.symm.toContinuousLinearMap‖ ^ (m + 2) *
        ‖iteratedFDeriv ℝ m (g.parametrizedCoefficients (f ∘ L)) x -
          iteratedFDeriv ℝ m (h.parametrizedCoefficients (f ∘ L)) x‖ := by
  rw [parametrizedCoefficients_comp_parameterEquiv,
    parametrizedCoefficients_comp_parameterEquiv]
  exact norm_iteratedFDeriv_sub_le_parameterBilinearEquiv_comp L _ _ m x

omit [IsManifold (𝓡 n) ∞ M] in
theorem contMDiffOn_comp_parameterEquiv
    (L : E' ≃L[ℝ] E) {f : E → M} {U : Set E} {k : ℕ∞ω}
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) k f U) :
    ContMDiffOn 𝓘(ℝ, E') (𝓡 n) k (f ∘ L) (L ⁻¹' U) :=
  hf.comp L.contDiff.contMDiff.contMDiffOn (fun _ hx => hx)

omit [IsManifold (𝓡 n) ∞ M] in
theorem isInvertible_mfderiv_comp_parameterEquiv_iff
    (L : E' ≃L[ℝ] E) (f : E → M) (x : E') :
    (mfderiv 𝓘(ℝ, E') (𝓡 n) (f ∘ L) x).IsInvertible ↔
      (mfderiv 𝓘(ℝ, E) (𝓡 n) f (L x)).IsInvertible := by
  rw [mfderiv_comp_parameterEquiv]
  constructor
  · intro h
    have h' := h.comp (show L.symm.toContinuousLinearMap.IsInvertible from ⟨L.symm, rfl⟩)
    have heq : ((mfderiv 𝓘(ℝ, E) (𝓡 n) f (L x)).comp L.toContinuousLinearMap).comp
        L.symm.toContinuousLinearMap = mfderiv 𝓘(ℝ, E) (𝓡 n) f (L x) := by
      ext v
      change (mfderiv 𝓘(ℝ, E) (𝓡 n) f (L x)) (L (L.symm v)) = _
      rw [L.apply_symm_apply]
      rfl
    rw [heq] at h'
    exact h'
  · intro h
    exact h.comp ⟨L, rfl⟩

end PoincareConjecture.RiemannianMetric
