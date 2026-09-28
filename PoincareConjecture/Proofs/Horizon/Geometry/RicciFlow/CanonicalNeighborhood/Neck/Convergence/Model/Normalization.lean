import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere
import Mathlib.Geometry.Manifold.Diffeomorph








noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture

def scalarNormalizedCylinderLine (R r₀ : ℝ) (hR : 0 < R) : ℝ ≃ₘ[ℝ] ℝ where
  toFun r := r₀ + r / Real.sqrt R
  invFun r := (r - r₀) * Real.sqrt R
  left_inv r := by
    dsimp
    field_simp [(Real.sqrt_pos.mpr hR).ne']
    ring
  right_inv r := by
    dsimp
    rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hR).ne']
    ring
  contMDiff_toFun := (contDiff_const.add (contDiff_id.div_const _)).contMDiff
  contMDiff_invFun := ((contDiff_id.sub contDiff_const).mul contDiff_const).contMDiff

theorem mfderiv_scalarNormalizedCylinderLine (R r₀ : ℝ) (hR : 0 < R)
    (r v : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (scalarNormalizedCylinderLine R r₀ hR) r v =
      v / Real.sqrt R := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (fun t : ℝ => r₀ + t / Real.sqrt R) r v = _
  have hd : HasDerivAt (fun t : ℝ => r₀ + t / Real.sqrt R) (1 / Real.sqrt R) r :=
    ((hasDerivAt_id r).div_const (Real.sqrt R)).const_add r₀
  rw [hd.hasFDerivAt.fderiv]
  simp [div_eq_mul_inv]

variable {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
  {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



def centeredScalarNormalizedCylinderDiffeomorph
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ C)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (R : ℝ) (hR : 0 < R) (p : M) :
    RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M :=
  (a.prodCongr (scalarNormalizedCylinderLine R (e.symm p).2 hR)).trans e

omit [IsManifold (𝓡 2) ∞ C] [IsManifold (𝓡 3) ∞ M] in
@[simp] theorem centeredScalarNormalizedCylinderDiffeomorph_apply
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ C)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (R : ℝ) (hR : 0 < R) (p : M) (z : RoundCylinderSpace) :
    centeredScalarNormalizedCylinderDiffeomorph a e R hR p z =
      e (a z.1, (e.symm p).2 + z.2 / Real.sqrt R) := rfl



theorem exists_centered_scalarNormalized_roundCylinder
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 2 C)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (hproduct : ∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      g.inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          h.inner z.1 v.1 w.1 + v.2 * w.2)
    {R : ℝ} (hR : 0 < R) (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ C)
    (hsphere : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
      R * h.inner (a x) (mfderiv (𝓡 2) (𝓡 2) a x v)
        (mfderiv (𝓡 2) (𝓡 2) a x w) =
          2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w)
    (p : M) :
    ∃ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
      (q : UnitTwoSphere),
      (∀ z, Φ z = e (a z.1, (e.symm p).2 + z.2 / Real.sqrt R)) ∧
      q = a.symm (e.symm p).1 ∧ Φ (q, 0) = p ∧
      (fun z v w => R * roundCylinderPullback g Φ z v w) =
        EvolvingRoundCylinderMetric 0 := by
  let ℓ := scalarNormalizedCylinderLine R (e.symm p).2 hR
  let b := a.prodCongr ℓ
  let Φ := centeredScalarNormalizedCylinderDiffeomorph a e R hR p
  refine ⟨Φ, a.symm (e.symm p).1, fun z => rfl, rfl, ?_, ?_⟩
  · change e (a (a.symm (e.symm p).1), (e.symm p).2 + 0 / Real.sqrt R) = p
    rw [a.apply_symm_apply, zero_div, add_zero, Prod.mk.eta, e.apply_symm_apply]
  · funext z v w
    have hdb (v : RoundCylinderTangent z) :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) b z v =
          (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1, v.2 / Real.sqrt R) := by
      change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (Prod.map a ℓ) z v = _
      rw [mfderiv_prodMap (a.mdifferentiable (by simp) _)
        (ℓ.mdifferentiable (by simp) _)]
      change (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1,
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℓ z.2 v.2) = _
      rw [mfderiv_scalarNormalizedCylinderLine]
    have hdΦ (v : RoundCylinderTangent z) :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v =
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (b z)
            (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1, v.2 / Real.sqrt R) := by
      change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (e ∘ b) z v = _
      rw [mfderiv_comp z (e.mdifferentiable (by simp) _) (b.mdifferentiable (by simp) _)]
      exact congrArg (fun t => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (b z) t) (hdb v)
    change R * g.inner (Φ z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z w) = _
    rw [hdΦ, hdΦ]
    change R * g.inner (e (b z)) _ _ = _
    rw [hproduct]
    change R * (h.inner (a z.1)
      (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1)
      (mfderiv (𝓡 2) (𝓡 2) a z.1 w.1) +
        (v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = _
    rw [mul_add, hsphere]
    have hline : R * ((v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = v.2 * w.2 := by
      rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hR.le]
      exact mul_div_cancel₀ _ hR.ne'
    rw [hline]
    simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one]
    rfl

end PoincareConjecture
