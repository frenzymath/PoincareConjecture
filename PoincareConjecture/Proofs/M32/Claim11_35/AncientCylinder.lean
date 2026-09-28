import PoincareConjecture.Proofs.M32.Claim11_35.AncientSurfaceHomothety
import PoincareConjecture.Proofs.M32.Claim11_35.AncientSphereFactor















noncomputable section
set_option autoImplicit false

open Set Topology Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M32

variable {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
  [T2Space C] [T3Space C] [ConnectedSpace C] [CompactSpace C]
  {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

set_option backward.isDefEq.respectTransparency false in



theorem roundProduct_exists_normalized_evolvingCylinder
    (hM04 : RicciFlowCurvatureTheory.{u}) (A : RicciFlow 2 C (Iic 0))
    (hround : ∀ t ≤ 0,
      ConstantPositiveSectionalCurvature (A.metric t) (A.connection t))
    (g : ℝ → RiemannianMetric 3 M) (D0 : LeviCivitaData (g 0))
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (hproduct : ∀ t ≤ 0, ∀ (z : C × ℝ)
      (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (g t).inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          (A.metric t).inner z.1 v.1 w.1 + v.2 * w.2)
    (p : M) (hnormalized : D0.scalarCurvature p = 1)
    (hno : ¬ ∃ f : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → M, IsOpenEmbedding f) :
    ∃ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
      (q : UnitTwoSphere), Φ (q, 0) = p ∧
        ∀ t ≤ 0, roundCylinderPullback (g t) Φ = EvolvingRoundCylinderMetric t := by
  have hscalar : (A.connection 0).scalarCurvature (e.symm p).1 = 1 := by
    have h := (A.metric 0).scalarCurvature_eq_of_line_product (g 0)
      (A.connection 0) D0 e (hproduct 0 le_rfl) (e.symm p)
    rw [e.apply_symm_apply] at h
    exact h.symm.trans hnormalized
  have hhom := roundSurface_inner_eq_one_sub_mul A
    (roundSurface_scalarCurvature_eq_one_div_one_sub hM04 A hround (e.symm p).1 hscalar)
  obtain ⟨a, ha⟩ := roundSurface_exists_sphereDiffeomorph_of_no_projective_product
    (A.metric 0) (A.connection 0) (hround 0 le_rfl) (e.symm p).1 hscalar
    e.toHomeomorph hno
  have hsphere (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x) :
      (1 : ℝ) * (A.metric 0).inner (a x)
        (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
          2 * (roundSphereMetric 2).inner x v w := by
    simpa only [one_mul] using ha x v w
  obtain ⟨Φ, q, hformula, _, hcenter, _⟩ :=
    exists_centered_scalarNormalized_roundCylinder (g 0) (A.metric 0) e
      (hproduct 0 le_rfl) (by norm_num : (0 : ℝ) < 1) a hsphere p
  refine ⟨Φ, q, hcenter, ?_⟩
  intro t ht
  let r0 := (e.symm p).2
  let b : RoundCylinderSpace → C × ℝ := Prod.map a (fun r => r0 + r)
  have hlineSmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun r : ℝ => r0 + r) :=
    (contDiff_const.add contDiff_id).contMDiff
  have hb : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ b :=
    a.contMDiff.prodMap hlineSmooth
  have hΦ : (Φ : RoundCylinderSpace → M) = e ∘ b := by
    funext z
    change Φ z = e (a z.1, r0 + z.2)
    simpa only [Real.sqrt_one, div_one, r0] using hformula z
  have hline (r v : ℝ) :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z : ℝ => r0 + z) r v = v := by
    have hfd : fderiv ℝ (fun z : ℝ => r0 + z) r = ContinuousLinearMap.id ℝ ℝ :=
      ((hasFDerivAt_id r).const_add r0).fderiv
    simp only [mfderiv_eq_fderiv, hfd]
    rfl
  funext z v w
  have hdb (v : RoundCylinderTangent z) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) b z v =
        (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1, v.2) := by
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (Prod.map a (fun r => r0 + r)) z v = _
    rw [mfderiv_prodMap (a.mdifferentiable (by simp) _)
      (hlineSmooth.mdifferentiable (by simp) _)]
    change (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ => r0 + r) z.2 v.2) = _
    rw [hline]
  have hdΦ (v : RoundCylinderTangent z) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (b z)
          (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1, v.2) := by
    rw [hΦ, mfderiv_comp z (e.mdifferentiable (by simp) _)
      (hb.mdifferentiable (by simp) _)]
    exact congrArg (fun u => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (b z) u) (hdb v)
  change (g t).inner (Φ z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z w) = _
  rw [hdΦ, hdΦ, hΦ]
  change (g t).inner (e (b z)) _ _ = _
  rw [hproduct t ht]
  change (A.metric t).inner (a z.1)
    (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1)
    (mfderiv (𝓡 2) (𝓡 2) a z.1 w.1) + v.2 * w.2 = _
  rw [hhom t ht, ha]
  calc
    (1 - t) * (2 * (roundSphereMetric 2).inner z.1 v.1 w.1) + v.2 * w.2 =
        2 * (1 - t) * (roundSphereMetric 2).inner z.1 v.1 w.1 + v.2 * w.2 := by ring
    _ = EvolvingRoundCylinderMetric t z v w := rfl

end PoincareConjecture.M32
