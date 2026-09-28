import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Deck.Factorization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Surface.IsometryLift











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M27RoundSphereFamily

theorem productInner_isometry_symm (F : M27RoundSphereFamily)
    (d : (UnitTwoSphere × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), (𝓡 2).prod 𝓘(ℝ, ℝ)⟯
      (UnitTwoSphere × ℝ))
    (hmetric : ∀ t ≤ 0, ∀ p (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p),
      F.productInner t (d p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d p w) =
          F.productInner t p v w) :
    ∀ t ≤ 0, ∀ p (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p),
      F.productInner t (d.symm p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d.symm p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d.symm p w) =
          F.productInner t p v w := by
  intro t ht p v w
  have hcomp : d ∘ d.symm = id := funext d.apply_symm_apply
  have hd := mfderiv_comp p (d.contMDiff.mdifferentiable (by simp) _)
    (d.symm.contMDiff.mdifferentiable (by simp) p)
  rw [hcomp, mfderiv_id] at hd
  have hdv (a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d (d.symm p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d.symm p a) = a :=
    (congrArg (fun L => L a) hd).symm
  have hm := hmetric t ht (d.symm p)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d.symm p v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d.symm p w)
  calc
    _ = F.productInner t (d (d.symm p)) v w := by simpa only [hdv] using hm.symm
    _ = F.productInner t p v w :=
      congrArg (fun z => F.productInner t z v w) (d.apply_symm_apply p)

private theorem real_isometry_eq_affine {b : ℝ → ℝ} (hb : Isometry b) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ r : ℝ, ∀ z, b z = s * z + r := by
  have hs (x y : ℝ) : (b x - b y) ^ 2 = (x - y) ^ 2 := by
    have h := congrArg (fun z : ℝ => z ^ 2) (hb.dist_eq x y)
    simpa only [Real.dist_eq, sq_abs] using h
  have hsign : b 1 - b 0 = 1 ∨ b 1 - b 0 = -1 := by
    have h := hs 1 0
    norm_num at h
    exact h
  rcases hsign with hp | hn
  · refine ⟨1, Or.inl rfl, b 0, fun z => ?_⟩
    nlinarith [hs z 0, hs z 1]
  · refine ⟨-1, Or.inr rfl, b 0, fun z => ?_⟩
    nlinarith [hs z 0, hs z 1]



theorem exists_orthogonal_affine_factors (F : M27RoundSphereFamily) {c : ℝ}
    (hscale : ∀ t ≤ 0, ∀ x (v w : TangentSpace (𝓡 2) x),
      (F.metric t).inner x v w = (c - 2 * t) * (roundSphereMetric 2).inner x v w)
    (d : (UnitTwoSphere × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), (𝓡 2).prod 𝓘(ℝ, ℝ)⟯
      (UnitTwoSphere × ℝ))
    (hmetric : ∀ t ≤ 0, ∀ p (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p),
      F.productInner t (d p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d p w) =
          F.productInner t p v w) :
    ∃ L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ r : ℝ,
        ∀ p, d p = (sphereMotion L p.1, s * p.2 + r) := by
  obtain ⟨a, b, ha, hb, hfactor⟩ :=
    F.exists_smooth_factors_of_calibrated_product hscale hmetric d.contMDiff
  have hinv := F.productInner_isometry_symm d hmetric
  obtain ⟨ai, bi, hai, hbi, hfactorInv⟩ :=
    F.exists_smooth_factors_of_calibrated_product hscale hinv d.symm.contMDiff
  let s0 : UnitTwoSphere := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hlefta (x : UnitTwoSphere) : ai (a x) = x := by
    have h := congrArg Prod.fst (d.symm_apply_apply (x, 0))
    simpa only [hfactor, hfactorInv] using h
  have hrighta (x : UnitTwoSphere) : a (ai x) = x := by
    have h := congrArg Prod.fst (d.apply_symm_apply (x, 0))
    simpa only [hfactor, hfactorInv] using h
  have hleftb (z : ℝ) : bi (b z) = z := by
    have h := congrArg Prod.snd (d.symm_apply_apply (s0, z))
    simpa only [hfactor, hfactorInv] using h
  let aD : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere := {
    toFun := a
    invFun := ai
    left_inv := hlefta
    right_inv := hrighta
    contMDiff_toFun := ha
    contMDiff_invFun := hai }
  have ham := F.factor_surface_metric_of_calibrated_product hscale hmetric a b ha hb hfactor
  obtain ⟨L, hL⟩ := RicciFlow.Splitting.exists_orthogonal_surface_isometry_lift
    (roundSphereMetric 2) id (Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞).isLocalDiffeomorph
    Function.surjective_id (fun x v w => by rw [mfderiv_id]; rfl) aD ham
  have hbder := F.factor_line_deriv_sq_of_calibrated_product hscale hmetric a b ha hb hfactor
  have hbider := F.factor_line_deriv_sq_of_calibrated_product hscale hinv ai bi hai hbi hfactorInv
  have hbLip : LipschitzWith 1 b := lipschitzWith_of_nnnorm_deriv_le
    (hb.contDiff.differentiable (by simp)) fun z => by
      change |deriv b z| ≤ (1 : ℝ)
      rcases sq_eq_one_iff.mp (hbder z) with h | h <;> simp [h]
  have hbiLip : LipschitzWith 1 bi := lipschitzWith_of_nnnorm_deriv_le
    (hbi.contDiff.differentiable (by simp)) fun z => by
      change |deriv bi z| ≤ (1 : ℝ)
      rcases sq_eq_one_iff.mp (hbider z) with h | h <;> simp [h]
  have hbiometry : Isometry b := by
    apply Isometry.of_dist_eq
    intro x y
    apply le_antisymm
    · simpa using hbLip.dist_le_mul x y
    · simpa only [hleftb, NNReal.coe_one, one_mul] using hbiLip.dist_le_mul (b x) (b y)
  obtain ⟨s, hs, r, hr⟩ := real_isometry_eq_affine hbiometry
  refine ⟨L, s, hs, r, fun p => ?_⟩
  rcases p with ⟨x, z⟩
  rw [hfactor, hr]
  exact Prod.ext (hL x).symm rfl

end PoincareConjecture.M27RoundSphereFamily
