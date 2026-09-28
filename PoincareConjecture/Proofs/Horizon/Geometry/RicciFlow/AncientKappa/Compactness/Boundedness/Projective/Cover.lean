import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.SphereCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Models
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.LocalDiffeomorph.Product










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

private def projectiveNormalizedLine (R r₀ : ℝ) (hR : 0 < R) : ℝ ≃ₘ[ℝ] ℝ where
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

private theorem mfderiv_projectiveNormalizedLine (R r₀ : ℝ) (hR : 0 < R)
    (r v : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (projectiveNormalizedLine R r₀ hR) r v =
      v / Real.sqrt R := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ (fun t : ℝ => r₀ + t / Real.sqrt R) r v = _
  have hd : HasDerivAt (fun t : ℝ => r₀ + t / Real.sqrt R) (1 / Real.sqrt R) r :=
    ((hasDerivAt_id r).div_const (Real.sqrt R)).const_add r₀
  rw [hd.hasFDerivAt.fderiv]
  simp [div_eq_mul_inv]

variable {C : Type*} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
  {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem exists_centered_scalarNormalized_projectiveCylinder_cover
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 2 C)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (hproduct : ∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      g.inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          h.inner z.1 v.1 w.1 + v.2 * w.2)
    {R : ℝ} (hR : 0 < R) (q : UnitTwoSphere → C)
    (hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q)
    (hsurj : Function.Surjective q)
    (hfiber : ∀ x y, q x = q y ↔ y = x ∨ y = -x)
    (hsphere : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
      R * h.inner (q x) (mfderiv (𝓡 2) (𝓡 2) q x v)
        (mfderiv (𝓡 2) (𝓡 2) q x w) =
          2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w)
    (p : M) :
    ∃ (Φ : RoundCylinderSpace → M) (x : UnitTwoSphere),
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ ∧
      Function.Surjective Φ ∧ Φ (x, 0) = p ∧
      (∀ z w, Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) ∧
      (fun z v w => R * roundCylinderPullback g Φ z v w) =
        EvolvingRoundCylinderMetric 0 := by
  let ℓ := projectiveNormalizedLine R (e.symm p).2 hR
  let b : RoundCylinderSpace → C × ℝ := Prod.map q ℓ
  let Φ : RoundCylinderSpace → M := e ∘ b
  have hb : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ b := hq.prodMap ℓ.isLocalDiffeomorph
  obtain ⟨x, hx⟩ := hsurj (e.symm p).1
  refine ⟨Φ, x, fun z => (hb z).comp (𝓡 3) M (e.isLocalDiffeomorph (b z)),
    ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨a, ha⟩ := hsurj (e.symm y).1
    refine ⟨(a, ℓ.symm (e.symm y).2), ?_⟩
    change e (q a, ℓ (ℓ.symm (e.symm y).2)) = y
    rw [ha, ℓ.apply_symm_apply, Prod.mk.eta, e.apply_symm_apply]
  · change e (q x, (e.symm p).2 + 0 / Real.sqrt R) = p
    rw [hx, zero_div, add_zero, Prod.mk.eta, e.apply_symm_apply]
  · intro z w
    constructor
    · intro heq
      have hp : b z = b w := e.injective heq
      have hs : q z.1 = q w.1 := congrArg Prod.fst hp
      have hl : z.2 = w.2 := ℓ.injective (congrArg Prod.snd hp)
      rcases (hfiber _ _).mp hs with hs | hs
      · exact Or.inl (Prod.ext hs hl.symm)
      · exact Or.inr (Prod.ext hs hl.symm)
    · rintro (rfl | rfl)
      · rfl
      · change e (q z.1, ℓ z.2) = e (q (-z.1), ℓ z.2)
        rw [(hfiber z.1 (-z.1)).mpr (Or.inr rfl)]
  · funext z v w
    have hdb (v : RoundCylinderTangent z) :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) b z v =
          (mfderiv (𝓡 2) (𝓡 2) q z.1 v.1, v.2 / Real.sqrt R) := by
      change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (Prod.map q ℓ) z v = _
      rw [mfderiv_prodMap (hq.mdifferentiable (by simp) _)
        (ℓ.mdifferentiable (by simp) _)]
      change (mfderiv (𝓡 2) (𝓡 2) q z.1 v.1,
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℓ z.2 v.2) = _
      rw [mfderiv_projectiveNormalizedLine]
    have hdΦ (v : RoundCylinderTangent z) :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v =
          mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (b z)
            (mfderiv (𝓡 2) (𝓡 2) q z.1 v.1, v.2 / Real.sqrt R) := by
      rw [mfderiv_comp z (e.mdifferentiable (by simp) _) (hb.mdifferentiable (by simp) _)]
      exact congrArg (fun t => mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e (b z) t) (hdb v)
    change R * g.inner (Φ z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z w) = _
    rw [hdΦ, hdΦ]
    change R * g.inner (e (b z)) _ _ = _
    rw [hproduct]
    change R * (h.inner (q z.1)
      (mfderiv (𝓡 2) (𝓡 2) q z.1 v.1)
      (mfderiv (𝓡 2) (𝓡 2) q z.1 w.1) +
        (v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = _
    rw [mul_add, hsphere]
    have hline : R * ((v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = v.2 * w.2 := by
      rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hR.le]
      exact mul_div_cancel₀ _ hR.ne'
    rw [hline]
    simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one]
    rfl

variable [T2Space C] [T3Space C] [ConnectedSpace C]
  [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]



theorem TwoDimensionalAncientRoundCertificate.roundCylinder_or_projective_cover
    {A : AncientKappaSolution 2 C} (H : TwoDimensionalAncientRoundCertificate A)
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (e : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
    (hproduct : ∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      g.inner (e z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
          (A.flow.metric 0).inner z.1 v.1 w.1 + v.2 * w.2)
    (p : M) :
    0 < D.scalarCurvature p ∧
      ((∃ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M)
          (x : UnitTwoSphere), Φ (x, 0) = p ∧
          (fun z v w => D.scalarCurvature p * roundCylinderPullback g Φ z v w) =
            EvolvingRoundCylinderMetric 0) ∨
        ∃ (Φ : RoundCylinderSpace → M) (x : UnitTwoSphere),
          IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ ∧
          Function.Surjective Φ ∧ Φ (x, 0) = p ∧
          (∀ z w, Φ z = Φ w ↔ w = z ∨ w = (-z.1, z.2)) ∧
          (fun z v w => D.scalarCurvature p * roundCylinderPullback g Φ z v w) =
            EvolvingRoundCylinderMetric 0) := by
  let : CompactSpace C := H.compact
  obtain ⟨hpos, hsphere | ⟨q, _, hsurj, hlocal, hnorm, hfiber⟩⟩ :=
    roundCylinder_or_antipodal_cover_of_round_surface_product
      (A.flow.metric 0) g (A.flow.connection 0) D (H.round_at_all_times 0 le_rfl)
      e hproduct p
  · exact ⟨hpos, Or.inl hsphere⟩
  · exact ⟨hpos, Or.inr (exists_centered_scalarNormalized_projectiveCylinder_cover
      g (A.flow.metric 0) e hproduct hpos q hlocal hsurj hfiber hnorm p)⟩

end PoincareConjecture
