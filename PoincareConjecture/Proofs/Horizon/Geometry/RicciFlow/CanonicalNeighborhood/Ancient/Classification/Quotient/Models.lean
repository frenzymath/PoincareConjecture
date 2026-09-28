import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Quotient.Certificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

noncomputable section

universe u

namespace PoincareConjecture.AncientCylinderQuotient

theorem cylinderCenterShift_mfderiv (a : ℝ) (p : UnitTwoSphere × ℝ)
    (v : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (cylinderCenterShift a) p v = v := by
  change (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (Prod.map (id : UnitTwoSphere → UnitTwoSphere) (fun z : ℝ => z - a)) p v :
      EuclideanSpace ℝ (Fin 2) × ℝ) = v
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun z : ℝ => z - a) :=
    contMDiff_id.sub contMDiff_const
  have hl := hs.mdifferentiable (by simp) p.2
  rw [mfderiv_prodMap mdifferentiableAt_id
    hl,
    mfderiv_id, mfderiv_eq_fderiv]
  rw [fderiv_sub_const]
  simp
  rfl

theorem cylinderCenterShift_productInner (F : M27RoundSphereFamily)
    (a t : ℝ) (p : UnitTwoSphere × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
    F.productInner t (cylinderCenterShift a p)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (cylinderCenterShift a) p v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
        (cylinderCenterShift a) p w) = F.productInner t p v w := by
  rw [cylinderCenterShift_mfderiv, cylinderCenterShift_mfderiv]
  rfl

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem models_of_fiber_alternatives
    (F : M27RoundSphereFamily) (q : UnitTwoSphere × ℝ → M)
    (hq : Function.Surjective q)
    (hd : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q)
    (hmetric : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
      ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
        (K.flow.metric t).inner (q p)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p w) =
          F.productInner t p v w)
    (hfib : Function.Injective q ∨
      (∀ p p', q p = q p' ↔ p' = p ∨ p' = (-p.1, p.2)) ∨
      ∃ a : ℝ, ∀ p p', q p = q p' ↔ p' = p ∨ p' = (-p.1, 2 * a - p.2)) :
    Nonempty (M27SphereLineFlowCertificate K) ∨
      Nonempty (M27ProjectivePlaneLineFlowCertificate K) ∨
      Nonempty (M27TwistedSphereLineFlowCertificate K) := by
  rcases hfib with hi | hfib | ⟨a, hfib⟩
  · exact Or.inl ⟨{
      sphere := F
      identification := hd.diffeomorphOfBijective ⟨hi, hq⟩
      metric_transport := hmetric }⟩
  · exact Or.inr (Or.inl ⟨M27ProjectivePlaneLineFlowCertificate.ofCover
      F q hq hd hfib hmetric⟩)
  · let e := cylinderCenterShift (-a)
    let q' := q ∘ e
    have hq' : Function.Surjective q' := hq.comp e.surjective
    have hd' : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q' :=
      fun p => (e.isLocalDiffeomorph p).comp (𝓡 3) M (hd _)
    have hfib' : ∀ p p', q' p = q' p' ↔
        p' = p ∨ p' = m27TwistedProductInvolution p := by
      intro p p'
      change q (e p) = q (e p') ↔ _
      rw [hfib]
      constructor
      · rintro (h | h)
        · exact Or.inl (e.injective h)
        · right
          apply Prod.ext
          · have hh := congrArg Prod.fst h
            change p'.1 = -p.1 at hh ⊢
            exact hh
          · have hh := congrArg Prod.snd h
            change p'.2 - -a = 2 * a - (p.2 - -a) at hh
            change p'.2 = -p.2
            linarith
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · right
          apply Prod.ext
          · rfl
          · change -p.2 - -a = 2 * a - (p.2 - -a)
            ring
    have hm' : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
        ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
          (K.flow.metric t).inner (q' p)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q' p v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q' p w) =
            F.productInner t p v w := by
      intro t ht p v w
      change (K.flow.metric t).inner (q (e p))
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (q ∘ e) p v)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (q ∘ e) p w) = _
      rw [mfderiv_comp_apply p (hd.mdifferentiable (by simp) _)
        (e.contMDiff.mdifferentiable (by simp) _),
        mfderiv_comp_apply p (hd.mdifferentiable (by simp) _)
        (e.contMDiff.mdifferentiable (by simp) _), hmetric t ht]
      exact cylinderCenterShift_productInner F (-a) t p v w
    exact Or.inr (Or.inr ⟨M27TwistedSphereLineFlowCertificate.ofCover
      F q' hq' hd' hfib' hm'⟩)

end PoincareConjecture.AncientCylinderQuotient
