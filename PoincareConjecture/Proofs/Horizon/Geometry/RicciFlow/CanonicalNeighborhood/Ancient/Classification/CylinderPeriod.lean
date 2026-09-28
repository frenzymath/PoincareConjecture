import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Cylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Period.Exclusion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Geometry.Riemannian.SpaceForm
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_calibrated_aperiodic_sphereLine_cover_of_terminal_null
    (P : AncientKappaClassificationServices.{u})
    (K : AncientKappaSolution 3 M) (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric 0).inner x v v = 1)
    (hw : (K.flow.metric 0).inner x w w = 1)
    (hvw : (K.flow.metric 0).inner x v w = 0)
    (hzero : (K.flow.connection 0).curvatureTensor x v w v w = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ (F : M27RoundSphereFamily) (q : UnitTwoSphere × ℝ → M),
      Function.Surjective q ∧ IsCoveringMap q ∧
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q ∧
      (∀ t ≤ 0, ∀ (z : UnitTwoSphere × ℝ)
        (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
        (K.flow.metric t).inner (q z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q z a)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q z b) = F.productInner t z a b) ∧
      (∀ t ≤ 0, ∀ z (a b : TangentSpace (𝓡 2) z),
        (F.metric t).inner z a b =
          (c - 2 * t) * (roundSphereMetric 2).inner z a b) ∧
      ∀ (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) (l : ℝ),
        (∀ z, q (sphereMotion L z.1, z.2 + l) = q z) → l = 0 := by
  obtain ⟨U, hU, hUT, hUc, hUm, hUb, hUchart, hUman, hUs, hUsc,
    B, p, _, hsurj, hcover, hp, hmetric⟩ := K.exists_simplyConnected_covering_solution
  obtain ⟨y, rfl⟩ := hsurj x
  let D := hp.mfderivToContinuousLinearEquiv (by simp) y
  let v' := D.symm v
  let w' := D.symm w
  have hv' : mfderiv (𝓡 3) (𝓡 3) p y v' = v := D.apply_symm_apply v
  have hw' : mfderiv (𝓡 3) (𝓡 3) p y w' = w := D.apply_symm_apply w
  have hunitv : (B.flow.metric 0).inner y v' v' = 1 := by rw [hmetric, hv']; exact hv
  have hunitw : (B.flow.metric 0).inner y w' w' = 1 := by rw [hmetric, hw']; exact hw
  have horth : (B.flow.metric 0).inner y v' w' = 0 := by rw [hmetric, hv', hw']; exact hvw
  have hnull : (B.flow.connection 0).curvatureTensor y v' w' v' w' = 0 := by
    rw [(B.flow.connection 0).curvatureTensor_eq_of_local_isometry (K.flow.connection 0)
      isOpen_univ hp.contMDiff.contMDiffOn (fun z _ => hmetric 0 z) (mem_univ y), hv', hw']
    exact hzero
  obtain ⟨N, hN, hT, hconn, hm, hb, hchart, hman, hsecond, A, ⟨R⟩, e, he⟩ :=
    B.exists_compact_round_product_of_terminal_null P y v' w' hunitv hunitw horth hnull
  let : CompactSpace N := R.compact
  let : SimplyConnectedSpace N :=
    Poincare.Topology.simplyConnectedSpace_of_prod_real_homeomorph e.toHomeomorph
  obtain ⟨c, hc, F, s, hs, hscale⟩ := R.exists_calibrated_roundSphereFamily_diffeomorph
  let d := s.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  let E := d.trans e
  have hE : ∀ t ≤ 0, ∀ (z : UnitTwoSphere × ℝ)
      (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
      (B.flow.metric t).inner (E z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) E z a)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) E z b) = F.productInner t z a b := by
    intro t ht z a b
    have hd (c : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d z c =
          (mfderiv (𝓡 2) (𝓡 2) s z.1 c.1, c.2) := by
      change mfderiv _ _ (Prod.map s id) z c = _
      rw [mfderiv_prodMap (s.mdifferentiable (by simp) _)
        (mdifferentiableAt_id : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id z.2)]
      rw [mfderiv_id]
      rfl
    change (B.flow.metric t).inner (e (d z))
      (mfderiv _ _ (e ∘ d) z a) (mfderiv _ _ (e ∘ d) z b) = _
    rw [mfderiv_comp z (e.mdifferentiable (by simp) _) (d.mdifferentiable (by simp) _)]
    change (B.flow.metric t).inner (e (d z))
      (mfderiv _ _ e (d z) (mfderiv _ _ d z a))
      (mfderiv _ _ e (d z) (mfderiv _ _ d z b)) = _
    rw [he t ht, hd, hd]
    exact congrArg (fun r : ℝ => r + a.2 * b.2) (hs t ht z.1 a.1 b.1)
  let q := p ∘ E
  have hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q := by
    intro z
    exact (E.isLocalDiffeomorph z).comp (𝓡 3) M (hp _)
  refine ⟨c, hc, F, q, hsurj.comp E.surjective,
    hcover.comp_homeomorph E.toHomeomorph, hq, ?_, hscale, ?_⟩
  · intro t ht z a b
    change (K.flow.metric t).inner (p (E z))
      (mfderiv _ _ (p ∘ E) z a) (mfderiv _ _ (p ∘ E) z b) = _
    rw [mfderiv_comp z (hp.mdifferentiable (by simp) _) (E.mdifferentiable (by simp) _)]
    change (K.flow.metric t).inner (p (E z))
      (mfderiv _ _ p (E z) (mfderiv _ _ E z a))
      (mfderiv _ _ p (E z) (mfderiv _ _ E z b)) = _
    rw [← hmetric]
    exact hE t ht z a b
  · intro L l hdeck
    let δ : Equiv.Perm (N × ℝ) :=
      ((s.toEquiv.symm.trans (sphereMotion L).toEquiv).trans s.toEquiv).prodCongr
        (Equiv.addRight l)
    apply AncientCylinderPeriod.translation_eq_zero_of_round_ancient_cover
      K B.flow A.flow R.round_at_all_times e he hp.contMDiff hsurj
      (fun t _ => hmetric t) δ l (fun _ => rfl)
    intro z
    change p (e (s (sphereMotion L (s.symm z.1)), z.2 + l)) = p (e z)
    have h := hdeck (s.symm z.1, z.2)
    change p (e (s (sphereMotion L (s.symm z.1)), z.2 + l)) =
      p (e (s (s.symm z.1), z.2)) at h
    simpa only [s.apply_symm_apply] using h

end PoincareConjecture.AncientKappaSolution
