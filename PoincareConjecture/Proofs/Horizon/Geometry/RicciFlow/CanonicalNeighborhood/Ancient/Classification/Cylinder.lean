import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Product
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Surface.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.UniversalCover
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Product

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

theorem calibrated_sphereLineFlowCertificate_of_terminal_null [SimplyConnectedSpace M]
    (P : AncientKappaClassificationServices.{u})
    (K : AncientKappaSolution 3 M) (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric 0).inner x v v = 1)
    (hw : (K.flow.metric 0).inner x w w = 1)
    (hvw : (K.flow.metric 0).inner x v w = 0)
    (hzero : (K.flow.connection 0).curvatureTensor x v w v w = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : M27SphereLineFlowCertificate K,
      ∀ t ≤ 0, ∀ z (a b : TangentSpace (𝓡 2) z),
        (C.sphere.metric t).inner z a b =
          (c - 2 * t) * (roundSphereMetric 2).inner z a b := by
  obtain ⟨N, hN, hT, hconn, hm, hb, hchart, hman, hsecond, A, ⟨R⟩, e, he⟩ :=
    K.exists_compact_round_product_of_terminal_null P x v w hv hw hvw hzero
  let : SimplyConnectedSpace N :=
    Poincare.Topology.simplyConnectedSpace_of_prod_real_homeomorph e.toHomeomorph
  obtain ⟨c, hc, F, q, hq, hscale⟩ := R.exists_calibrated_roundSphereFamily_diffeomorph
  let d := q.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  refine ⟨c, hc, { sphere := F, identification := d.trans e, metric_transport := ?_ },
    hscale⟩
  intro t ht z a b
  have hd (c : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d z c =
        (mfderiv (𝓡 2) (𝓡 2) q z.1 c.1, c.2) := by
    change mfderiv _ _ (Prod.map q id) z c = _
    rw [mfderiv_prodMap (q.mdifferentiable (by simp) _)
      (mdifferentiableAt_id : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) id z.2)]
    rw [mfderiv_id]
    rfl
  change (K.flow.metric t).inner (e (d z))
    (mfderiv _ _ (e ∘ d) z a) (mfderiv _ _ (e ∘ d) z b) = _
  rw [mfderiv_comp z (e.mdifferentiable (by simp) _) (d.mdifferentiable (by simp) _)]
  change (K.flow.metric t).inner (e (d z))
    (mfderiv _ _ e (d z) (mfderiv _ _ d z a))
    (mfderiv _ _ e (d z) (mfderiv _ _ d z b)) = _
  rw [he t ht, hd, hd]
  exact congrArg (fun s : ℝ => s + a.2 * b.2) (hq t ht z.1 a.1 b.1)

theorem sphereLineFlowCertificate_of_terminal_null [SimplyConnectedSpace M]
    (P : AncientKappaClassificationServices.{u})
    (K : AncientKappaSolution 3 M) (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric 0).inner x v v = 1)
    (hw : (K.flow.metric 0).inner x w w = 1)
    (hvw : (K.flow.metric 0).inner x v w = 0)
    (hzero : (K.flow.connection 0).curvatureTensor x v w v w = 0) :
    Nonempty (M27SphereLineFlowCertificate K) := by
  obtain ⟨_, _, C, _⟩ :=
    K.calibrated_sphereLineFlowCertificate_of_terminal_null P x v w hv hw hvw hzero
  exact ⟨C⟩

theorem exists_calibrated_sphereLine_cover_of_terminal_null
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
      ∀ t ≤ 0, ∀ z (a b : TangentSpace (𝓡 2) z),
        (F.metric t).inner z a b =
          (c - 2 * t) * (roundSphereMetric 2).inner z a b := by
  obtain ⟨N, hN, hT, hconn, hm, hb, hchart, hman, hsecond, hsimple,
    L, p, _, hsurj, hcover, hp, hmetric⟩ := K.exists_simplyConnected_covering_solution
  obtain ⟨y, rfl⟩ := hsurj x
  let D := hp.mfderivToContinuousLinearEquiv (by simp) y
  let v' := D.symm v
  let w' := D.symm w
  have hv' : mfderiv (𝓡 3) (𝓡 3) p y v' = v := D.apply_symm_apply v
  have hw' : mfderiv (𝓡 3) (𝓡 3) p y w' = w := D.apply_symm_apply w
  have hunitv : (L.flow.metric 0).inner y v' v' = 1 := by rw [hmetric, hv']; exact hv
  have hunitw : (L.flow.metric 0).inner y w' w' = 1 := by rw [hmetric, hw']; exact hw
  have horth : (L.flow.metric 0).inner y v' w' = 0 := by rw [hmetric, hv', hw']; exact hvw
  have hnull : (L.flow.connection 0).curvatureTensor y v' w' v' w' = 0 := by
    rw [(L.flow.connection 0).curvatureTensor_eq_of_local_isometry (K.flow.connection 0)
      isOpen_univ hp.contMDiff.contMDiffOn (fun z _ => hmetric 0 z) (mem_univ y), hv', hw']
    exact hzero
  obtain ⟨c, hc, C, hscale⟩ :=
    L.calibrated_sphereLineFlowCertificate_of_terminal_null P y v' w' hunitv hunitw horth hnull
  let q := p ∘ C.identification
  have hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q := by
    intro z
    exact (C.identification.isLocalDiffeomorph z).comp (𝓡 3) M (hp _)
  refine ⟨c, hc, C.sphere, q, hsurj.comp C.identification.surjective,
    hcover.comp_homeomorph C.identification.toHomeomorph, hq, ?_, hscale⟩
  intro t ht z a b
  change (K.flow.metric t).inner (p (C.identification z))
    (mfderiv _ _ (p ∘ C.identification) z a)
    (mfderiv _ _ (p ∘ C.identification) z b) = _
  rw [mfderiv_comp z (hp.mdifferentiable (by simp) _)
    (C.identification.mdifferentiable (by simp) _)]
  change (K.flow.metric t).inner (p (C.identification z))
    (mfderiv _ _ p (C.identification z) (mfderiv _ _ C.identification z a))
    (mfderiv _ _ p (C.identification z) (mfderiv _ _ C.identification z b)) = _
  rw [← hmetric]
  exact C.metric_transport t ht z a b

theorem exists_sphereLine_cover_of_terminal_null
    (P : AncientKappaClassificationServices.{u})
    (K : AncientKappaSolution 3 M) (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (K.flow.metric 0).inner x v v = 1)
    (hw : (K.flow.metric 0).inner x w w = 1)
    (hvw : (K.flow.metric 0).inner x v w = 0)
    (hzero : (K.flow.connection 0).curvatureTensor x v w v w = 0) :
    ∃ (F : M27RoundSphereFamily) (q : UnitTwoSphere × ℝ → M),
      Function.Surjective q ∧ IsCoveringMap q ∧
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q ∧
      ∀ t ≤ 0, ∀ (z : UnitTwoSphere × ℝ)
        (a b : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
        (K.flow.metric t).inner (q z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q z a)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q z b) = F.productInner t z a b := by
  obtain ⟨_, _, F, q, hs, hc, hl, hm, _⟩ :=
    K.exists_calibrated_sphereLine_cover_of_terminal_null P x v w hv hw hvw hzero
  exact ⟨F, q, hs, hc, hl, hm⟩

end PoincareConjecture.AncientKappaSolution
