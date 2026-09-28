import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Product.CoverFlow











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

theorem normalizedCover_metric (C : M27TwistedSphereLineFlowCertificate K)
    {t : ℝ} (ht : t ≤ 0) (p : UnitTwoSphere × ℝ)
    (hR : 0 < (K.flow.connection t).scalarCurvature (C.cover p))
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
      (K.flow.connection t).scalarCurvature (C.cover p) *
        (C.sphere.metric t).inner (a x)
          (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
            2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w)
    {u : ℝ} (hu : u ≤ 0) :
    (fun z v w => (K.flow.connection t).scalarCurvature (C.cover p) *
      roundCylinderPullback
        (K.flow.metric (t + u / (K.flow.connection t).scalarCurvature (C.cover p)))
        (C.normalizedCover a ((K.flow.connection t).scalarCurvature (C.cover p)) p.2 hR)
        z v w) = EvolvingRoundCylinderMetric u := by
  let R := (K.flow.connection t).scalarCurvature (C.cover p)
  let ℓ := scalarNormalizedCylinderLine R p.2 hR
  let b := a.prodCongr ℓ
  funext z v w
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
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (C.normalizedCover a R p.2 hR) z v =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.cover (b z)
          (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1, v.2 / Real.sqrt R) := by
    change mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (C.cover ∘ b) z v = _
    rw [mfderiv_comp z (C.cover_local_diffeomorph.mdifferentiable (by simp) _)
      (b.mdifferentiable (by simp) _)]
    exact congrArg (fun q =>
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) C.cover (b z) q) (hdb v)
  change R * (K.flow.metric (t + u / R)).inner (C.normalizedCover a R p.2 hR z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (C.normalizedCover a R p.2 hR) z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (C.normalizedCover a R p.2 hR) z w) = _
  rw [hdΦ, hdΦ]
  change R * (K.flow.metric (t + u / R)).inner (C.cover (b z)) _ _ = _
  rw [C.metric_transport _ (add_nonpos ht (div_nonpos_of_nonpos_of_nonneg hu hR.le))]
  change R * ((C.sphere.metric (t + u / R)).inner (a z.1)
    (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1) (mfderiv (𝓡 2) (𝓡 2) a z.1 w.1) +
      (v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = _
  have he := C.sphere_inner_backward ht hu p.1 (a z.1)
    (mfderiv (𝓡 2) (𝓡 2) a z.1 v.1) (mfderiv (𝓡 2) (𝓡 2) a z.1 w.1)
  rw [← C.scalarCurvature_cover ht p] at he
  rw [he, mul_add]
  have hline : R * ((v.2 / Real.sqrt R) * (w.2 / Real.sqrt R)) = v.2 * w.2 := by
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hR.le]
    exact mul_div_cancel₀ _ hR.ne'
  rw [hline, ← mul_assoc, mul_comm R (1 - u), mul_assoc, ha]
  change (1 - u) * (2 * _) + v.2 * w.2 = 2 * (1 - u) * _ + v.2 * w.2
  rw [← mul_assoc, mul_comm (1 - u) 2]
  rfl


noncomputable def strongNeck
    (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hεhalf : epsilon < 1 / 2)
    (p : UnitTwoSphere × ℝ)
    (hR : 0 < (K.flow.connection t).scalarCurvature (C.cover p))
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (ha : ∀ (x : UnitTwoSphere) (v w : TangentSpace (𝓡 2) x),
      (K.flow.connection t).scalarCurvature (C.cover p) *
        (C.sphere.metric t).inner (a x)
          (mfderiv (𝓡 2) (𝓡 2) a x v) (mfderiv (𝓡 2) (𝓡 2) a x w) =
            2 * (Poincare.Geometry.Riemannian.SpaceForm.roundSphereMetric 2).inner x v w)
    (hp : epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover p)) ≤ p.2) :
    StrongEvolvingNeck K t epsilon := by
  let R := (K.flow.connection t).scalarCurvature (C.cover p)
  let e := C.normalizedSlab a hR hp
  have hsource : e.source = univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := rfl
  have hcenter : e (a.symm p.1, 0) = C.cover p := by
    change C.cover (a (a.symm p.1), p.2 + 0 / Real.sqrt R) = C.cover p
    rw [a.apply_symm_apply, zero_div, add_zero, Prod.mk.eta]
  have hcentral : e '' (univ ×ˢ ({0} : Set ℝ)) ⊆ e.target := by
    rintro _ ⟨z, hz, rfl⟩
    apply e.map_source
    rw [hsource]
    have hpos := inv_pos.mpr hε
    exact ⟨hz.1, by simpa only [mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ from
        ⟨neg_neg_of_pos hpos, hpos⟩)⟩
  have hmodel (u : ℝ) (hu : u ≤ 0) :
      (fun z v w => R * roundCylinderPullback (K.flow.metric (t + u / R)) e z v w) =
        EvolvingRoundCylinderMetric u := C.normalizedCover_metric ht p hR a ha hu
  have hscale : (R ^ (-1 / 2 : ℝ))⁻¹ ^ (2 : ℕ) = R := by
    rw [neg_div, Real.rpow_neg hR.le, inv_inv, ← Real.rpow_natCast,
      ← Real.rpow_mul hR.le]
    norm_num [R]
  have hterminal : (fun z v w => R * roundCylinderPullback (K.flow.metric t) e z v w) =
      EvolvingRoundCylinderMetric 0 := by
    simpa only [zero_div, add_zero] using hmodel 0 le_rfl
  let terminal : EpsilonNeck (K.flow.metric t) := {
    epsilon := epsilon
    epsilon_pos := hε
    epsilon_lt_half := hεhalf
    scale := R ^ (-1 / 2 : ℝ)
    scale_pos := Real.rpow_pos_of_pos hR _
    center := C.cover p
    connection := K.flow.connection t
    scalar_center_pos := hR
    scale_eq_scalar := rfl
    carrier := e.target
    carrier_open := e.open_target
    coordinate := neckDomainCoordinates e hsource
    coordinate_map := e
    coordinate_map_eq := fun _ => rfl
    coordinate_map_smooth :=
      (C.normalizedCover_localDiffeomorph a R p.2 hR).contMDiff.contMDiffOn
    coordinate_inverse := e.symm
    coordinate_inverse_mem := fun _ hx => neckDomainCoordinates_inverse_mem e hsource hx
    coordinate_inverse_left := neckDomainCoordinates_inverse_left e hsource
    coordinate_inverse_right := neckDomainCoordinates_inverse_right e hsource
    coordinate_inverse_smooth := C.normalizedSlab_inverse_smooth a hR hp
    central_sphere := e '' (univ ×ˢ ({0} : Set ℝ))
    central_sphere_eq := rfl
    center_on_central_sphere :=
      ⟨(a.symm p.1, 0), ⟨mem_univ _, mem_singleton _⟩, hcenter⟩
    central_sphere_subset := hcentral
    metric_comparison := ⟨by
      rw [hscale, hterminal]
      exact roundCylinderClose_model hε 0⟩ }
  refine {
    time_mem := ht
    center := C.cover p
    duration := R⁻¹
    duration_pos := inv_pos.mpr hR
    normalized_duration := inv_mul_cancel₀ hR.ne'
    terminal_neck := terminal
    terminal_center := rfl
    terminal_epsilon := rfl
    terminal_connection := rfl
    metric_comparison := ?_ }
  change RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0)
    (fun u z v w => R * roundCylinderPullback (K.flow.metric (t + u / R)) e z v w)
  refine ⟨?_, 0, sq_pos_of_pos hε, ?_⟩
  · intro u hu
    dsimp only
    rw [hmodel u hu.2]
    exact (roundCylinderFamilyClose_model hε (Ioc (-1 : ℝ) 0)).1 u hu
  · intro u hu z _
    dsimp only
    rw [hmodel u hu.2, roundCylinderJetErrorSquared_model]


theorem exists_strongEvolvingNeck_of_positive_height
    (C : M27TwistedSphereLineFlowCertificate K)
    {t epsilon : ℝ} (ht : t ≤ 0) (hε : 0 < epsilon) (hεhalf : epsilon < 1 / 2)
    (p : UnitTwoSphere × ℝ)
    (hp : epsilon⁻¹ / Real.sqrt ((K.flow.connection t).scalarCurvature (C.cover p)) ≤ p.2) :
    ∃ N : StrongEvolvingNeck K t epsilon, N.center = C.cover p := by
  obtain ⟨hR, a, ha⟩ := C.exists_scalarNormalized_sphere ht p
  exact ⟨C.strongNeck ht hε hεhalf p hR a ha hp, rfl⟩

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
