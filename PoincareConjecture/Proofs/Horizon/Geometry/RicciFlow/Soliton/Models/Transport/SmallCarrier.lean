import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Models.Transport.Canonical
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Models

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture
open RicciFlow.Splitting
variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
  [MeasurableSpace N] [BorelSpace N] [T2Space N] [T3Space N]
  [SecondCountableTopology N] [ConnectedSpace N]
  {S : GradientShrinkingSolitonData 3 M} {T : GradientShrinkingSolitonData 3 N}
  (G : ShrinkingSolitonFlow S) (H : ShrinkingSolitonFlow T)
  (e : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N)
  (hmetric : ∀ t, t < 0 → ∀ (x : M) (v w : TangentSpace (𝓡 3) x),
    (G.flow.metric t).inner x v w = (H.flow.metric t).inner (e x)
      (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w))

def SphereLineProductCertificate.toSmallCarrier (C : SphereLineProductCertificate H) :
    SphereLineProductCertificate G := by
  letI := C.surface_topology
  letI := C.surface_charted
  letI := C.surface_manifold
  letI := C.product_charted
  letI := C.product_manifold
  let D := C.toSphereLineProductData.canonicalProductDiffeomorph
  let f := D.trans (C.product_equiv.symm.trans e.symm)
  let s := Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞
  apply productSphereLineCertificateOfRawProduct G s
    (RoundCylinderSurface.metric s) (RoundCylinderSurface.connection s)
    (fun t _ => RoundCylinderSurface.round s t) (RoundCylinderSurface.inner s) f
  intro t ht z v w
  rw [hmetric t ht, C.flow_isometric_to_product t ht]
  have heq : C.product_equiv ∘ (e ∘ f) = D := by
    funext z
    change C.product_equiv (e (e.symm (C.product_equiv.symm (D z)))) = D z
    rw [e.apply_symm_apply, C.product_equiv.apply_symm_apply]
  have hd (a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      mfderiv (𝓡 3) (𝓡 3) C.product_equiv (e (f z))
        (mfderiv (𝓡 3) (𝓡 3) e (f z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z a)) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) D z a := by
    have h := mfderiv_comp z
      (C.product_equiv.contMDiff.mdifferentiable (by simp) _)
      ((e.contMDiff.comp f.contMDiff).mdifferentiable (by simp) z)
    rw [mfderiv_comp z (e.contMDiff.mdifferentiable (by simp) _)
      (f.contMDiff.mdifferentiable (by simp) z), heq] at h
    exact congrArg (fun L => L a) h.symm
  rw [hd, hd]
  have hp : C.product_equiv (e (f z)) = D z := congrFun heq z
  rw [hp, C.toSphereLineProductData.canonicalProductDiffeomorph_inner t ht,
    RoundCylinderSurface.inner s t ht]
  rfl

def QuotientSphereLineCertificate.toSmallCarrier (C : QuotientSphereLineCertificate H) :
    QuotientSphereLineCertificate G := by
  letI := C.cover_topology
  letI := C.cover_charted
  letI := C.cover_manifold
  letI := C.product.surface_topology
  letI := C.product.surface_charted
  letI := C.product.surface_manifold
  letI := C.product.product_charted
  letI := C.product.product_manifold
  letI := C.quotient_topology
  letI := C.quotient_charted
  letI := C.quotient_manifold
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (UnitTwoSphere × ℝ) :=
    RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  letI : IsManifold (𝓡 3) ∞ (UnitTwoSphere × ℝ) :=
    RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let a := RiemannianMetric.lineProductDiffeomorph (n := 2) (M := UnitTwoSphere)
  let D := C.product.canonicalProductDiffeomorph
  let b := a.symm.trans D
  let τ : (C.product.surface × ℝ) ≃ₘ⟮𝓡 3, 𝓡 3⟯ (C.product.surface × ℝ) :=
    { toFun := C.involution
      invFun := C.involution
      left_inv := C.involution_involutive
      right_inv := C.involution_involutive
      contMDiff_toFun := C.involution_smooth
      contMDiff_invFun := C.involution_smooth }
  let deck := b.trans (τ.trans b.symm)
  have hdeck (z : UnitTwoSphere × ℝ) : deck z = b.symm (C.involution (b z)) := rfl
  have hdeckdeck : Function.Involutive deck := by
    intro z
    rw [hdeck, hdeck, b.apply_symm_apply, C.involution_involutive, b.symm_apply_apply]
  have hdeckfree (z : UnitTwoSphere × ℝ) : deck z ≠ z := by
    intro hz
    have h := congrArg b hz
    rw [hdeck, b.apply_symm_apply] at h
    exact C.involution_free (b z) h
  let eq := Classical.choose C.flow_isometric_to_quotient
  have hqmetric := Classical.choose_spec C.flow_isometric_to_quotient
  let projection : UnitTwoSphere × ℝ → M :=
    e.symm ∘ eq.symm ∘ C.quotient_map ∘ b
  have hp : ContMDiff (𝓡 3) (𝓡 3) ∞ projection :=
    e.symm.contMDiff.comp (eq.symm.contMDiff.comp
      (C.quotient_map_smooth.comp b.contMDiff))
  have hsurj : Function.Surjective projection :=
    e.symm.surjective.comp (eq.symm.surjective.comp
      (C.quotient_map_surjective.comp b.surjective))
  have hfiber (z w : UnitTwoSphere × ℝ) :
      projection z = projection w ↔ w = z ∨ w = deck z := by
    have hew : projection z = projection w ↔ C.quotient_map (b z) = C.quotient_map (b w) :=
      ⟨fun h => eq.symm.injective (e.symm.injective h),
        fun h => congrArg (fun q => e.symm (eq.symm q)) h⟩
    rw [hew, C.quotient_fiber_eq_orbit]
    constructor
    · rintro (he | he)
      · exact Or.inl (b.injective he)
      · right
        apply b.injective
        change b w = b (deck z)
        rw [hdeck, b.apply_symm_apply]
        exact he
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (by rw [hdeck, b.apply_symm_apply])
  let s := Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞
  apply quotientSphereLineCertificateOfRawProduct G s
    (RoundCylinderSurface.metric s) (RoundCylinderSurface.connection s)
    (fun t _ => RoundCylinderSurface.round s t) (RoundCylinderSurface.inner s)
    a deck hdeckdeck hdeckfree projection hp hsurj hfiber
  intro t ht z v w
  let f : UnitTwoSphere × ℝ → M := projection ∘ a
  have hf : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f := hp.comp a.contMDiff
  have heq : eq ∘ (e ∘ f) = C.quotient_map ∘ D := by
    funext z
    change eq (e (e.symm (eq.symm (C.quotient_map (D (a.symm (a z))))))) =
      C.quotient_map (D z)
    rw [a.symm_apply_apply, e.apply_symm_apply, eq.apply_symm_apply]
  rw [hmetric t ht, hqmetric t ht]
  have hd (u : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z) :
      mfderiv (𝓡 3) (𝓡 3) eq (e (f z))
        (mfderiv (𝓡 3) (𝓡 3) e (f z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f z u)) =
      mfderiv (𝓡 3) (𝓡 3) C.quotient_map (D z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) D z u) := by
    have h := mfderiv_comp z (eq.contMDiff.mdifferentiable (by simp) _)
      ((e.contMDiff.comp hf).mdifferentiable (by simp) z)
    rw [mfderiv_comp z (e.contMDiff.mdifferentiable (by simp) _)
      (hf.mdifferentiable (by simp) z), heq,
      mfderiv_comp z (C.quotient_map_smooth.mdifferentiable (by simp) _)
        (D.contMDiff.mdifferentiable (by simp) z)] at h
    exact congrArg (fun L => L u) h.symm
  change (C.quotient_metric t).inner (eq (e (f z))) _ _ = _
  rw [hd, hd]
  have hz : eq (e (f z)) = C.quotient_map (D z) := congrFun heq z
  rw [hz, ← C.quotient_metric_pullback t ht,
    C.product.canonicalProductDiffeomorph_inner t ht]
  rfl

include e hmetric in
theorem CompactRoundShrinkingModel.toSmallCarrier (C : CompactRoundShrinkingModel H) :
    CompactRoundShrinkingModel G := by
  let : CompactSpace N := C.compact
  refine ⟨e.toHomeomorph.symm.compactSpace, ?_⟩
  intro t ht
  obtain ⟨k, hk, hround⟩ := C.round_at_time t ht
  refine ⟨k, hk, ?_⟩
  intro x v w hv hw hvw
  have hcurv := (G.flow.connection t).curvatureTensor_eq_of_local_isometry
    (H.flow.connection t) isOpen_univ e.contMDiff.contMDiffOn
    (fun x _ v w => hmetric t ht x v w) (Set.mem_univ x) v w v w
  have hr := hround (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
    (mfderiv (𝓡 3) (𝓡 3) e x w)
    ((hmetric t ht x v v).symm.trans hv) ((hmetric t ht x w w).symm.trans hw)
    ((hmetric t ht x v w).symm.trans hvw)
  simpa only [LeviCivitaData.sectionalCurvature, hmetric t ht, hcurv] using hr

def ThreeDimensionalSolitonModel.toSmallCarrier (C : ThreeDimensionalSolitonModel T H) :
    ThreeDimensionalSolitonModel S G :=
  match C with
  | .compactRound B => .compactRound (B.toSmallCarrier G H e hmetric)
  | .sphereLine B => .sphereLine (B.toSmallCarrier G H e hmetric)
  | .quotientSphereLine B => .quotientSphereLine (B.toSmallCarrier G H e hmetric)

end PoincareConjecture
