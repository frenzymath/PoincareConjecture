import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Quotient.Normalization











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M27TwistedSphereLineFlowCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}


noncomputable def normalizedCover (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (R s : ℝ) (hR : 0 < R) : RoundCylinderSpace → M :=
  C.cover ∘ a.prodCongr (scalarNormalizedCylinderLine R s hR)

theorem normalizedCover_localDiffeomorph (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    (R s : ℝ) (hR : 0 < R) :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (C.normalizedCover a R s hR) := by
  intro z
  exact ((a.prodCongr (scalarNormalizedCylinderLine R s hR)).isLocalDiffeomorph z).comp
    (𝓡 3) M (C.cover_local_diffeomorph _)

theorem normalizedCover_injOn (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {R s epsilon : ℝ} (hR : 0 < R) (hs : epsilon⁻¹ / Real.sqrt R ≤ s) :
    InjOn (C.normalizedCover a R s hR) (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) := by
  let b := a.prodCongr (scalarNormalizedCylinderLine R s hR)
  have hpos (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) :
      0 < (b z).2 := by
    change 0 < s + z.2 / Real.sqrt R
    have h := div_lt_div_of_pos_right hz.2.1 (Real.sqrt_pos.mpr hR)
    rw [neg_div] at h
    linarith
  intro z hz w hw heq
  rcases (C.cover_fibers (b z) (b w)).mp heq with h | h
  · exact b.injective h.symm
  · have hline : (b w).2 = -(b z).2 := congrArg Prod.snd h
    have hzpos := hpos z hz
    have hwpos := hpos w hw
    linarith


noncomputable def normalizedSlab (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {R s epsilon : ℝ} (hR : 0 < R) (hs : epsilon⁻¹ / Real.sqrt R ≤ s) :
    OpenPartialHomeomorph RoundCylinderSpace M :=
  OpenPartialHomeomorph.ofContinuousOpen
    ((C.normalizedCover_injOn a hR hs).toPartialEquiv _ _)
    (C.normalizedCover_localDiffeomorph a R s hR).contMDiff.continuous.continuousOn
    (C.normalizedCover_localDiffeomorph a R s hR).isOpenMap
    (isOpen_univ.prod isOpen_Ioo)

@[simp] theorem normalizedSlab_apply (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {R s epsilon : ℝ} (hR : 0 < R) (hs : epsilon⁻¹ / Real.sqrt R ≤ s)
    (z : RoundCylinderSpace) :
    C.normalizedSlab a hR hs z = C.normalizedCover a R s hR z := rfl

@[simp] theorem normalizedSlab_source (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {R s epsilon : ℝ} (hR : 0 < R) (hs : epsilon⁻¹ / Real.sqrt R ≤ s) :
    (C.normalizedSlab a hR hs).source = univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := rfl

theorem normalizedSlab_inverse_smooth (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {R s epsilon : ℝ} (hR : 0 < R) (hs : epsilon⁻¹ / Real.sqrt R ≤ s) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (C.normalizedSlab a hR hs).symm (C.normalizedSlab a hR hs).target := by
  let e := C.normalizedSlab a hR hs
  intro x hx
  let hf := C.normalizedCover_localDiffeomorph a R s hR (e.symm x)
  have he : C.normalizedCover a R s hR (e.symm x) = x := e.right_inv hx
  have hlocal := hf.localInverse_contMDiffAt
  rw [he] at hlocal
  apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [e.open_target.mem_nhds hx,
    (e.continuousAt_symm hx).preimage_mem_nhds
      (hf.localInverse.open_target.mem_nhds hf.localInverse_mem_target)] with y hy hlocaly
  have h := hf.localInverse_left_inv hlocaly
  have hey : C.normalizedCover a R s hR (e.symm y) = y := e.right_inv hy
  rw [hey] at h
  exact h.symm

theorem normalizedCover_image_interval (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {R : ℝ} (hR : 0 < R) (s l u : ℝ) :
    C.normalizedCover a R s hR '' (univ ×ˢ Ioo l u) =
      C.cover '' (univ ×ˢ Ioo (s + l / Real.sqrt R) (s + u / Real.sqrt R)) := by
  have hsqrt := Real.sqrt_pos.mpr hR
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(a z.1, s + z.2 / Real.sqrt R), ⟨mem_univ _, ?_⟩, rfl⟩
    have hl := div_lt_div_of_pos_right hz.2.1 hsqrt
    have hu := div_lt_div_of_pos_right hz.2.2 hsqrt
    constructor <;> dsimp only <;> linarith
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(a.symm z.1, (z.2 - s) * Real.sqrt R), ⟨mem_univ _, ?_⟩, ?_⟩
    · constructor
      · exact (div_lt_iff₀ hsqrt).mp (by linarith [hz.2.1])
      · exact (lt_div_iff₀ hsqrt).mp (by linarith [hz.2.2])
    · change C.cover (a (a.symm z.1), s + (z.2 - s) * Real.sqrt R / Real.sqrt R) =
        C.cover z
      rw [a.apply_symm_apply, mul_div_cancel_right₀ _ hsqrt.ne', add_sub_cancel,
        Prod.mk.eta]

theorem normalizedCover_image_sphere (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {R : ℝ} (hR : 0 < R) (s : ℝ) :
    C.normalizedCover a R s hR '' (univ ×ˢ ({0} : Set ℝ)) =
      C.cover '' (univ ×ˢ ({s} : Set ℝ)) := by
  ext x
  constructor
  · rintro ⟨⟨q, z⟩, ⟨_, hz⟩, rfl⟩
    obtain rfl : z = 0 := hz
    refine ⟨(a q, s), ⟨mem_univ _, mem_singleton _⟩, ?_⟩
    change C.cover (a q, s) = C.cover (a q, s + 0 / Real.sqrt R)
    rw [zero_div, add_zero]
  · rintro ⟨⟨q, z⟩, ⟨_, hz⟩, rfl⟩
    have hzs : z = s := hz
    subst z
    refine ⟨(a.symm q, 0), ⟨mem_univ _, mem_singleton _⟩, ?_⟩
    change C.cover (a (a.symm q), s + 0 / Real.sqrt R) = C.cover (q, s)
    rw [a.apply_symm_apply, zero_div, add_zero]

theorem normalizedSlab_target (C : M27TwistedSphereLineFlowCertificate K)
    (a : UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere)
    {R s epsilon : ℝ} (hR : 0 < R) (hs : epsilon⁻¹ / Real.sqrt R ≤ s) :
    (C.normalizedSlab a hR hs).target =
      C.cover '' (univ ×ˢ Ioo (s - epsilon⁻¹ / Real.sqrt R)
        (s + epsilon⁻¹ / Real.sqrt R)) := by
  rw [← (C.normalizedSlab a hR hs).image_source_eq_target]
  change C.normalizedCover a R s hR '' (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) = _
  rw [C.normalizedCover_image_interval, neg_div, ← sub_eq_add_neg]

end PoincareConjecture.M27TwistedSphereLineFlowCertificate
