import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapCoordinates










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D



theorem closedModelCapData_exists_cofinalEndChart
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : ClosedModelCapData g) :
    let U : TopologicalSpace.Opens M :=
      { carrier := C.carrier, is_open' := C.carrier_open }
    ∃ e : OpenPartialHomeomorph RoundCylinderSpace U,
      e.source = univ ×ˢ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ ∧
      e.target = (Subtype.val : U → M) ⁻¹' C.end_chart.target ∧
      (∀ z ∈ e.source, (e z).val = C.coordinate_map z) ∧
      (∀ x : U, e.symm x = C.coordinate_inverse x.val) ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
      (∀ d ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
        e.cylinderTail C.epsilon⁻¹ d =
          (Subtype.val : U → M) ⁻¹' (C.region d C.epsilon⁻¹)) ∧
      (∀ d ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
        IsCompact (e.cylinderTail C.epsilon⁻¹ d)ᶜ) := by
  classical
  let U : TopologicalSpace.Opens M :=
    { carrier := C.carrier, is_open' := C.carrier_open }
  change ∃ e : OpenPartialHomeomorph RoundCylinderSpace U, _
  have hU : Nonempty U := ⟨⟨C.carrier_connected.nonempty.choose,
    C.carrier_connected.nonempty.choose_spec⟩⟩
  let f := C.coordinatePartialHomeomorph.symm
  let r : OpenPartialHomeomorph U RoundCylinderSpace := f.subtypeRestr hU
  let e : OpenPartialHomeomorph RoundCylinderSpace U := r.symm
  have hsource : e.source = univ ×ˢ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by
    change (f.subtypeRestr hU).target = _
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target]
    rw [U.openPartialHomeomorphSubtypeCoe_target]
    ext z
    change (z ∈ C.end_chart.source ∧ C.coordinate_map z ∈ C.carrier) ↔ _
    rw [C.end_chart_source]
    exact ⟨fun hz => hz.1,
      fun hz => ⟨hz, C.end_chart_target_subset (C.coordinate_map_mem hz)⟩⟩
  have htarget : e.target = (Subtype.val : U → M) ⁻¹' C.end_chart.target := by
    change (f.subtypeRestr hU).source = _
    exact f.subtypeRestr_source hU
  have hforward : ∀ z ∈ e.source, (e z).val = C.coordinate_map z := by
    intro z hz
    exact f.subtypeRestr_symm_apply hU hz
  have hinverse : ∀ x : U, e.symm x = C.coordinate_inverse x.val :=
    fun _ => rfl
  have he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source := by
    have hmap : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        C.coordinate_map e.source := by
      rw [hsource]
      exact C.coordinate_map_smooth
    have hcomp : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (Subtype.val ∘ e) e.source := hmap.congr hforward
    intro z hz
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U e e.source z).mp (hcomp z hz)
  have hei : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target := by
    have hinc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val : U → M) e.target :=
      contMDiff_subtype_val.contMDiffOn
    have hmaps : MapsTo (Subtype.val : U → M) e.target C.end_chart.target := by
      intro x hx
      simpa only [htarget, mem_preimage] using hx
    exact C.coordinate_inverse_smooth.comp hinc hmaps
  have htail : ∀ d ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
      e.cylinderTail C.epsilon⁻¹ d =
        (Subtype.val : U → M) ⁻¹' (C.region d C.epsilon⁻¹) := by
    intro d hd
    ext x
    rw [e.mem_cylinderTail_iff hsource hd.1 x, htarget, hinverse]
    rfl
  refine ⟨e, hsource, htarget, hforward, hinverse, he, hei, htail, ?_⟩
  intro d hd
  have himage : (Subtype.val : U → M) '' (e.cylinderTail C.epsilon⁻¹ d)ᶜ =
      C.carrier \ C.region d C.epsilon⁻¹ := by
    rw [htail d hd]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  apply Subtype.isCompact_iff.mpr
  rw [himage]
  exact C.isCompact_end_neck_lower_cut hd





theorem closedModelCapData_exists_standardEnd_of_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : ClosedModelCapData g) (hkind : C.model_kind = CapModelKind.euclidean)
    {v : ℝ} (hv : v ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹) :
    let U : TopologicalSpace.Opens M :=
      { carrier := C.carrier, is_open' := C.carrier_open }
    ∃ (Phi : Diffeomorph (𝓡 3) (𝓡 3) U E3 ∞)
      (A : E3 ≃ₗᵢ[ℝ] E3) (r0 : ℝ) (sigma : OpenPartialHomeomorph ℝ ℝ),
      0 < r0 ∧ sigma.source = Ioo v C.epsilon⁻¹ ∧ sigma.target = Ioi r0 ∧
      ContDiffOn ℝ ∞ (sigma : ℝ → ℝ) sigma.source ∧
      ContDiffOn ℝ ∞ sigma.symm sigma.target ∧
      StrictMonoOn (sigma : ℝ → ℝ) sigma.source ∧
      (∀ s ∈ sigma.source, 0 < deriv (sigma : ℝ → ℝ) s) ∧
      (∀ (q : UnitTwoSphere) (s : ℝ) (x : U),
        s ∈ Ioo v C.epsilon⁻¹ →
        x.val = C.coordinate_map (q, s) →
        Phi x = sigma s • (sphereMap A q).val) := by
  classical
  let U : TopologicalSpace.Opens M :=
    { carrier := C.carrier, is_open' := C.carrier_open }
  change ∃ (Phi : Diffeomorph (𝓡 3) (𝓡 3) U E3 ∞), _
  let R := C.model_equivalence
  let : TopologicalSpace R.model := R.model_topology
  let : ChartedSpace E3 R.model := R.model_charted
  let : IsManifold (𝓡 3) ∞ R.model := R.model_manifold
  obtain ⟨F, _, _⟩ := capModelEquivalence_exists_carrierDiffeomorph U R
  have hstd : Nonempty (Diffeomorph (𝓡 3) (𝓡 3) R.model E3 ∞) := by
    have h := R.standard_smooth
    split at h
    · exact h
    · simp_all only [reduceCtorEq]
  obtain ⟨D0⟩ := hstd
  let Phi0 := F.trans D0
  obtain ⟨e, hsource, _, hforward, _, he, hei, _, hend⟩ :=
    closedModelCapData_exists_cofinalEndChart C
  let c := (-C.epsilon⁻¹ + v) / 2
  let η := (v + C.epsilon⁻¹) / 2
  have hc : c ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by
    dsimp only [c]
    constructor <;> linarith [hv.1, hv.2]
  have hη : 0 < η := by
    dsimp only [η]
    linarith [hv.1]
  have hcv : c + η = v := by dsimp only [c, η]; ring
  have hcb : c + η < C.epsilon⁻¹ := by rw [hcv]; exact hv.2
  obtain ⟨Phi, A, r0, sigma, hr0, hsrc, htgt, hs, hsi, hmono, hderiv, hformula⟩ :=
    standardEnd_of_openPartialHomeomorph hS hD Phi0 e hsource he hei hend hc hη hcb
  rw [hcv] at hsrc hformula
  refine ⟨Phi, A, r0, sigma, hr0, hsrc, htgt, hs, hsi, hmono, hderiv, ?_⟩
  intro q s x hs hx
  have hzs : (q, s) ∈ e.source := by
    rw [hsource]
    exact ⟨mem_univ _, hv.1.trans hs.1, hs.2⟩
  have hex : e (q, s) = x := Subtype.ext ((hforward (q, s) hzs).trans hx.symm)
  simpa only [hex] using hformula q s hs

end PoincareConjecture.M25.Topology3D
