import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCuts
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.StandardEndServices
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.Basic














set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D




theorem capModelEquivalence_exists_carrierDiffeomorph
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    {kind : CapModelKind} {p : RealProjectiveThree}
    (U : TopologicalSpace.Opens M)
    (R : CapModelEquivalence kind p (U : Set M)) :
    letI : TopologicalSpace R.model := R.model_topology
    letI : ChartedSpace E3 R.model := R.model_charted
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) U R.model ∞,
      (∀ x : U, F x = R.forward x.val) ∧
      (∀ y : R.model, (F.symm y).val = R.inverse y) := by
  let : TopologicalSpace R.model := R.model_topology
  let : ChartedSpace E3 R.model := R.model_charted
  let F : Diffeomorph (𝓡 3) (𝓡 3) U R.model ∞ :=
    { toFun := fun x => R.forward x.val
      invFun := fun y => ⟨R.inverse y, R.inverse_mem y⟩
      left_inv := fun x => Subtype.ext (R.left_inverse x.val x.property)
      right_inv := R.right_inverse
      contMDiff_toFun :=
        R.forward_smooth.comp_contMDiff contMDiff_subtype_val (fun x => x.property)
      contMDiff_invFun :=
        (ContMDiff.subtypeVal_comp_iff U
          (fun y => ⟨R.inverse y, R.inverse_mem y⟩)).mp
          (contMDiffOn_univ.mp R.inverse_smooth) }
  exact ⟨F, fun _ => rfl, fun _ => rfl⟩





theorem capCertificate_exists_cofinalEndChart
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) :
    let U : TopologicalSpace.Opens M :=
      { carrier := C.carrier, is_open' := C.carrier_open }
    ∃ e : OpenPartialHomeomorph RoundCylinderSpace U,
      e.source = univ ×ˢ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ ∧
      e.target = (Subtype.val : U → M) ⁻¹' C.end_neck.carrier ∧
      (∀ z ∈ e.source, (e z).val = C.end_neck.coordinate_map z) ∧
      (∀ x : U, e.symm x = C.end_neck.coordinate_inverse x.val) ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
      (∀ d ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
        e.cylinderTail C.epsilon⁻¹ d =
          (Subtype.val : U → M) ⁻¹' (C.end_neck.region d C.epsilon⁻¹)) ∧
      (∀ d ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
        IsCompact (e.cylinderTail C.epsilon⁻¹ d)ᶜ) := by
  classical
  let U : TopologicalSpace.Opens M :=
    { carrier := C.carrier, is_open' := C.carrier_open }
  change ∃ e : OpenPartialHomeomorph RoundCylinderSpace U, _
  have hU : Nonempty U := ⟨⟨C.end_neck.center,
    C.end_neck_subset
      (C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere)⟩⟩
  let f := C.end_neck.coordinatePartialHomeomorph.symm
  let r : OpenPartialHomeomorph U RoundCylinderSpace := f.subtypeRestr hU
  let e : OpenPartialHomeomorph RoundCylinderSpace U := r.symm
  have hsource : e.source = univ ×ˢ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by
    change (f.subtypeRestr hU).target = _
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target]
    rw [U.openPartialHomeomorphSubtypeCoe_target]
    ext z
    change (z ∈ C.end_neck.cylinderDomain ∧ C.end_neck.coordinate_map z ∈ C.carrier) ↔ _
    have hdom : z ∈ C.end_neck.cylinderDomain ↔
        z ∈ univ ×ˢ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ := by
      simp only [EpsilonNeck.cylinderDomain, C.end_neck_epsilon]
    exact ⟨fun hz => hdom.mp hz.1,
      fun hz => ⟨hdom.mpr hz, C.end_neck_subset (C.end_neck.coordinate_map_mem (hdom.mpr hz))⟩⟩
  have htarget : e.target = (Subtype.val : U → M) ⁻¹' C.end_neck.carrier := by
    change (f.subtypeRestr hU).source = _
    exact f.subtypeRestr_source hU
  have hforward : ∀ z ∈ e.source, (e z).val = C.end_neck.coordinate_map z := by
    intro z hz
    exact f.subtypeRestr_symm_apply hU hz
  have hinverse : ∀ x : U, e.symm x = C.end_neck.coordinate_inverse x.val :=
    fun _ => rfl
  have he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source := by
    have hmap : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        C.end_neck.coordinate_map e.source := by
      rw [hsource, ← C.end_neck_epsilon]
      exact C.end_neck.coordinate_map_smooth
    have hcomp : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
        (Subtype.val ∘ e) e.source := hmap.congr hforward
    intro z hz
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U e e.source z).mp (hcomp z hz)
  have hei : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target := by
    have hinc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val : U → M) e.target :=
      contMDiff_subtype_val.contMDiffOn
    have hmaps : MapsTo (Subtype.val : U → M) e.target C.end_neck.carrier := by
      intro x hx
      simpa only [htarget, mem_preimage] using hx
    exact C.end_neck.coordinate_inverse_smooth.comp hinc hmaps
  have htail : ∀ d ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹,
      e.cylinderTail C.epsilon⁻¹ d =
        (Subtype.val : U → M) ⁻¹' (C.end_neck.region d C.epsilon⁻¹) := by
    intro d hd
    ext x
    rw [e.mem_cylinderTail_iff hsource hd.1 x, htarget, hinverse]
    rfl
  refine ⟨e, hsource, htarget, hforward, hinverse, he, hei, htail, ?_⟩
  intro d hd
  have himage : (Subtype.val : U → M) '' (e.cylinderTail C.epsilon⁻¹ d)ᶜ =
      C.carrier \ C.end_neck.region d C.epsilon⁻¹ := by
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





theorem capCertificate_exists_standardEnd_of_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) (hkind : C.model_kind = CapModelKind.euclidean)
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
        x.val = C.end_neck.coordinate_map (q, s) →
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
    capCertificate_exists_cofinalEndChart C
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
