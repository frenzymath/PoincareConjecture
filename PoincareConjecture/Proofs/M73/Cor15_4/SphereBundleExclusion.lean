import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Set

universe u

namespace PoincareConjecture

noncomputable def m73UnitCircleHomeomorph : Circle ≃ₜ UnitCircle where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr z.1,
    mem_sphere_zero_iff_norm.mpr (by
      rw [LinearIsometryEquiv.norm_map, z.norm_coe])⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr.symm z,
    mem_sphere_zero_iff_norm.mpr (by
      rw [LinearIsometryEquiv.norm_map]
      exact mem_sphere_zero_iff_norm.mp z.property)⟩
  left_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply z)
  right_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply z)
  continuous_toFun :=
    (Complex.orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val).subtype_mk
      (fun z => mem_sphere_zero_iff_norm.mpr (by
        simp only [Function.comp_apply]
        rw [LinearIsometryEquiv.norm_map]
        exact mem_sphere_zero_iff_norm.mp z.property))
  continuous_invFun :=
    (Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val).subtype_mk
      (fun z => mem_sphere_zero_iff_norm.mpr (by
        change ‖Complex.orthonormalBasisOneI.repr.symm z.1‖ = 1
        rw [LinearIsometryEquiv.norm_map]
        exact mem_sphere_zero_iff_norm.mp z.property))

theorem m73UnitCircle_covering :
    IsCoveringMap (m73UnitCircleHomeomorph ∘ Circle.exp) := by
  exact Circle.isCoveringMap_exp.homeomorph_comp m73UnitCircleHomeomorph

private noncomputable def SurgerySphereBundle.localHomeomorph
    {C : GeneralizedSliceCarrier.{u}} (B : SurgerySphereBundle C)
    {U : Set UnitCircle} (hU : IsOpen U)
    (f : C.carrier → UnitTwoSphere × UnitCircle)
    (g : UnitTwoSphere × UnitCircle → C.carrier)
    (himage : f '' (B.projection ⁻¹' U) = Set.univ ×ˢ U)
    (hleft : Set.LeftInvOn g f (B.projection ⁻¹' U))
    (hright : Set.LeftInvOn f g (Set.univ ×ˢ U))
    (hsmooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ f
      (B.projection ⁻¹' U))
    (hsmooth' : ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ g
      (Set.univ ×ˢ U)) :
    OpenPartialHomeomorph C.carrier (UnitTwoSphere × UnitCircle) := by
  let e : PartialEquiv C.carrier (UnitTwoSphere × UnitCircle) :=
    { toFun := f
      invFun := g
      source := B.projection ⁻¹' U
      target := Set.univ ×ˢ U
      map_source' := by
        intro x hx
        rw [← himage]
        exact ⟨x, hx, rfl⟩
      map_target' := by
        intro z hz
        rw [← himage] at hz
        obtain ⟨x, hx, hxf⟩ := hz
        rw [← hxf, hleft hx]
        exact hx
      left_inv' := by
        intro x hx
        exact hleft hx
      right_inv' := by
        intro z hz
        exact hright hz }
  exact
    { toPartialEquiv := e
      continuousOn_toFun := hsmooth.continuousOn
      continuousOn_invFun := hsmooth'.continuousOn
      open_source := hU.preimage B.projection_continuous
      open_target := isOpen_univ.prod hU }

private theorem SurgerySphereBundle.projection_isOpenMap
    {C : GeneralizedSliceCarrier.{u}} (B : SurgerySphereBundle C) :
    IsOpenMap B.projection := by
  intro s hs
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨x, hxs, hxy⟩ := hy
  obtain ⟨U, hU, hyU, f, g, himage, hleft, hright, hsmooth, hsmooth', hproj⟩ :=
    B.local_trivialization y
  let V : Set C.carrier := s ∩ B.projection ⁻¹' U
  have hV : IsOpen V := hs.inter (hU.preimage B.projection_continuous)
  have hVsub : V ⊆ B.projection ⁻¹' U := inter_subset_right
  let e := B.localHomeomorph hU f g himage hleft hright hsmooth hsmooth'
  have heopen : IsOpen (e '' V) := e.isOpen_image_of_subset_source hV hVsub
  have hproj_image : B.projection '' V =
      Prod.snd '' (e '' V) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
      exact hproj x hx.2
    · rintro ⟨z, ⟨x, hx, hxe⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      rw [← hxe]
      exact (hproj x hx.2).symm
  have hopen : IsOpen (B.projection '' V) := by
    rw [hproj_image]
    exact isOpenMap_snd _ heopen
  apply Filter.mem_of_superset (hopen.mem_nhds ?_) (image_mono inter_subset_left)
  refine ⟨x, ⟨hxs, ?_⟩, hxy⟩
  change B.projection x ∈ U
  rw [hxy]
  exact hyU

theorem SurgerySphereBundle.not_simplyConnectedSpace
    {C : GeneralizedSliceCarrier.{u}} (B : SurgerySphereBundle C)
    (hc : IsCompact (Set.univ : Set C.carrier)) :
    ¬ SimplyConnectedSpace C.carrier := by
  intro hsc
  let q : ℝ → UnitCircle := m73UnitCircleHomeomorph ∘ Circle.exp
  have hq : IsCoveringMap q := m73UnitCircle_covering
  let : LocallyPathConnectedSpace C.carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier
  let : SimplyConnectedSpace C.carrier := hsc
  obtain ⟨x₀, hx₀⟩ := B.projection_surjective (q 0)
  obtain ⟨L, hL, _⟩ := hq.existsUnique_continuousMap_lifts
    ⟨B.projection, B.projection_continuous⟩ x₀ 0 hx₀.symm
  have hLq (x : C.carrier) : q (L x) = B.projection x := by
    exact congrFun hL.2 x
  let R : Set ℝ := Set.range L
  have hRcompact : IsCompact R := by
    simpa only [Set.image_univ] using hc.image L.continuous
  have hRnonempty : R.Nonempty := ⟨L x₀, ⟨x₀, rfl⟩⟩
  have hRopen : IsOpen R := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨x, rfl⟩ := ht
    obtain ⟨e, he, hqe⟩ := hq.isLocalHomeomorph (L x)
    let W : Set C.carrier := L ⁻¹' e.source
    have hW : IsOpen W := e.open_source.preimage L.continuous
    have hpW : IsOpen (B.projection '' W) := B.projection_isOpenMap W hW
    have hV : IsOpen (e.source ∩ q ⁻¹' (B.projection '' W)) :=
      e.open_source.inter (hpW.preimage hq.continuous)
    have hxV : L x ∈ e.source ∩ q ⁻¹' (B.projection '' W) :=
      ⟨he, ⟨x, he, (hLq x).symm⟩⟩
    apply Filter.mem_of_superset (hV.mem_nhds hxV)
    rintro t ⟨htsource, y, hyW, hyt⟩
    refine ⟨y, e.injOn hyW htsource ?_⟩
    rw [← hqe, hLq y, hyt]
  have hRclosed : IsClosed R := hRcompact.isClosed
  have hclopen : IsClopen R := ⟨hRclosed, hRopen⟩
  have hRuniv : R = Set.univ := IsClopen.eq_univ hclopen hRnonempty
  have hcompactReal : CompactSpace ℝ := isCompact_univ_iff.mp (hRuniv ▸ hRcompact)
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) hcompactReal

end PoincareConjecture
