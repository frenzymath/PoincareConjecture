import PoincareConjecture.Proofs.M32.Cor11_36.Comparison
import PoincareConjecture.Definitions.M32HornSelection

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

noncomputable def restrictCylinderSpace
    {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale : ℝ} {I : Set ℝ} {U V : Set C.carrier}
    (e : GeneralizedFlowCylinder F C origin scale I U) (hVU : V ⊆ U) :
    GeneralizedFlowCylinder F C origin scale I V where
  scale_pos := e.scale_pos
  forward := e.forward
  inverse := e.inverse
  forward_smooth s hs := (e.forward_smooth s hs).mono hVU
  inverse_smooth s hs := (e.inverse_smooth s hs).mono (Set.image_mono hVU)
  left_inverse s hs := (e.left_inverse s hs).mono hVU
  right_inverse s hs := (e.right_inverse s hs).mono (Set.image_mono hVU)
  embedding := e.embedding.comp
    (Topology.IsEmbedding.id.prodMap (Topology.IsEmbedding.inclusion hVU))
  vertical_compatibility s hs x hx := e.vertical_compatibility s hs x (hVU hx)

section Neck

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon delta : ℝ}

private def domainInclusion (he : 0 < epsilon) (hed : epsilon ≤ delta) :
    NeckDomain delta → NeckDomain epsilon :=
  Prod.map id (Set.inclusion (neckInterval_subset he hed))

private theorem domainInclusion_open (he : 0 < epsilon) (hed : epsilon ≤ delta) :
    Topology.IsOpenEmbedding (domainInclusion he hed) :=
  Topology.IsOpenEmbedding.id.prodMap
    (Topology.IsOpenEmbedding.inclusion _ (isOpen_Ioo.preimage continuous_subtype_val))

private def restrictedMap (N : GeneralizedStrongNeck F t epsilon) (hed : epsilon ≤ delta) :
    NeckDomain delta → (F.slice t).carrier :=
  fun z => N.coordinate (domainInclusion N.epsilon_pos hed z)

private theorem restrictedMap_open (N : GeneralizedStrongNeck F t epsilon)
    (hed : epsilon ≤ delta) : Topology.IsOpenEmbedding (restrictedMap N hed) :=
  N.carrier_open.isOpenEmbedding_subtypeVal.comp
    (N.coordinate.isOpenEmbedding.comp (domainInclusion_open N.epsilon_pos hed))

noncomputable def restrictNeckAccuracy (N : GeneralizedStrongNeck F t epsilon)
    (hed : epsilon ≤ delta) : GeneralizedStrongNeck F t delta := by
  let f := restrictedMap N hed
  have hf : Topology.IsOpenEmbedding f := restrictedMap_open N hed
  have hsub : Set.range f ⊆ N.carrier := by
    rintro x ⟨z, rfl⟩
    exact (N.coordinate _).property
  have hmap (z : NeckDomain delta) : f z = N.coordinate_map (z.1, (z.2 : ℝ)) :=
    N.coordinate_map_eq _
  have hinv (z : NeckDomain delta) : N.coordinate_inverse (f z) = (z.1, (z.2 : ℝ)) :=
    N.coordinate_inverse_left _
  refine {
    epsilon_pos := N.epsilon_pos.trans_le hed
    center := N.center
    scalar_center_pos := N.scalar_center_pos
    scale := N.scale
    scale_pos := N.scale_pos
    scale_scalar := N.scale_scalar
    carrier := Set.range f
    carrier_open := hf.isOpen_range
    coordinate := hf.isEmbedding.toHomeomorph
    coordinate_map := N.coordinate_map
    coordinate_map_eq := hmap
    coordinate_map_smooth := N.coordinate_map_smooth.mono
      (Set.prod_mono subset_rfl (neckInterval_subset N.epsilon_pos hed))
    coordinate_inverse := N.coordinate_inverse
    coordinate_inverse_mem := ?_
    coordinate_inverse_left := hinv
    coordinate_inverse_right := fun x hx => N.coordinate_inverse_right x (hsub hx)
    coordinate_inverse_smooth := N.coordinate_inverse_smooth.mono hsub
    central_sphere := N.central_sphere
    central_sphere_eq := N.central_sphere_eq
    center_on_central_sphere := N.center_on_central_sphere
    central_sphere_subset := ?_
    time_cylinder := restrictCylinderSpace N.time_cylinder hsub
    cylinder_identity := fun h x hx => N.cylinder_identity h x (hsub hx)
    metric_comparison := roundCylinderFamilyClose_mono N.epsilon_pos hed
      (fun s hs => hs.2.trans_lt (by norm_num)) N.metric_comparison }
  · rintro x ⟨z, rfl⟩
    rw [hinv]
    exact z.2.property
  · intro x hx
    rw [N.central_sphere_eq] at hx
    obtain ⟨⟨s, a⟩, ⟨_, ha⟩, rfl⟩ := hx
    have ha0 : a = 0 := ha
    subst a
    have hd : 0 < delta⁻¹ := inv_pos.mpr (N.epsilon_pos.trans_le hed)
    exact ⟨(s, ⟨0, by constructor <;> linarith⟩), hmap _⟩

@[simp] theorem restrictNeckAccuracy_center (N : GeneralizedStrongNeck F t epsilon)
    (hed : epsilon ≤ delta) : (restrictNeckAccuracy N hed).center = N.center := rfl

@[simp] theorem restrictNeckAccuracy_central_sphere (N : GeneralizedStrongNeck F t epsilon)
    (hed : epsilon ≤ delta) :
    (restrictNeckAccuracy N hed).central_sphere = N.central_sphere := rfl

@[simp] theorem restrictNeckAccuracy_scale (N : GeneralizedStrongNeck F t epsilon)
    (hed : epsilon ≤ delta) : (restrictNeckAccuracy N hed).scale = N.scale := rfl

theorem restrictNeckAccuracy_carrier_subset (N : GeneralizedStrongNeck F t epsilon)
    (hed : epsilon ≤ delta) : (restrictNeckAccuracy N hed).carrier ⊆ N.carrier := by
  rintro x ⟨z, rfl⟩
  exact (N.coordinate _).property

end Neck

noncomputable def restrictHornCutAccuracy
    {F : GeneralizedRicciFlowData.{u}} {T epsilon delta eta rho : ℝ}
    {E : GeneralizedFlowExtension F T} {horn : StrongHorn E epsilon}
    {N : TerminalStrongNeck E delta} (cut : HornEndCut horn N rho)
    (hde : delta ≤ eta) : HornEndCut horn (restrictNeckAccuracy N hde) rho where
  point := cut.point
  point_mem := cut.point_mem
  carrier := cut.carrier
  component_eq := cut.component_eq
  tail_level := cut.tail_level
  tail_level_nonneg := cut.tail_level_nonneg
  tail_level_lt_one := cut.tail_level_lt_one
  contains_tail := cut.contains_tail
  escapes_compact := cut.escapes_compact
  disjoint_low_curvature := cut.disjoint_low_curvature

def enlargeHornCutRadius
    {F : GeneralizedRicciFlowData.{u}} {T epsilon delta rho sigma : ℝ}
    {E : GeneralizedFlowExtension F T} {horn : StrongHorn E epsilon}
    {N : TerminalStrongNeck E delta} (cut : HornEndCut horn N rho)
    (hr : 0 < rho) (hrs : rho ≤ sigma) : HornEndCut horn N sigma where
  point := cut.point
  point_mem := cut.point_mem
  carrier := cut.carrier
  component_eq := cut.component_eq
  tail_level := cut.tail_level
  tail_level_nonneg := cut.tail_level_nonneg
  tail_level_lt_one := cut.tail_level_lt_one
  contains_tail := cut.contains_tail
  escapes_compact := cut.escapes_compact
  disjoint_low_curvature := cut.disjoint_low_curvature.mono_right (by
    intro x hx
    exact hx.trans (pow_le_pow_left₀ (inv_nonneg.mpr (hr.trans_le hrs).le)
      ((inv_le_inv₀ (hr.trans_le hrs) hr).2 hrs) 2))

theorem deepHornConclusion_mono
    {F : GeneralizedRicciFlowData.{u}} {T epsilon C rho sigma delta eta h : ℝ}
    {E : GeneralizedFlowExtension F T} {horn : StrongHorn E epsilon}
    (D : DeepHornNeckConclusion E epsilon C rho delta horn h)
    (hC : 0 < C) (hr : 0 < rho) (hrs : rho ≤ sigma)
    (hd : 0 < delta) (hde : delta ≤ eta) :
    DeepHornNeckConclusion E epsilon C sigma eta horn h where
  h_pos := D.h_pos
  h_upper := D.h_upper.trans (min_le_min
    (mul_le_mul hrs hde hd.le (hr.trans_le hrs).le)
    (div_le_div_of_nonneg_right hrs (by positivity)))
  deep_neck := by
    intro x hx hR
    obtain ⟨N, hc, hN⟩ := D.deep_neck x hx hR
    exact ⟨restrictNeckAccuracy N hde, hc,
      (restrictNeckAccuracy_carrier_subset N hde).trans hN⟩
  selected_neck := by
    obtain ⟨N, hc, hN, hR, ⟨cut⟩⟩ := D.selected_neck
    exact ⟨restrictNeckAccuracy N hde, hc,
      (restrictNeckAccuracy_carrier_subset N hde).trans hN, hR,
      ⟨enlargeHornCutRadius (restrictHornCutAccuracy cut hde) hr hrs⟩⟩

end PoincareConjecture.M32
