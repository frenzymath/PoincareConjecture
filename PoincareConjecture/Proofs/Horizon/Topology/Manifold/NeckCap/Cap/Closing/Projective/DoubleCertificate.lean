import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Certificate
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.ProjectiveModel
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.Transport












noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.SmoothProjectiveDoubleModel

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



def of_collar
    {Q : Type u} [TopologicalSpace Q] [ChartedSpace E3 Q]
    (hcompact : IsCompact (univ : Set Q)) (hconnected : IsConnected (univ : Set Q))
    {p₁ p₂ : RealProjectiveThree} {U V : Set Q}
    (S₁ : StandardPuncturedProjectiveCover Q p₁ U)
    (S₂ : StandardPuncturedProjectiveCover Q p₂ V)
    (hdisjoint : Disjoint U V)
    (c : OpenPartialHomeomorph RoundCylinderSpace Q)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hU : ∀ y ∈ c.target, y ∈ U ↔ (c.symm y).2 < 0)
    (hV : ∀ y ∈ c.target, y ∈ V ↔ 0 < (c.symm y).2)
    (hcover : U ∪ V ∪ c '' (univ ×ˢ ({0} : Set ℝ)) = univ) :
    SmoothProjectiveDoubleModel Q := by
  let R : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
    toEquiv := (Equiv.refl UnitTwoSphere).prodCongr
      (Homeomorph.smulOfNeZero δ hδ.ne').toEquiv
    contMDiff_toFun := by
      change ContMDiff CylModel CylModel ∞ (fun z : RoundCylinderSpace => (z.1, δ * z.2))
      exact contMDiff_fst.prodMk
        (((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => δ)).mul contDiff_id).contMDiff.comp contMDiff_snd)
    contMDiff_invFun := by
      change ContMDiff CylModel CylModel ∞ (fun z : RoundCylinderSpace => (z.1, δ⁻¹ * z.2))
      exact contMDiff_fst.prodMk
        (((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => δ⁻¹)).mul contDiff_id).contMDiff.comp contMDiff_snd) }
  let e := R.toHomeomorph.toOpenPartialHomeomorph.trans c
  have heq (z : RoundCylinderSpace) : e z = c (z.1, δ * z.2) := rfl
  have hscaled (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
      (z.1, δ * z.2) ∈ c.source := by
    apply hsource
    refine ⟨mem_univ _, ?_, ?_⟩
    · nlinarith [hz.2.1]
    · nlinarith [hz.2.2]
  have hes : univ ×ˢ Ioo (-1 : ℝ) 1 ⊆ e.source :=
    fun z hz => ⟨mem_univ _, hscaled z hz⟩
  have he : ContMDiffOn CylModel (𝓡 3) ∞ e e.source :=
    hc.comp R.contMDiff.contMDiffOn inter_subset_right
  have hei : ContMDiffOn (𝓡 3) CylModel ∞ e.symm e.target :=
    R.symm.contMDiff.comp_contMDiffOn (hci.mono inter_subset_left)
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ c.source :=
    hsource ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hsph : e '' (univ ×ˢ ({0} : Set ℝ)) = c '' (univ ×ˢ ({0} : Set ℝ)) := by
    apply image_congr
    rintro ⟨q, t⟩ ⟨_, ht⟩
    have ht0 : t = 0 := ht
    subst t
    simp only [heq, mul_zero]
  let E : PartialDiffeomorph CylModel (𝓡 3) RoundCylinderSpace Q ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := he
    contMDiffOn_invFun := hei }
  refine {
    compact := hcompact
    connected := hconnected
    sphere := c '' (univ ×ˢ ({0} : Set ℝ))
    first_region := U
    second_region := V
    first_open := S₁.isOpen_target
    second_open := S₂.isOpen_target
    disjoint := hdisjoint
    sphere_disjoint := ?_
    cover := hcover
    first_puncture := p₁
    second_puncture := p₂
    first_model := S₁
    second_model := S₂
    collar := e
    collar_local_diffeomorph := fun z => ⟨E, hes z.property, fun _ _ => rfl⟩
    collar_injective := e.injOn.mono hes
    collar_open := e.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) hes
    collar_sphere := hsph
    collar_negative := ?_
    collar_positive := ?_ }
  · apply disjoint_left.mpr
    rintro _ ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩ (hy | hy)
    · have ht0 : t = 0 := ht
      subst t
      have h := (hU _ (c.map_source (hzero q))).mp hy
      simp only [c.left_inv (hzero q), lt_self_iff_false] at h
    · have ht0 : t = 0 := ht
      subst t
      have h := (hV _ (c.map_source (hzero q))).mp hy
      simp only [c.left_inv (hzero q), lt_self_iff_false] at h
  · rintro _ ⟨⟨q, t⟩, ⟨_, htl, htu⟩, rfl⟩
    have hz := hscaled (q, t) ⟨mem_univ _, htl, htu.trans (by norm_num)⟩
    rw [heq]
    apply (hU _ (c.map_source hz)).mpr
    rw [c.left_inv hz]
    exact mul_neg_of_pos_of_neg hδ htu
  · rintro _ ⟨⟨q, t⟩, ⟨_, htl, htu⟩, rfl⟩
    have hz := hscaled (q, t) ⟨mem_univ _, (by norm_num : (-1 : ℝ) < 0).trans htl, htu⟩
    rw [heq]
    apply (hV _ (c.map_source hz)).mpr
    rw [c.left_inv hz]
    exact mul_pos hδ htl



theorem nonempty_closedComponentCertificate
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (Y : Opens M) (P : SmoothProjectiveDoubleModel Y)
    (hcompact : IsCompact (Y : Set M))
    (hcomponent : ∃ x : M, (Y : Set M) = connectedComponent x) :
    Nonempty (ClosedComponentCertificate .realProjectiveThreeConnectedSum (Y : Set M)) := by
  classical
  have hY : Nonempty Y := by
    obtain ⟨x, hx⟩ := hcomponent
    exact ⟨⟨x, hx.symm.subset mem_connectedComponent⟩⟩
  let inv : M → Y := fun x => if hx : x ∈ Y then ⟨x, hx⟩ else Classical.choice hY
  have hinv (x : M) (hx : x ∈ Y) : (inv x : M) = x := by simp [inv, hx]
  have hinv_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inv (Y : Set M) := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff Y inv (Y : Set M) x).mp
    apply contMDiffWithinAt_id.congr
    · intro y hy
      exact hinv y hy
    · exact hinv x hx
  let S : SmoothClosedComponentModel .realProjectiveThreeConnectedSum (Y : Set M) := {
    model := Y
    model_topology := inferInstance
    model_charted := inferInstance
    model_manifold := inferInstance
    standard_model := P.connectedSumModel
    standard_smooth := ⟨P⟩
    forward := Subtype.val
    inverse := inv
    forward_mem := fun x => x.property
    left_inverse := hinv
    right_inverse := fun x => Subtype.ext (hinv x x.property)
    forward_smooth := contMDiff_subtype_val
    inverse_smooth := hinv_smooth }
  exact S.nonempty_closedComponentCertificate hcompact hcomponent



theorem nonempty_closedComponentCertificate_of_collar_in_open
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (Y : Opens M) (hcompact : IsCompact (Y : Set M))
    (hcomponent : ∃ x : M, (Y : Set M) = connectedComponent x)
    {p₁ p₂ : RealProjectiveThree} {U V : Set M}
    (S₁ : StandardPuncturedProjectiveCover M p₁ U)
    (S₂ : StandardPuncturedProjectiveCover M p₂ V)
    (hUY : U ⊆ Y) (hVY : V ⊆ Y) (hdisjoint : Disjoint U V)
    (c : OpenPartialHomeomorph RoundCylinderSpace M)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source) (htarget : c.target ⊆ Y)
    (hU : ∀ y ∈ c.target, y ∈ U ↔ (c.symm y).2 < 0)
    (hV : ∀ y ∈ c.target, y ∈ V ↔ 0 < (c.symm y).2)
    (hcover : U ∪ V ∪ c '' (univ ×ˢ ({0} : Set ℝ)) = (Y : Set M)) :
    Nonempty (ClosedComponentCertificate .realProjectiveThreeConnectedSum (Y : Set M)) := by
  classical
  have hY : Nonempty Y := by
    obtain ⟨x, hx⟩ := hcomponent
    exact ⟨⟨x, hx.symm.subset mem_connectedComponent⟩⟩
  let : Nonempty Y := hY
  let : CompactSpace Y := isCompact_iff_compactSpace.mp hcompact
  have hconnected : IsConnected (Y : Set M) := by
    obtain ⟨x, hx⟩ := hcomponent
    rw [hx]
    exact isConnected_connectedComponent
  let : ConnectedSpace Y := isConnected_iff_connectedSpace.mp hconnected
  let i : OpenPartialHomeomorph Y M := Y.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  have hit : i.target = (Y : Set M) := by simp [i]
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ i.symm i.target := by
    rw [hit]
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff Y i.symm (Y : Set M) x).mp
    apply contMDiffWithinAt_id.congr
    · intro y hy
      exact i.right_inv (hit.symm ▸ hy)
    · exact i.right_inv (hit.symm ▸ hx)
  let d := c.trans i.symm
  have hds : univ ×ˢ Ioo (-δ) δ ⊆ d.source := by
    intro z hz
    refine ⟨hsource hz, ?_⟩
    change c z ∈ i.target
    rw [hit]
    exact htarget (c.map_source (hsource hz))
  have hd : ContMDiffOn CylModel (𝓡 3) ∞ d d.source :=
    hi.comp (hc.mono inter_subset_left) inter_subset_right
  have hdi : ContMDiffOn (𝓡 3) CylModel ∞ d.symm d.target :=
    hci.comp contMDiff_subtype_val.contMDiffOn inter_subset_right
  have hdval (z : RoundCylinderSpace) (hz : z ∈ univ ×ˢ Ioo (-δ) δ) :
      (d z : M) = c z := i.right_inv (hit.symm ▸ htarget (c.map_source (hsource hz)))
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ univ ×ˢ Ioo (-δ) δ :=
    ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have hdsph : (Subtype.val : Y → M) ⁻¹' (c '' (univ ×ˢ ({0} : Set ℝ))) =
      d '' (univ ×ˢ ({0} : Set ℝ)) := by
    ext y
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, hcy⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, Subtype.ext ((hdval _ (hzero q)).trans hcy)⟩
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨(q, 0), ⟨mem_univ _, rfl⟩, (hdval _ (hzero q)).symm⟩
  have hdin (y : Y) (hy : y ∈ d.target) :
      y ∈ (Subtype.val : Y → M) ⁻¹' U ↔ (d.symm y).2 < 0 := hU y hy.2
  have hdout (y : Y) (hy : y ∈ d.target) :
      y ∈ (Subtype.val : Y → M) ⁻¹' V ↔ 0 < (d.symm y).2 := hV y hy.2
  have hcoverY : (Subtype.val : Y → M) ⁻¹' U ∪ (Subtype.val : Y → M) ⁻¹' V ∪
      d '' (univ ×ˢ ({0} : Set ℝ)) = univ := by
    rw [← hdsph, ← preimage_union, ← preimage_union, hcover]
    exact eq_univ_of_forall fun y => y.property
  let P := of_collar isCompact_univ isConnected_univ (S₁.inOpen Y hUY) (S₂.inOpen Y hVY)
    (hdisjoint.preimage _) d hd hdi hδ hds hdin hdout hcoverY
  exact nonempty_closedComponentCertificate Y P hcompact hcomponent

end PoincareConjecture.SmoothProjectiveDoubleModel
