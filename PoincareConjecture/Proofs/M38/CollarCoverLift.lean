import PoincareConjecture.Proofs.M38.CoverSphereLifts
import PoincareConjecture.Definitions.Ch11.BlowupLimits
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Covering
import Mathlib.Analysis.Convex.Contractible














set_option autoImplicit false

open Set Topology Filter
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem simplyConnectedSpace_collarStrip {δ : ℝ} (hδ : 0 < δ) :
    SimplyConnectedSpace (UnitTwoSphere × Ioo (-δ) δ) := by
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : ContractibleSpace (Ioo (-δ) δ) :=
    (convex_Ioo (-δ) δ).contractibleSpace ⟨0, neg_lt_zero.mpr hδ, hδ⟩
  exact ((ContinuousMap.HomotopyEquiv.refl UnitTwoSphere).prodCongr
    (ContractibleSpace.hequiv (Ioo (-δ) δ) Unit).some |>.trans
      (Homeomorph.prodUnique UnitTwoSphere Unit).toHomotopyEquiv).simplyConnectedSpace




theorem continuous_collar_lift_smooth
    {A Q : GeneralizedSliceCarrier.{u}}
    (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    {U : Set RoundCylinderSpace} (hU : IsOpen U)
    (c : RoundCylinderSpace → Q.carrier)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c U)
    (L : RoundCylinderSpace → A.carrier) (hL : ContinuousOn L U)
    (hlift : ∀ p ∈ U, q (L p) = c p) :
    ContMDiffOn CylModel (𝓡 3) ∞ L U := by
  intro p hp
  let h := hq (L p)
  have hinverse : ContMDiffAt (𝓡 3) (𝓡 3) ∞ h.localInverse (c p) := by
    rw [← hlift p hp]
    exact h.localInverse_contMDiffAt
  have hsmooth := hinverse.comp p ((hc p hp).contMDiffAt (hU.mem_nhds hp))
  have hnear : ∀ᶠ x in 𝓝 p, L x ∈ h.localInverse.target :=
    ((hL p hp).continuousAt (hU.mem_nhds hp)).preimage_mem_nhds
      (h.localInverse.open_target.mem_nhds h.localInverse_mem_target)
  apply (hsmooth.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hU.mem_nhds hp, hnear] with x hx htarget
  change L x = h.localInverse (c x)
  rw [← hlift x hx, h.localInverse_left_inv htarget]




theorem exists_smooth_collar_lift
    {A Q : GeneralizedSliceCarrier.{u}}
    (q : A.carrier → Q.carrier)
    (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q) (hcover : IsCoveringMap q)
    (c : OpenPartialHomeomorph RoundCylinderSpace Q.carrier)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : c.source = univ ×ˢ Ioo (-δ) δ)
    (z₀ : UnitTwoSphere) (a₀ : A.carrier) (ha₀ : q a₀ = c (z₀, 0)) :
    ∃ C : OpenPartialHomeomorph RoundCylinderSpace A.carrier,
      C.source = c.source ∧ C (z₀, 0) = a₀ ∧
      ContMDiffOn CylModel (𝓡 3) ∞ C C.source ∧
      ContMDiffOn (𝓡 3) CylModel ∞ C.symm C.target ∧
        ∀ p ∈ c.source, q (C p) = c p := by
  classical
  let D := UnitTwoSphere × Ioo (-δ) δ
  let : SimplyConnectedSpace D := simplyConnectedSpace_collarStrip hδ
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  let : LocallyPathConnectedSpace (Ioo (-δ) δ) := isOpen_Ioo.locallyPathConnectedSpace
  let e : D ≃ₜ c.source :=
    ((Homeomorph.Set.univ UnitTwoSphere).symm.prodCongr
      (Homeomorph.refl (Ioo (-δ) δ))).trans
        ((Homeomorph.Set.prod univ (Ioo (-δ) δ)).symm.trans
          (Homeomorph.setCongr hsource.symm))
  let f : D → Q.carrier := fun p => c (e p).val
  have hf : IsOpenEmbedding f := c.isOpenEmbedding_restrict.comp e.isOpenEmbedding
  let d₀ : D := (z₀, ⟨0, neg_lt_zero.mpr hδ, hδ⟩)
  obtain ⟨F, hF₀, hqF, hFopen⟩ :=
    Poincare.Topology.exists_openEmbedding_lift hcover hf d₀ a₀ ha₀
  let L : RoundCylinderSpace → A.carrier :=
    fun p => if hp : p ∈ c.source then F (e.symm ⟨p, hp⟩) else a₀
  have hL (p : c.source) : L p.val = F (e.symm p) := by
    simp only [L, dif_pos p.property]
  have hLcontinuous : ContinuousOn L c.source := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert F.continuous.comp e.symm.continuous using 1
    funext p
    exact hL p
  have hlift (p : RoundCylinderSpace) (hp : p ∈ c.source) : q (L p) = c p := by
    rw [hL ⟨p, hp⟩]
    have hh := congrFun hqF (e.symm ⟨p, hp⟩)
    change q (F (e.symm ⟨p, hp⟩)) = c (e (e.symm ⟨p, hp⟩)).val at hh
    simpa only [e.apply_symm_apply] using hh
  have himage : L '' c.source = range F := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨e.symm ⟨p, hp⟩, (hL ⟨p, hp⟩).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨(e p).val, (e p).property, (hL (e p)).trans
        (congrArg F (e.symm_apply_apply p))⟩
  have hinverse : ∀ p ∈ c.source, c.symm (q (L p)) = p := by
    intro p hp
    rw [hlift p hp, c.left_inv hp]
  have hmaps : MapsTo q (L '' c.source) c.target := by
    rintro _ ⟨p, hp, rfl⟩
    rw [hlift p hp]
    exact c.map_source hp
  let C : OpenPartialHomeomorph RoundCylinderSpace A.carrier := {
    toFun := L
    invFun := c.symm ∘ q
    source := c.source
    target := L '' c.source
    map_source' := fun _ hp => mem_image_of_mem L hp
    map_target' := by
      rintro _ ⟨p, hp, rfl⟩
      change c.symm (q (L p)) ∈ c.source
      rw [hinverse p hp]
      exact hp
    left_inv' := hinverse
    right_inv' := by
      rintro _ ⟨p, hp, rfl⟩
      change L (c.symm (q (L p))) = L p
      rw [hinverse p hp]
    open_source := c.open_source
    open_target := himage.symm ▸ hFopen.isOpen_range
    continuousOn_toFun := hLcontinuous
    continuousOn_invFun := c.symm.continuousOn.comp hq.contMDiff.continuous.continuousOn hmaps }
  refine ⟨C, rfl, ?_, ?_, ?_, hlift⟩
  · have hp : (z₀, (0 : ℝ)) ∈ c.source := hsource.symm ▸ ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
    change L (z₀, 0) = a₀
    rw [hL ⟨(z₀, 0), hp⟩]
    exact hF₀
  · exact continuous_collar_lift_smooth q hq c.open_source c hc L hLcontinuous hlift
  · exact hci.comp hq.contMDiff.contMDiffOn hmaps

end PoincareConjecture.M38
