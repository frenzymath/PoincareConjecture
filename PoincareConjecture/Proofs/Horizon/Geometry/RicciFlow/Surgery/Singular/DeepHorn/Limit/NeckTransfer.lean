import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.LimitMetricJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckSpatialMap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Blowup.Controlled.Geometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.CanonicalNeighborhood
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderRestriction
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (d : GeneralizedFlowCylinder F C a q J U)

theorem horizon_forward_mfderiv_bijective (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {x : C.carrier} (hx : x ∈ U) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x) := by
  have hf := (d.forward_smooth s hs x hx).mdifferentiableWithinAt (by simp)
  have hi := (d.inverse_smooth s hs (d.forward s hs x)
    (mem_image_of_mem (d.forward s hs) hx)).mdifferentiableWithinAt (by simp)
  have hc := mfderivWithin_comp x hi hf
    (fun y hy => mem_image_of_mem (d.forward s hs) hy) (hU.uniqueMDiffOn x hx)
  have hid : mfderivWithin (𝓡 3) (𝓡 3)
      (d.inverse s hs ∘ d.forward s hs) U x =
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) := by
    have heq := mfderivWithin_congr_of_mem (I := 𝓡 3) (I' := 𝓡 3)
      (f := id) (f₁ := d.inverse s hs ∘ d.forward s hs)
      (fun y hy => d.left_inverse s hs hy) hx
    exact heq.trans (mfderivWithin_id (hU.uniqueMDiffOn x hx))
  rw [hid, mfderivWithin_eq_mfderiv (hU.uniqueMDiffOn x hx)
    (hf.mdifferentiableAt (hU.mem_nhds hx))] at hc
  have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x) := by
    intro v w hvw
    have hv := congrArg (fun A => A v) hc
    have hw := congrArg (fun A => A w) hc
    change v = mfderivWithin (𝓡 3) (𝓡 3) (d.inverse s hs)
      (d.forward s hs '' U) (d.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x v) at hv
    change w = mfderivWithin (𝓡 3) (𝓡 3) (d.inverse s hs)
      (d.forward s hs '' U) (d.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x w) at hw
    rw [hvw] at hv
    exact hv.trans hw.symm
  dsimp only [TangentSpace] at hinj ⊢
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

theorem horizon_isOpen_forward_image (hU : IsOpen U) (s : ℝ) (hs : s ∈ J) :
    IsOpen (d.forward s hs '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    ((d.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx))
    (d.horizon_forward_mfderiv_bijective hU s hs hx)]
  change (d.forward s hs) ⁻¹' (d.forward s hs '' U) ∈ 𝓝 x
  exact mem_of_superset (hU.mem_nhds hx) (fun z hz => mem_image_of_mem _ hz)

noncomputable def sliceHomeomorph (hU : IsOpen U) (s : ℝ) (hs : s ∈ J) :
    OpenPartialHomeomorph C.carrier (F.slice (a + s / q)).carrier where
  toFun := d.forward s hs
  invFun := d.inverse s hs
  source := U
  target := d.forward s hs '' U
  map_source' := fun x hx => mem_image_of_mem (d.forward s hs) hx
  map_target' := by
    rintro x ⟨y, hy, rfl⟩
    rw [d.left_inverse s hs hy]
    exact hy
  left_inv' := d.left_inverse s hs
  right_inv' := d.right_inverse s hs
  open_source := hU
  open_target := d.horizon_isOpen_forward_image hU s hs
  continuousOn_toFun := (d.forward_smooth s hs).continuousOn
  continuousOn_invFun := (d.inverse_smooth s hs).continuousOn

@[simp] theorem sliceHomeomorph_apply (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : C.carrier) : d.sliceHomeomorph hU s hs x = d.forward s hs x := rfl

@[simp] theorem sliceHomeomorph_symm_apply (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    (x : (F.slice (a + s / q)).carrier) :
    (d.sliceHomeomorph hU s hs).symm x = d.inverse s hs x := rfl

noncomputable def sliceHomeomorphAt (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) :
    OpenPartialHomeomorph C.carrier (F.slice t).carrier := ht ▸ d.sliceHomeomorph hU s hs

theorem sliceHomeomorphAt_source (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) : (d.sliceHomeomorphAt hU s hs ht).source = U := by
  cases ht
  rfl

theorem sliceHomeomorphAt_smooth (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (d.sliceHomeomorphAt hU s hs ht) U := by
  cases ht
  exact d.forward_smooth s hs

theorem sliceHomeomorphAt_symm_smooth (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (d.sliceHomeomorphAt hU s hs ht).symm
      (d.sliceHomeomorphAt hU s hs ht).target := by
  cases ht
  exact d.inverse_smooth s hs

theorem sliceHomeomorphAt_pointMap (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) (x : C.carrier) :
    d.pointMap s hs x = (⟨t, d.sliceHomeomorphAt hU s hs ht x⟩ : F.point) := by
  cases ht
  rfl

theorem sliceHomeomorphAt_pullbackInner (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) (x : C.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    d.pullbackInner s hs x v w = q *
      (F.metric t).inner (d.sliceHomeomorphAt hU s hs ht x)
        (mfderiv (𝓡 3) (𝓡 3) (d.sliceHomeomorphAt hU s hs ht) x v)
        (mfderiv (𝓡 3) (𝓡 3) (d.sliceHomeomorphAt hU s hs ht) x w) := by
  cases ht
  rfl

noncomputable def zeroSliceHomeomorph (hU : IsOpen U) (hzero : 0 ∈ J) :
    OpenPartialHomeomorph C.carrier (F.slice a).carrier :=
  d.sliceHomeomorphAt hU 0 hzero (by simp)

@[simp] theorem zeroSliceHomeomorph_source (hU : IsOpen U) (hzero : 0 ∈ J) :
    (d.zeroSliceHomeomorph hU hzero).source = U :=
  d.sliceHomeomorphAt_source hU 0 hzero _

theorem zeroSliceHomeomorph_smooth (hU : IsOpen U) (hzero : 0 ∈ J) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (d.zeroSliceHomeomorph hU hzero) U :=
  d.sliceHomeomorphAt_smooth hU 0 hzero _

theorem zeroSliceHomeomorph_symm_smooth (hU : IsOpen U) (hzero : 0 ∈ J) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (d.zeroSliceHomeomorph hU hzero).symm
      (d.zeroSliceHomeomorph hU hzero).target :=
  d.sliceHomeomorphAt_symm_smooth hU 0 hzero _

theorem zeroSliceHomeomorph_pointMap (hU : IsOpen U) (hzero : 0 ∈ J)
    (x : C.carrier) :
    d.pointMap 0 hzero x = (⟨a, d.zeroSliceHomeomorph hU hzero x⟩ : F.point) :=
  d.sliceHomeomorphAt_pointMap hU 0 hzero _ x

theorem zeroSliceHomeomorph_pullbackInner (hU : IsOpen U) (hzero : 0 ∈ J)
    (x : C.carrier) (v w : TangentSpace (𝓡 3) x) :
    d.pullbackInner 0 hzero x v w = q *
      (F.metric a).inner (d.zeroSliceHomeomorph hU hzero x)
        (mfderiv (𝓡 3) (𝓡 3) (d.zeroSliceHomeomorph hU hzero) x v)
        (mfderiv (𝓡 3) (𝓡 3) (d.zeroSliceHomeomorph hU hzero) x w) :=
  d.sliceHomeomorphAt_pullbackInner hU 0 hzero _ x v w

variable {C' : GeneralizedSliceCarrier.{u}}

noncomputable def rebasePartialSource
    (e : OpenPartialHomeomorph C'.carrier C.carrier) (heU : e.target ⊆ U)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target) :
    GeneralizedFlowCylinder F C' a q J e.source := by
  have hmaps : MapsTo e e.source U := fun x hx => heU (e.map_source hx)
  refine {
    scale_pos := d.scale_pos
    forward := fun s hs => d.forward s hs ∘ e
    inverse := fun s hs => e.symm ∘ d.inverse s hs
    forward_smooth := fun s hs => (d.forward_smooth s hs).comp he hmaps
    inverse_smooth := ?_
    left_inverse := ?_
    right_inverse := ?_
    embedding := d.embedding.comp (Topology.IsEmbedding.id.prodMap
      ((Topology.IsEmbedding.inclusion heU).comp e.toHomeomorphSourceTarget.isEmbedding))
    vertical_compatibility := fun s hs x hx => d.vertical_compatibility s hs (e x) (hmaps hx) }
  · intro s hs
    apply hei.comp ((d.inverse_smooth s hs).mono ?_) ?_
    · rintro y ⟨x, hx, rfl⟩
      exact mem_image_of_mem (d.forward s hs) (hmaps hx)
    · rintro y ⟨x, hx, rfl⟩
      dsimp only [Function.comp_apply]
      change d.inverse s hs (d.forward s hs (e x)) ∈ e.target
      rw [d.left_inverse s hs (hmaps hx)]
      exact e.map_source hx
  · intro s hs x hx
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs (hmaps hx), e.left_inv hx]
  · intro s hs y hy
    obtain ⟨x, hx, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [d.left_inverse s hs (hmaps hx), e.left_inv hx]

theorem rebasePartialSource_pointMap
    (e : OpenPartialHomeomorph C'.carrier C.carrier) (heU : e.target ⊆ U)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (s : ℝ) (hs : s ∈ J) (x : C'.carrier) :
    (d.rebasePartialSource e heU he hei).pointMap s hs x = d.pointMap s hs (e x) := rfl

theorem rebasePartialSource_pullbackInner
    (e : OpenPartialHomeomorph C'.carrier C.carrier) (heU : e.target ⊆ U)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hU : IsOpen U) (s : ℝ) (hs : s ∈ J) (x : C'.carrier) (hx : x ∈ e.source)
    (v w : TangentSpace (𝓡 3) x) :
    (d.rebasePartialSource e heU he hei).pullbackInner s hs x v w =
      d.pullbackInner s hs (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
        (mfderiv (𝓡 3) (𝓡 3) e x w) := by
  have hd := ((d.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds (heU (e.map_source hx)))).mdifferentiableAt (by simp)
  have hef := (he.contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  dsimp only [pullbackInner, rebasePartialSource]
  rw [mfderiv_comp x hd hef]
  rfl

noncomputable def rebaseAtZero (hU : IsOpen U) (hzero : 0 ∈ J) :
    GeneralizedFlowCylinder F (F.slice a) a q J
      (d.zeroSliceHomeomorph hU hzero).target :=
  d.rebasePartialSource (d.zeroSliceHomeomorph hU hzero).symm
    (by simp only [OpenPartialHomeomorph.symm_target, zeroSliceHomeomorph_source]; rfl)
    (d.zeroSliceHomeomorph_symm_smooth hU hzero)
    (by simpa only [OpenPartialHomeomorph.symm_symm,
      OpenPartialHomeomorph.symm_target, zeroSliceHomeomorph_source] using
      d.zeroSliceHomeomorph_smooth hU hzero)

theorem rebaseAtZero_identity (hU : IsOpen U) (hzero : 0 ∈ J)
    (x : (F.slice a).carrier) (hx : x ∈ (d.zeroSliceHomeomorph hU hzero).target) :
    (d.rebaseAtZero hU hzero).pointMap 0 hzero x = (⟨a, x⟩ : F.point) := by
  change d.pointMap 0 hzero ((d.zeroSliceHomeomorph hU hzero).symm x) = _
  rw [d.zeroSliceHomeomorph_pointMap hU hzero,
    (d.zeroSliceHomeomorph hU hzero).right_inv hx]

theorem rebaseAtZero_cylindricalPullback (hU : IsOpen U) (hzero : 0 ∈ J)
    {epsilon : ℝ} (Φ : RoundCylinderSpace → C.carrier)
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))
    (hΦU : MapsTo Φ (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) U)
    (s : ℝ) (hs : s ∈ J) (z : RoundCylinderSpace)
    (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹) (v w : RoundCylinderTangent z) :
    generalizedCylinderPullback (d.rebaseAtZero hU hzero)
      (d.zeroSliceHomeomorph hU hzero ∘ Φ) s z v w =
      generalizedCylinderPullback d Φ s z v w := by
  let e := d.zeroSliceHomeomorph hU hzero
  let coordinate := e ∘ Φ
  have hΦz : Φ z ∈ e.source := by
    rw [d.zeroSliceHomeomorph_source]
    exact hΦU ⟨mem_univ _, hz⟩
  have hcoordinate : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) :=
    (d.zeroSliceHomeomorph_smooth hU hzero).comp hΦ hΦU
  have hd := (hcoordinate.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have hi := ((d.zeroSliceHomeomorph_symm_smooth hU hzero).contMDiffAt
    (e.open_target.mem_nhds (e.map_source hΦz))).mdifferentiableAt (by simp)
  have heq : e.symm ∘ coordinate =ᶠ[𝓝 z] Φ := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩] with y hy
    exact e.left_inv (by rw [d.zeroSliceHomeomorph_source]; exact hΦU hy)
  have hderiv : (mfderiv (𝓡 3) (𝓡 3) e.symm (coordinate z)).comp
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z := by
    rw [← mfderiv_comp z hi hd]
    exact heq.mfderiv_eq
  have hderiv_apply (v : RoundCylinderTangent z) :
      mfderiv (𝓡 3) (𝓡 3) e.symm (coordinate z)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Φ z v :=
    congrArg (fun A => A v) hderiv
  simp only [generalizedCylinderPullback, dif_pos hs]
  change (d.rebasePartialSource e.symm _ _ _).pullbackInner s hs (coordinate z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w) = _
  rw [d.rebasePartialSource_pullbackInner e.symm _ _ _ hU s hs (coordinate z)
    (e.map_source hΦz), hderiv_apply v, hderiv_apply w]
  change d.pullbackInner s hs (e.symm (e (Φ z))) _ _ = _
  rw [e.left_inv hΦz]

end PoincareConjecture.GeneralizedFlowCylinder

namespace PoincareConjecture.GeneralizedBlowupConvergence

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence S J)

noncomputable def zeroSliceEmbedding (k : ℕ) :
    OpenPartialHomeomorph G.limit.sliceCarrier.carrier
      ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier :=
  (G.embedding k).zeroSliceHomeomorph (G.exhaustion.space_open k)
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩

@[simp] theorem zeroSliceEmbedding_source (k : ℕ) :
    (G.zeroSliceEmbedding k).source = G.exhaustion.space k :=
  (G.embedding k).zeroSliceHomeomorph_source _ _

theorem zeroSliceEmbedding_smooth (k : ℕ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (G.zeroSliceEmbedding k) (G.exhaustion.space k) :=
  (G.embedding k).zeroSliceHomeomorph_smooth _ _

theorem zeroSliceEmbedding_symm_smooth (k : ℕ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (G.zeroSliceEmbedding k).symm
      (G.zeroSliceEmbedding k).target :=
  (G.embedding k).zeroSliceHomeomorph_symm_smooth _ _

theorem zeroSliceEmbedding_base (k : ℕ) :
    G.zeroSliceEmbedding k G.limit.base = (S.base (G.subsequence k)).2 := by
  have h := G.base_preserving k
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  rw [(G.embedding k).zeroSliceHomeomorph_pointMap (G.exhaustion.space_open k)] at h
  exact eq_of_heq (Sigma.mk.inj h).2

noncomputable def cylinderSlabEmbedding
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limit.sliceCarrier.carrier)
    (epsilon : ℝ) (k : ℕ) : OpenPartialHomeomorph RoundCylinderSpace
      ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier :=
  (Φ.toHomeomorph.toOpenPartialHomeomorph.trans (G.zeroSliceEmbedding k)).restrOpen
    (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) (isOpen_univ.prod isOpen_Ioo)

@[simp] theorem cylinderSlabEmbedding_apply
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limit.sliceCarrier.carrier)
    (epsilon : ℝ) (k : ℕ) (z : RoundCylinderSpace) :
    G.cylinderSlabEmbedding Φ epsilon k z = G.zeroSliceEmbedding k (Φ z) := rfl

@[simp] theorem cylinderSlabEmbedding_symm_apply
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limit.sliceCarrier.carrier)
    (epsilon : ℝ) (k : ℕ)
    (x : ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier) :
    (G.cylinderSlabEmbedding Φ epsilon k).symm x =
      Φ.symm ((G.zeroSliceEmbedding k).symm x) := rfl

theorem eventually_cylinderSlab_subset_exhaustion
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limit.sliceCarrier.carrier)
    (epsilon : ℝ) :
    ∀ᶠ k in atTop, Φ '' (univ ×ˢ Icc (-epsilon⁻¹) epsilon⁻¹) ⊆ G.exhaustion.space k := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    ((isCompact_univ.prod isCompact_Icc).image Φ.continuous)
  exact (eventually_ge_atTop j).mono fun k hk => hj.trans (G.exhaustion.space_increasing hk)

theorem eventually_cylinderSlabEmbedding
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limit.sliceCarrier.carrier)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ k in atTop,
      let e := G.cylinderSlabEmbedding Φ epsilon k
      e.source = univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e
        (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
      e '' (univ ×ˢ ({0} : Set ℝ)) ⊆ e.target := by
  filter_upwards [G.eventually_cylinderSlab_subset_exhaustion Φ epsilon] with k hk
  let e := G.cylinderSlabEmbedding Φ epsilon k
  have hsub : univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ ⊆ Φ ⁻¹' G.exhaustion.space k := by
    intro z hz
    exact hk (mem_image_of_mem Φ ⟨hz.1, hz.2.1.le, hz.2.2.le⟩)
  have hsource : e.source = univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    change (univ ∩ Φ ⁻¹' (G.zeroSliceEmbedding k).source) ∩
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) = _
    rw [G.zeroSliceEmbedding_source, univ_inter, inter_eq_right.mpr hsub]
  refine ⟨hsource, ?_, ?_, ?_⟩
  · exact (G.zeroSliceEmbedding_smooth k).comp Φ.contMDiff.contMDiffOn hsub
  · apply Φ.symm.contMDiff.comp_contMDiffOn
    apply (G.zeroSliceEmbedding_symm_smooth k).mono
    intro x hx
    have hxsrc := e.map_target hx
    have heq := e.right_inv hx
    change G.zeroSliceEmbedding k (Φ (e.symm x)) = x at heq
    rw [← heq]
    apply (G.zeroSliceEmbedding k).map_source
    rw [G.zeroSliceEmbedding_source]
    exact hsub (hsource ▸ hxsrc)
  · rintro x ⟨z, hz, rfl⟩
    apply e.map_source
    rw [hsource]
    have hpos := inv_pos.mpr hepsilon
    exact ⟨hz.1, by simpa only [mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ from ⟨neg_neg_of_pos hpos, hpos⟩)⟩

theorem cylinderSlabEmbedding_center
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limit.sliceCarrier.carrier)
    (epsilon : ℝ) (k : ℕ) (q : UnitTwoSphere) (hq : Φ (q, 0) = G.limit.base) :
    G.cylinderSlabEmbedding Φ epsilon k (q, 0) = (S.base (G.subsequence k)).2 := by
  rw [cylinderSlabEmbedding_apply, hq, G.zeroSliceEmbedding_base]

end PoincareConjecture.GeneralizedBlowupConvergence
