import PoincareConjecture.Proofs.M32.Claim11_34.CylinderOpen
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Volume
























set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

section Cylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (d : GeneralizedFlowCylinder F C a q J U)

private noncomputable def cylinderSlice (hU : IsOpen U) (s : ℝ) (hs : s ∈ J) :
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
  open_target := cylinder_isOpen_forward_image d hU s hs
  continuousOn_toFun := (d.forward_smooth s hs).continuousOn
  continuousOn_invFun := (d.inverse_smooth s hs).continuousOn

private noncomputable def cylinderSliceAt (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) :
    OpenPartialHomeomorph C.carrier (F.slice t).carrier :=
  ht ▸ cylinderSlice d hU s hs

private theorem cylinderSliceAt_source (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) :
    (cylinderSliceAt d hU s hs ht).source = U := by
  cases ht
  rfl

private theorem cylinderSliceAt_smooth (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cylinderSliceAt d hU s hs ht) U := by
  cases ht
  exact d.forward_smooth s hs

private theorem cylinderSliceAt_symm_smooth (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (cylinderSliceAt d hU s hs ht).symm
      (cylinderSliceAt d hU s hs ht).target := by
  cases ht
  exact d.inverse_smooth s hs

private theorem cylinderSliceAt_pointMap (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) (x : C.carrier) :
    d.pointMap s hs x = (⟨t, cylinderSliceAt d hU s hs ht x⟩ : F.point) := by
  cases ht
  rfl

private theorem cylinderSliceAt_pullbackInner (hU : IsOpen U) (s : ℝ) (hs : s ∈ J)
    {t : ℝ} (ht : a + s / q = t) (x : C.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    d.pullbackInner s hs x v w = q *
      (F.metric t).inner (cylinderSliceAt d hU s hs ht x)
        (mfderiv (𝓡 3) (𝓡 3) (cylinderSliceAt d hU s hs ht) x v)
        (mfderiv (𝓡 3) (𝓡 3) (cylinderSliceAt d hU s hs ht) x w) := by
  cases ht
  rfl

end Cylinder

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

private theorem zero_mem_cylinder (G : GeneralizedBlowupConvergence S J) (k : ℕ) :
    (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
  ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩



noncomputable def blowup_zeroSliceEmbedding (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) :
    OpenPartialHomeomorph G.limit.sliceCarrier.carrier
      ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier :=
  cylinderSliceAt (G.embedding k) (G.exhaustion.space_open k) 0
    (zero_mem_cylinder G k) (by simp)



@[simp] theorem blowup_zeroSliceEmbedding_source
    (G : GeneralizedBlowupConvergence S J) (k : ℕ) :
    (blowup_zeroSliceEmbedding G k).source = G.exhaustion.space k :=
  cylinderSliceAt_source (G.embedding k) (G.exhaustion.space_open k) 0
    (zero_mem_cylinder G k) _



theorem blowup_zeroSliceEmbedding_smooth (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (blowup_zeroSliceEmbedding G k)
      (G.exhaustion.space k) :=
  cylinderSliceAt_smooth (G.embedding k) (G.exhaustion.space_open k) 0
    (zero_mem_cylinder G k) _



theorem blowup_zeroSliceEmbedding_symm_smooth (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (blowup_zeroSliceEmbedding G k).symm
      (blowup_zeroSliceEmbedding G k).target :=
  cylinderSliceAt_symm_smooth (G.embedding k) (G.exhaustion.space_open k) 0
    (zero_mem_cylinder G k) _



theorem blowup_zeroSliceEmbedding_base (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) :
    blowup_zeroSliceEmbedding G k G.limit.base = (S.base (G.subsequence k)).2 := by
  have h := G.base_preserving k (zero_mem_cylinder G k)
  rw [cylinderSliceAt_pointMap (G.embedding k) (G.exhaustion.space_open k)
    0 (zero_mem_cylinder G k) (t := (S.base (G.subsequence k)).1) (by simp)] at h
  exact eq_of_heq (Sigma.mk.inj h).2



noncomputable def blowup_zeroSourceMetric (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) :
    RiemannianMetric 3
      ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier :=
  rescaledMetric ((S.flow (G.subsequence k)).metric (S.base (G.subsequence k)).1)
    (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))



theorem blowup_zeroSourceMetric_ball (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) (r : ℝ) :
    (blowup_zeroSourceMetric G k).ball (S.base (G.subsequence k)).2 r =
      S.baseBall (G.subsequence k) r := by
  rw [blowup_zeroSourceMetric, rescaledMetric_ball_allDimensions]
  rfl



noncomputable def blowup_zeroPullbackForm (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) (x : G.limit.carrier.carrier) :
    TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) x →L[ℝ] ℝ := by
  let e := G.embedding k
  let h0 := zero_mem_cylinder G k
  let : NormedAddCommGroup (TangentSpace (𝓡 3) x) := by unfold TangentSpace; infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) x) := by unfold TangentSpace; infer_instance
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (e.forward 0 h0 x)) := by
    unfold TangentSpace; infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (e.forward 0 h0 x)) := by
    unfold TangentSpace; infer_instance
  let A : TangentSpace (𝓡 3) x →L[ℝ] TangentSpace (𝓡 3) (e.forward 0 h0 x) :=
    mfderiv (𝓡 3) (𝓡 3) (e.forward 0 h0) x
  exact S.scale (G.subsequence k) • ContinuousLinearMap.bilinearComp
    (E := TangentSpace (𝓡 3) (e.forward 0 h0 x))
    (F := TangentSpace (𝓡 3) (e.forward 0 h0 x)) (G := ℝ)
    (E' := TangentSpace (𝓡 3) x) (F' := TangentSpace (𝓡 3) x)
    (((S.flow (G.subsequence k)).metric ((S.base (G.subsequence k)).1 +
      0 / S.scale (G.subsequence k))).inner (e.forward 0 h0 x)) A A



theorem blowup_zeroPullbackForm_eq_sourceMetric
    (G : GeneralizedBlowupConvergence S J) (k : ℕ) (x : G.limit.carrier.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    blowup_zeroPullbackForm G k x v w =
      (blowup_zeroSourceMetric G k).inner (blowup_zeroSliceEmbedding G k x)
        (mfderiv (𝓡 3) (𝓡 3) (blowup_zeroSliceEmbedding G k) x v)
        (mfderiv (𝓡 3) (𝓡 3) (blowup_zeroSliceEmbedding G k) x w) := by
  rw [blowup_zeroSourceMetric, rescaledMetric_inner]
  exact cylinderSliceAt_pullbackInner (G.embedding k) (G.exhaustion.space_open k)
    0 (zero_mem_cylinder G k) (by simp) x v w

end PoincareConjecture.M32
