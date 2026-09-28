import PoincareConjecture.Proofs.M47.LimitRP2Collar
import PoincareConjecture.Proofs.M47.LimitRP2Charts












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

section Transfer

variable {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
  {C : GeneralizedSliceCarrier.{u}} [ConnectedSpace C.carrier]
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  {K : AncientKappaSolution 3 C.carrier}



theorem limitRP2_cover_eq (D : M27ProjectivePlaneLineFlowCertificate K)
    (p : UnitTwoSphere × ℝ) :
    D.cover p = D.product_homeomorph.symm (Quotient.mk' p.1, p.2) := by
  exact (D.product_homeomorph.symm_apply_apply (D.cover p)).symm.trans
    (congrArg D.product_homeomorph.symm (D.product_coordinates p))


theorem limitRP2_cover_mem_compact (D : M27ProjectivePlaneLineFlowCertificate K)
    (p : UnitTwoSphere × ℝ) (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    D.cover p ∈ limitRP2CompactCollar D.product_homeomorph := by
  rw [limitRP2_cover_eq D p]
  exact limitRP2InnerCollar_mem_compact D.product_homeomorph
    (Quotient.mk' p.1, ⟨p.2, hp⟩)



noncomputable def limitRP2PhysicalCollar
    (e : GeneralizedFlowCylinder G C origin scale I U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K) :
    RealProjectiveTwo × Ioo (-1 : ℝ) 1 → (F.slice (origin + s / scale)).carrier :=
  limitRP2PhysicalMap e R s hs ht ∘ limitRP2InnerCollar D.product_homeomorph



noncomputable def limitRP2PhysicalCover
    (e : GeneralizedFlowCylinder G C origin scale I U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K) :
    UnitTwoSphere × ℝ → (F.slice (origin + s / scale)).carrier :=
  limitRP2PhysicalMap e R s hs ht ∘ D.cover



theorem limitRP2PhysicalCollar_isOpenEmbedding
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K)
    (hcover : limitRP2CompactCollar D.product_homeomorph ⊆ U) :
    Topology.IsOpenEmbedding (limitRP2PhysicalCollar e R s hs ht D) := by
  exact (limitRP2PhysicalMap_isOpenEmbedding e hU R s hs ht).comp
    (limitRP2InnerCollar_isOpenEmbedding_codRestrict D.product_homeomorph hU hcover)



theorem limitRP2PhysicalCover_quotient
    (e : GeneralizedFlowCylinder G C origin scale I U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K)
    (p : UnitTwoSphere × ℝ) (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    limitRP2PhysicalCover e R s hs ht D p =
      limitRP2PhysicalCollar e R s hs ht D (Quotient.mk' p.1, ⟨p.2, hp⟩) := by
  exact congrArg (limitRP2PhysicalMap e R s hs ht) (limitRP2_cover_eq D p)



theorem limitRP2PhysicalCover_isLocalDiffeomorphOn
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K)
    (hcover : limitRP2CompactCollar D.product_homeomorph ⊆ U) :
    IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (limitRP2PhysicalCover e R s hs ht D)
      ((univ : Set UnitTwoSphere) ×ˢ Ioo (-1 : ℝ) 1) := by
  intro p
  exact (D.cover_local_diffeomorph p).comp (K := 𝓡 3) (P := _)
    (limitRP2PhysicalMap_isLocalDiffeomorphAt e hU R s hs ht
      (hcover (limitRP2_cover_mem_compact D p p.property.2)))


theorem limitRP2PhysicalCover_contMDiffOn
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K)
    (hcover : limitRP2CompactCollar D.product_homeomorph ⊆ U) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (limitRP2PhysicalCover e R s hs ht D)
      ((univ : Set UnitTwoSphere) ×ˢ Ioo (-1 : ℝ) 1) :=
  (limitRP2PhysicalCover_isLocalDiffeomorphOn e hU R s hs ht D hcover).contMDiffOn



theorem limitRP2PhysicalCover_fibers
    (e : GeneralizedFlowCylinder G C origin scale I U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K)
    (hcover : limitRP2CompactCollar D.product_homeomorph ⊆ U)
    (p q : UnitTwoSphere × ℝ)
    (hp : p.2 ∈ Ioo (-1 : ℝ) 1) (hq : q.2 ∈ Ioo (-1 : ℝ) 1) :
    limitRP2PhysicalCover e R s hs ht D p = limitRP2PhysicalCover e R s hs ht D q ↔
      q = p ∨ q = (-p.1, p.2) := by
  constructor
  · intro hpq
    exact (D.cover_fibers p q).mp ((limitRP2PhysicalMap_injOn e R s hs ht)
      (hcover (limitRP2_cover_mem_compact D p hp))
      (hcover (limitRP2_cover_mem_compact D q hq)) hpq)
  · intro hpq
    exact congrArg (limitRP2PhysicalMap e R s hs ht) ((D.cover_fibers p q).mpr hpq)



theorem limitRP2PhysicalCover_antipodal
    (e : GeneralizedFlowCylinder G C origin scale I U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K) (z : UnitTwoSphere) (r : ℝ) :
    limitRP2PhysicalCover e R s hs ht D (-z, r) =
      limitRP2PhysicalCover e R s hs ht D (z, r) := by
  exact congrArg (limitRP2PhysicalMap e R s hs ht)
    ((D.cover_fibers (z, r) (-z, r)).mpr (Or.inr rfl)).symm


theorem limitRP2PhysicalCover_mfderiv_bijective
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K)
    (hcover : limitRP2CompactCollar D.product_homeomorph ⊆ U)
    (p : UnitTwoSphere × ℝ) (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    Function.Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      (limitRP2PhysicalCover e R s hs ht D) p) := by
  exact ((limitRP2PhysicalCover_isLocalDiffeomorphOn e hU R s hs ht D hcover
    ⟨p, ⟨mem_univ _, hp⟩⟩).mfderivToContinuousLinearEquiv (by simp)).bijective



theorem limitRP2PhysicalCover_normal_ne_tangent
    (e : GeneralizedFlowCylinder G C origin scale I U) (hU : IsOpen U)
    (R : M33RegularHistoryRealization G F) (s : ℝ) (hs : s ∈ I)
    (ht : origin + s / scale ∈ G.interval)
    (D : M27ProjectivePlaneLineFlowCertificate K)
    (hcover : limitRP2CompactCollar D.product_homeomorph ⊆ U)
    (p : UnitTwoSphere × ℝ) (hp : p.2 ∈ Ioo (-1 : ℝ) 1)
    (v : TangentSpace (𝓡 2) p.1) :
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (limitRP2PhysicalCover e R s hs ht D) p (0, 1) ≠
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
        (limitRP2PhysicalCover e R s hs ht D) p (v, 0) := by
  intro heq
  have hv := (limitRP2PhysicalCover_mfderiv_bijective e hU R s hs ht D hcover p hp).1 heq
  exact one_ne_zero (congrArg Prod.snd hv)

end Transfer




theorem limitRP2_no_projectivePlaneLine
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (C : GeneralizedBlowupConvergence S J)
    (F : ℕ → SurgeryFlowData.{u})
    (R : ∀ i, M33RegularHistoryRealization (S.flow i) (F i)) :
    letI : ConnectedSpace C.limit.sliceCarrier.carrier := C.limit.connectedSpace
    ∀ K : AncientKappaSolution 3 C.limit.sliceCarrier.carrier,
      ¬ Nonempty (M27ProjectivePlaneLineFlowCertificate K) := by
  let : ConnectedSpace C.limit.sliceCarrier.carrier := C.limit.connectedSpace
  intro K ⟨D⟩
  obtain ⟨k, hk⟩ := limitRP2_compactCollar_subset_domain C.exhaustion D.product_homeomorph
  have hzero : 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  have ht : (S.base (C.subsequence k)).1 + 0 / S.scale (C.subsequence k) ∈
      (S.flow (C.subsequence k)).interval :=
    ((S.flow (C.subsequence k)).slice_nonempty_iff _).mp
      ⟨(C.embedding k).forward 0 hzero C.limit.base⟩
  exact (F (C.subsequence k)).no_two_sided_projective_plane _
    ((R (C.subsequence k)).time_subset ht)
    ⟨limitRP2PhysicalCollar (C.embedding k) (R (C.subsequence k)) 0 hzero ht D,
      limitRP2PhysicalCollar_isOpenEmbedding (C.embedding k)
        (C.exhaustion.space_open k) (R (C.subsequence k)) 0 hzero ht D hk⟩

end PoincareConjecture.M47
