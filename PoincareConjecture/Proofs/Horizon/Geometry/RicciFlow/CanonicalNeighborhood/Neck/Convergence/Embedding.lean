import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.BallTransfer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding
import Mathlib.Geometry.Manifold.Diffeomorph









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture


noncomputable def neckDomainHomeomorphSlab (ε : ℝ) :
    NeckDomain ε ≃ₜ (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ : Set RoundCylinderSpace) :=
  ((Homeomorph.Set.univ UnitTwoSphere).symm.prodCongr
    (Homeomorph.refl (Ioo (-ε⁻¹) ε⁻¹))).trans
      (Homeomorph.Set.prod univ (Ioo (-ε⁻¹) ε⁻¹)).symm

@[simp] theorem neckDomainHomeomorphSlab_coe (ε : ℝ) (z : NeckDomain ε) :
    (neckDomainHomeomorphSlab ε z : RoundCylinderSpace) = (z.1, (z.2 : ℝ)) := rfl



noncomputable def neckDomainCoordinates {M : Type*} [TopologicalSpace M]
    {ε : ℝ} (e : OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : e.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) : NeckDomain ε ≃ₜ e.target :=
  (neckDomainHomeomorphSlab ε).trans
    ((Homeomorph.setCongr hsource.symm).trans e.toHomeomorphSourceTarget)

@[simp] theorem neckDomainCoordinates_coe {M : Type*} [TopologicalSpace M]
    {ε : ℝ} (e : OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : e.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) (z : NeckDomain ε) :
    (neckDomainCoordinates e hsource z : M) = e (z.1, (z.2 : ℝ)) := rfl

theorem neckDomainCoordinates_inverse_mem {M : Type*} [TopologicalSpace M]
    {ε : ℝ} (e : OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : e.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) {x : M} (hx : x ∈ e.target) :
    e.symm x ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ := by
  rw [← hsource]
  exact e.map_target hx

@[simp] theorem neckDomainCoordinates_inverse_left {M : Type*} [TopologicalSpace M]
    {ε : ℝ} (e : OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : e.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) (z : NeckDomain ε) :
    e.symm (neckDomainCoordinates e hsource z) = (z.1, (z.2 : ℝ)) := by
  rw [neckDomainCoordinates_coe]
  apply e.left_inv
  rw [hsource]
  exact ⟨mem_univ _, z.2.property⟩

@[simp] theorem neckDomainCoordinates_inverse_right {M : Type*} [TopologicalSpace M]
    {ε : ℝ} (e : OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : e.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) (x : M) (hx : x ∈ e.target) :
    neckDomainCoordinates e hsource
      ((e.symm x).1, ⟨(e.symm x).2, (neckDomainCoordinates_inverse_mem e hsource hx).2⟩) =
      ⟨x, hx⟩ := by
  apply Subtype.ext
  exact e.right_inv hx

namespace PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {a b : ℝ} {S : PointedFlowSequence 3 a b}



noncomputable def cylinderSlabEmbedding (G : PointedGeometricConvergence S)
    (hzero : a < 0 ∧ 0 < b)
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
    (ε : ℝ) (k : ℕ) :
    OpenPartialHomeomorph RoundCylinderSpace (S.carrier (G.subsequence k)).carrier :=
  (Φ.toHomeomorph.toOpenPartialHomeomorph.trans
    ((G.embedding k).spatialHomeomorph (G.exhaustion_open k) hzero)).restrOpen
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) (isOpen_univ.prod isOpen_Ioo)

@[simp] theorem cylinderSlabEmbedding_apply (G : PointedGeometricConvergence S)
    (hzero : a < 0 ∧ 0 < b)
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
    (ε : ℝ) (k : ℕ) (z : RoundCylinderSpace) :
    G.cylinderSlabEmbedding hzero Φ ε k z = ((G.embedding k).toFun (0, Φ z)).2 := rfl

@[simp] theorem cylinderSlabEmbedding_symm_apply (G : PointedGeometricConvergence S)
    (hzero : a < 0 ∧ 0 < b)
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
    (ε : ℝ) (k : ℕ) (x : (S.carrier (G.subsequence k)).carrier) :
    (G.cylinderSlabEmbedding hzero Φ ε k).symm x =
      Φ.symm ((G.embedding k).inverse (0, x)).2 := rfl


theorem eventually_cylinderSlab_subset_exhaustion (G : PointedGeometricConvergence S)
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
    (ε : ℝ) :
    ∀ᶠ k in atTop, Φ '' (univ ×ˢ Icc (-ε⁻¹) ε⁻¹) ⊆ G.exhaustion k := by
  have hcompact : IsCompact (univ ×ˢ Icc (-ε⁻¹) ε⁻¹ : Set RoundCylinderSpace) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hcompact.image Φ.continuous)
  exact (eventually_ge_atTop j).mono fun k hk => hj.trans (G.exhaustion_monotone hk)



theorem eventually_cylinderSlabEmbedding (G : PointedGeometricConvergence S)
    (hzero : a < 0 ∧ 0 < b)
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop,
      let e := G.cylinderSlabEmbedding hzero Φ ε k
      e.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e
        (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target ∧
      e '' (univ ×ˢ ({0} : Set ℝ)) ⊆ e.target := by
  filter_upwards [G.eventually_cylinderSlab_subset_exhaustion Φ ε] with k hk
  let e := G.cylinderSlabEmbedding hzero Φ ε k
  have hsub : univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ ⊆ Φ ⁻¹' G.exhaustion k := by
    intro z hz
    exact hk (mem_image_of_mem Φ ⟨hz.1, hz.2.1.le, hz.2.2.le⟩)
  have hsource : e.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ := by
    change (univ ∩ Φ ⁻¹' G.exhaustion k) ∩ (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) = _
    rw [univ_inter, inter_eq_right.mpr hsub]
  refine ⟨hsource, ?_, ?_, ?_⟩
  · intro z hz
    exact (((G.embedding k).spatialMap_contMDiffAt (G.exhaustion_open k)
      hzero (hsub hz)).comp z (Φ.contMDiff z)).contMDiffWithinAt
  · intro x hx
    have hxe := e.map_target hx
    rw [hsource] at hxe
    have hinverse := (G.embedding k).spatialInverse_contMDiffAt
      (G.exhaustion_open k) hzero (hsub hxe)
    have heq : ((G.embedding k).toFun (0, Φ (e.symm x))).2 = x := e.right_inv hx
    rw [heq] at hinverse
    exact ((Φ.symm.contMDiff _).comp x hinverse).contMDiffWithinAt
  · rintro _ ⟨z, hz, rfl⟩
    apply e.map_source
    rw [hsource]
    have hpos := inv_pos.mpr hε
    exact ⟨hz.1, by simpa only [mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ Ioo (-ε⁻¹) ε⁻¹ from ⟨neg_neg_of_pos hpos, hpos⟩)⟩


theorem cylinderSlabEmbedding_center (G : PointedGeometricConvergence S)
    (hzero : a < 0 ∧ 0 < b)
    (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limitCarrier.carrier)
    (ε : ℝ) (k : ℕ) (q : UnitTwoSphere) (hq : Φ (q, 0) = G.limitFlow.base) :
    G.cylinderSlabEmbedding hzero Φ ε k (q, 0) = (S.flow (G.subsequence k)).base := by
  rw [cylinderSlabEmbedding_apply, hq, G.base_preserving]

end PointedGeometricConvergence

end PoincareConjecture
