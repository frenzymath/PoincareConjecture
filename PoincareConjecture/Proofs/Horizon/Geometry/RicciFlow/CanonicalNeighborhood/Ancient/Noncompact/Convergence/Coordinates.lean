import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Embeddings
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalCoordinateCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

namespace NormalizedKappaSpacetimeEmbedding

variable {kappa : ℝ} {source target : BasedKappaSolution kappa}
  {U : Set target.carrier.carrier}
  (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target)
    (Iic 0 ×ˢ U))

theorem terminalSpatialMap_contMDiffAt (hU : IsOpen U)
    {t : ℝ} (ht : t ≤ 0) {x : target.carrier.carrier} (hx : x ∈ U) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y => (e.toFun (t, y)).2) x :=
  (e.contMDiffOn_terminalSpatialMap ht).contMDiffAt (hU.mem_nhds hx)

theorem terminalSpatialMap_mfderiv_injective (hU : IsOpen U)
    {t : ℝ} (ht : t ≤ 0) {x : target.carrier.carrier} (hx : x ∈ U) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun y => (e.toFun (t, y)).2) x) := by
  let f := fun y => (e.toFun (t, y)).2
  let g := fun y => (e.inverse (t, y)).2
  have hpair (y : target.carrier.carrier) : e.toFun (t, y) = (t, f y) :=
    Prod.ext (e.time_preserving t y) rfl
  have hmaps : MapsTo (fun y : source.carrier.carrier => (t, y)) (f '' U)
      (e.toFun '' (Iic 0 ×ˢ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(t, y), ⟨ht, hy⟩, hpair y⟩
  have hinv : ContMDiffWithinAt (𝓡 3) (𝓡 3) ∞ g (f '' U) (f x) := by
    have hs := e.smooth_inverse_on (t, f x) (hmaps ⟨x, hx, rfl⟩)
    exact (hs.comp (f x) (contMDiffWithinAt_const.prodMk contMDiffWithinAt_id) hmaps).snd
  have hleft : ∀ y ∈ U, (g ∘ f) y = id y := by
    intro y hy
    have h := congrArg Prod.snd (e.left_inverse (t, y) ⟨ht, hy⟩)
    simpa only [hpair, Function.comp_apply, id_eq, g] using h
  have hf : MDifferentiableAt (𝓡 3) (𝓡 3) f x :=
    (e.terminalSpatialMap_contMDiffAt hU ht hx).mdifferentiableAt (by simp)
  have hu : UniqueMDiffWithinAt (𝓡 3) U x := hU.uniqueMDiffWithinAt hx
  have hcomp := mfderivWithin_comp x (hinv.mdifferentiableWithinAt (by simp))
    hf.mdifferentiableWithinAt (fun y hy => ⟨y, hy, rfl⟩) hu
  rw [mfderivWithin_congr_of_mem hleft hx, mfderivWithin_id hu,
    mfderivWithin_eq_mfderiv hu hf] at hcomp
  intro v w hvw
  have h := congrArg (mfderivWithin (𝓡 3) (𝓡 3) g (f '' U) (f x)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hcomp] at h
  exact h

theorem terminalSpatialMap_mfderiv_bijective (hU : IsOpen U)
    {t : ℝ} (ht : t ≤ 0) {x : target.carrier.carrier} (hx : x ∈ U) :
    Function.Bijective (mfderiv (𝓡 3) (𝓡 3) (fun y => (e.toFun (t, y)).2) x) := by
  have hi := e.terminalSpatialMap_mfderiv_injective hU ht hx
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 3) x) =
      Module.finrank ℝ (TangentSpace (𝓡 3) ((e.toFun (t, x)).2)) := rfl
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.finiteDimensional_of_finite
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) ((e.toFun (t, x)).2)) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.finiteDimensional_of_finite
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hi⟩

theorem terminalSpatialMap_isOpen_image (hU : IsOpen U)
    {t : ℝ} (ht : t ≤ 0) : IsOpen ((fun y => (e.toFun (t, y)).2) '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    (e.terminalSpatialMap_contMDiffAt hU ht hx)
    (e.terminalSpatialMap_mfderiv_bijective hU ht hx)]
  exact image_mem_map (hU.mem_nhds hx)

theorem terminalSpatialInverse_contMDiffAt (hU : IsOpen U)
    {t : ℝ} (ht : t ≤ 0) {x : target.carrier.carrier} (hx : x ∈ U) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y => (e.inverse (t, y)).2)
      (e.toFun (t, x)).2 := by
  let f := fun y => (e.toFun (t, y)).2
  have hmaps : MapsTo (fun y : source.carrier.carrier => (t, y)) (f '' U)
      (e.toFun '' (Iic 0 ×ˢ U)) := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨(t, z), ⟨ht, hz⟩, Prod.ext (e.time_preserving t z) rfl⟩
  have hs := e.smooth_inverse_on.comp
    (contMDiff_const.prodMk contMDiff_id).contMDiffOn hmaps
  exact (hs (f x) (mem_image_of_mem f hx)).snd.contMDiffAt
    ((e.terminalSpatialMap_isOpen_image hU ht).mem_nhds (mem_image_of_mem f hx))


noncomputable def terminalSpatialHomeomorph (hU : IsOpen U)
    {t : ℝ} (ht : t ≤ 0) :
    OpenPartialHomeomorph target.carrier.carrier source.carrier.carrier := by
  let f := fun x => (e.toFun (t, x)).2
  let f' := fun y => (e.inverse (t, y)).2
  have hleft (x : target.carrier.carrier) (hx : x ∈ U) : f' (f x) = x := by
    have hp : e.toFun (t, x) = (t, f x) := Prod.ext (e.time_preserving t x) rfl
    simpa only [hp] using congrArg Prod.snd (e.left_inverse (t, x) ⟨ht, hx⟩)
  exact {
    toFun := f
    invFun := f'
    source := U
    target := f '' U
    map_source' := fun x hx => mem_image_of_mem f hx
    map_target' := by rintro _ ⟨x, hx, rfl⟩; simpa only [hleft x hx] using hx
    left_inv' := hleft
    right_inv' := by rintro _ ⟨x, hx, rfl⟩; rw [hleft x hx]
    open_source := hU
    open_target := e.terminalSpatialMap_isOpen_image hU ht
    continuousOn_toFun := fun x hx =>
      (e.terminalSpatialMap_contMDiffAt hU ht hx).continuousAt.continuousWithinAt
    continuousOn_invFun := by
      rintro _ ⟨x, hx, rfl⟩
      exact (e.terminalSpatialInverse_contMDiffAt hU ht hx).continuousAt.continuousWithinAt }

end NormalizedKappaSpacetimeEmbedding

namespace M23InteriorConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  (G : M23InteriorConvergence S)
  (e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j))


noncomputable def terminalNeckEmbedding
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (ε : ℝ) (k : ℕ) :
    OpenPartialHomeomorph RoundCylinderSpace (S.term (G.subsequence k)).carrier.carrier :=
  (N.coordinatePartialHomeomorph.trans
    ((e k).terminalSpatialHomeomorph (G.exhaustion_open k) (t := 0) le_rfl)).restrOpen
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) (isOpen_univ.prod isOpen_Ioo)

@[simp] theorem terminalNeckEmbedding_apply
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (ε : ℝ) (k : ℕ)
    (z : RoundCylinderSpace) :
    G.terminalNeckEmbedding e N ε k z = ((e k).toFun (0, N.coordinate_map z)).2 := rfl

@[simp] theorem terminalNeckEmbedding_symm_apply
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (ε : ℝ) (k : ℕ)
    (x : (S.term (G.subsequence k)).carrier.carrier) :
    (G.terminalNeckEmbedding e N ε k).symm x =
      N.coordinate_inverse ((e k).inverse (0, x)).2 := rfl

theorem closedSmallerNeckCylinder_subset
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) {ε : ℝ} (hε : N.epsilon < ε) :
    univ ×ˢ Icc (-ε⁻¹) ε⁻¹ ⊆ N.cylinderDomain := by
  have hinv : ε⁻¹ < N.epsilon⁻¹ :=
    (inv_lt_inv₀ (N.epsilon_pos.trans hε) N.epsilon_pos).mpr hε
  intro z hz
  exact ⟨hz.1, (neg_lt_neg hinv).trans_le hz.2.1, hz.2.2.trans_lt hinv⟩


theorem eventually_terminalNeckCylinder_subset_exhaustion
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) {ε : ℝ} (hε : N.epsilon < ε) :
    ∀ᶠ k in atTop, N.coordinate_map '' (univ ×ˢ Icc (-ε⁻¹) ε⁻¹) ⊆ G.exhaustion k := by
  have hcompact : IsCompact (univ ×ˢ Icc (-ε⁻¹) ε⁻¹ : Set RoundCylinderSpace) :=
    isCompact_univ.prod isCompact_Icc
  have hsmooth := N.coordinate_map_smooth.mono (G.closedSmallerNeckCylinder_subset N hε)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (hcompact.image_of_continuousOn hsmooth.continuousOn)
  exact (eventually_ge_atTop j).mono fun k hk => hj.trans (G.exhaustion_monotone hk)



theorem eventually_terminalNeckEmbedding
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) {ε : ℝ} (hε : N.epsilon < ε) :
    ∀ᶠ k in atTop,
      let f := G.terminalNeckEmbedding e N ε k
      f.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
        (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f.symm f.target ∧
      f '' (univ ×ˢ ({0} : Set ℝ)) ⊆ f.target := by
  filter_upwards [G.eventually_terminalNeckCylinder_subset_exhaustion N hε] with k hk
  let f := G.terminalNeckEmbedding e N ε k
  have hsmall : univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ ⊆ N.cylinderDomain :=
    (prod_mono subset_rfl Ioo_subset_Icc_self).trans
      (G.closedSmallerNeckCylinder_subset N hε)
  have hsub : univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ ⊆ N.coordinate_map ⁻¹' G.exhaustion k := by
    intro z hz
    exact hk (mem_image_of_mem N.coordinate_map ⟨hz.1, hz.2.1.le, hz.2.2.le⟩)
  have hsource : f.source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ := by
    change (N.cylinderDomain ∩ N.coordinate_map ⁻¹' G.exhaustion k) ∩
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) = _
    exact inter_eq_right.mpr fun z hz => ⟨hsmall hz, hsub hz⟩
  refine ⟨hsource, ?_, ?_, ?_⟩
  · intro z hz
    exact (((e k).terminalSpatialMap_contMDiffAt (G.exhaustion_open k)
      (t := 0) le_rfl (hsub hz)).comp z
        (N.coordinate_map_smooth.contMDiffAt
          (N.cylinderDomain_open.mem_nhds (hsmall hz)))).contMDiffWithinAt
  · intro x hx
    have hxf := f.map_target hx
    rw [hsource] at hxf
    have hinverse := (e k).terminalSpatialInverse_contMDiffAt
      (G.exhaustion_open k) (t := 0) le_rfl (hsub hxf)
    have heq : ((e k).toFun (0, N.coordinate_map (f.symm x))).2 = x := f.right_inv hx
    rw [heq] at hinverse
    have hback : ((e k).inverse (0, x)).2 = N.coordinate_map (f.symm x) := by
      have h := congrArg Prod.snd ((e k).left_inverse (0, N.coordinate_map (f.symm x))
        ⟨by simp, hsub hxf⟩)
      have hpair : (e k).toFun (0, N.coordinate_map (f.symm x)) = (0, x) :=
        Prod.ext ((e k).time_preserving _ _) heq
      simpa only [hpair] using h
    have hxN : ((e k).inverse (0, x)).2 ∈ N.carrier := by
      rw [hback]
      exact N.coordinate_map_mem (hsmall hxf)
    exact ((N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds hxN)).comp x hinverse).contMDiffWithinAt
  · rintro _ ⟨z, hz, rfl⟩
    apply f.map_source
    rw [hsource]
    have hpos := inv_pos.mpr (N.epsilon_pos.trans hε)
    exact ⟨hz.1, by simpa only [mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ Ioo (-ε⁻¹) ε⁻¹ from ⟨neg_neg_of_pos hpos, hpos⟩)⟩


theorem terminalNeckEmbedding_center
    (hbase : ∀ k, (e k).toFun (0, G.limit.base) = (0, (S.term (G.subsequence k)).base))
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (ε : ℝ) (k : ℕ)
    (q : UnitTwoSphere) (hq : N.coordinate_map (q, 0) = G.limit.base) :
    G.terminalNeckEmbedding e N ε k (q, 0) = (S.term (G.subsequence k)).base := by
  rw [terminalNeckEmbedding_apply, hq, hbase]

end M23InteriorConvergence

end PoincareConjecture
