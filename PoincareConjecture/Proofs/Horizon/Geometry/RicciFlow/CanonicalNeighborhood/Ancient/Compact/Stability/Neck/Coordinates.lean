import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Coordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23InteriorConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  (G : M23InteriorConvergence S)
  (e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j))

theorem terminalNeckEmbedding_central_sphere_image
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (ε : ℝ) (k : ℕ) :
    G.terminalNeckEmbedding e N ε k '' (univ ×ˢ ({0} : Set ℝ)) =
      (fun x => ((e k).toFun (0, x)).2) '' N.central_sphere := by
  rw [N.central_sphere_eq, image_image]
  rfl

theorem terminalNeckEmbedding_center_mem_central_image
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (ε : ℝ) (k : ℕ) :
    ((e k).toFun (0, N.center)).2 ∈
      G.terminalNeckEmbedding e N ε k '' (univ ×ˢ ({0} : Set ℝ)) := by
  rw [G.terminalNeckEmbedding_central_sphere_image]
  exact mem_image_of_mem _ N.center_on_central_sphere

theorem terminalNeckEmbedding_coordinates_of_source
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    (hsource : (G.terminalNeckEmbedding e N ε k).source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) :
    let f := G.terminalNeckEmbedding e N ε k
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) ∧
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f.symm f.target ∧
    f '' (univ ×ˢ ({0} : Set ℝ)) ⊆ f.target := by
  let f := G.terminalNeckEmbedding e N ε k
  have hpair {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) :
      z ∈ N.cylinderDomain ∧ N.coordinate_map z ∈ G.exhaustion k := by
    have hz' : z ∈ f.source := hsource.symm ▸ hz
    exact hz'.1
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact (((e k).terminalSpatialMap_contMDiffAt (G.exhaustion_open k)
      (t := 0) le_rfl (hpair hz).2).comp z
        (N.coordinate_map_smooth.contMDiffAt
          (N.cylinderDomain_open.mem_nhds (hpair hz).1))).contMDiffWithinAt
  · intro x hx
    have hxf := f.map_target hx
    rw [hsource] at hxf
    have hinverse := (e k).terminalSpatialInverse_contMDiffAt
      (G.exhaustion_open k) (t := 0) le_rfl (hpair hxf).2
    have heq : ((e k).toFun (0, N.coordinate_map (f.symm x))).2 = x := f.right_inv hx
    rw [heq] at hinverse
    have hback : ((e k).inverse (0, x)).2 = N.coordinate_map (f.symm x) := by
      have h := congrArg Prod.snd ((e k).left_inverse (0, N.coordinate_map (f.symm x))
        ⟨by simp, (hpair hxf).2⟩)
      have hpair' : (e k).toFun (0, N.coordinate_map (f.symm x)) = (0, x) :=
        Prod.ext ((e k).time_preserving _ _) heq
      simpa only [hpair'] using h
    have hxN : ((e k).inverse (0, x)).2 ∈ N.carrier := by
      rw [hback]
      exact N.coordinate_map_mem (hpair hxf).1
    exact ((N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds hxN)).comp x hinverse).contMDiffWithinAt
  · rintro _ ⟨z, hz, rfl⟩
    apply f.map_source
    rw [hsource]
    have hpos := inv_pos.mpr hε
    exact ⟨hz.1, by simpa only [mem_singleton_iff.mp hz.2] using
      (show (0 : ℝ) ∈ Ioo (-ε⁻¹) ε⁻¹ from ⟨neg_neg_of_pos hpos, hpos⟩)⟩

theorem terminalNeckEmbedding_full_source
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (k : ℕ)
    (hN : N.carrier ⊆ G.exhaustion k) :
    (G.terminalNeckEmbedding e N N.epsilon k).source = N.cylinderDomain := by
  change (N.cylinderDomain ∩ N.coordinate_map ⁻¹' G.exhaustion k) ∩ N.cylinderDomain = _
  apply inter_eq_right.mpr
  intro z hz
  exact ⟨hz, hN (N.coordinate_map_mem hz)⟩

theorem terminalNeckEmbedding_target_eq_image_region
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) {ε : ℝ} (k : ℕ)
    (hsource : (G.terminalNeckEmbedding e N ε k).source = univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) :
    (G.terminalNeckEmbedding e N ε k).target =
      (fun x => ((e k).toFun (0, x)).2) '' N.region (-ε⁻¹) ε⁻¹ := by
  let f := G.terminalNeckEmbedding e N ε k
  have hsmall {z : RoundCylinderSpace} (hz : z ∈ univ ×ˢ Ioo (-ε⁻¹) ε⁻¹) :
      z ∈ N.cylinderDomain := by
    have hz' : z ∈ f.source := hsource.symm ▸ hz
    exact hz'.1.1
  ext x
  constructor
  · intro hx
    have hz := f.map_target hx
    rw [hsource] at hz
    refine ⟨N.coordinate_map (f.symm x), ?_, f.right_inv hx⟩
    refine ⟨N.coordinate_map_mem (hsmall hz), ?_⟩
    rw [N.coordinate_inverse_coordinate_map (hsmall hz)]
    exact hz.2
  · rintro ⟨y, hy, rfl⟩
    have hz : N.coordinate_inverse y ∈ f.source := by
      rw [hsource]
      exact ⟨mem_univ _, hy.2⟩
    have h := f.map_source hz
    change ((e k).toFun (0, N.coordinate_map (N.coordinate_inverse y))).2 ∈ f.target at h
    rw [N.coordinate_map_coordinate_inverse hy.1] at h
    exact h

theorem terminalNeckEmbedding_full_target
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (k : ℕ)
    (hN : N.carrier ⊆ G.exhaustion k) :
    (G.terminalNeckEmbedding e N N.epsilon k).target =
      (fun x => ((e k).toFun (0, x)).2) '' N.carrier := by
  rw [G.terminalNeckEmbedding_target_eq_image_region e N k
    (G.terminalNeckEmbedding_full_source e N k hN)]
  congr 1
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, (N.coordinate_inverse_mem x hx).2⟩⟩

theorem terminalNeckEmbedding_full_inverse_image
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (k : ℕ)
    (hN : N.carrier ⊆ G.exhaustion k) {x : G.limit.carrier.carrier} (hx : x ∈ N.carrier) :
    (G.terminalNeckEmbedding e N N.epsilon k).symm ((e k).toFun (0, x)).2 =
      N.coordinate_inverse x := by
  let f := G.terminalNeckEmbedding e N N.epsilon k
  have hz : N.coordinate_inverse x ∈ f.source := by
    rw [G.terminalNeckEmbedding_full_source e N k hN]
    exact N.coordinate_inverse_mem x hx
  have h := f.left_inv hz
  change f.symm ((e k).toFun (0, N.coordinate_map (N.coordinate_inverse x))).2 = _ at h
  rw [N.coordinate_map_coordinate_inverse hx] at h
  exact h

theorem terminalNeckEmbedding_full_region
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (k : ℕ)
    (hN : N.carrier ⊆ G.exhaustion k) (a b : ℝ) :
    {x | x ∈ (G.terminalNeckEmbedding e N N.epsilon k).target ∧
      a < ((G.terminalNeckEmbedding e N N.epsilon k).symm x).2 ∧
      ((G.terminalNeckEmbedding e N N.epsilon k).symm x).2 < b} =
      (fun x => ((e k).toFun (0, x)).2) '' N.region a b := by
  ext x
  constructor
  · rintro ⟨hx, ha, hb⟩
    rw [G.terminalNeckEmbedding_full_target e N k hN] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [G.terminalNeckEmbedding_full_inverse_image e N k hN hy] at ha hb
    exact ⟨y, ⟨hy, ha, hb⟩, rfl⟩
  · rintro ⟨y, ⟨hy, ha, hb⟩, rfl⟩
    simp only [mem_ofPred_eq]
    rw [G.terminalNeckEmbedding_full_inverse_image e N k hN hy,
      G.terminalNeckEmbedding_full_target e N k hN]
    exact ⟨mem_image_of_mem _ hy, ha, hb⟩

theorem eventually_terminalNeckEmbedding_full
    (N : EpsilonNeck (G.limit.flow.flow.metric 0)) (hN : IsCompact (closure N.carrier)) :
    ∀ᶠ k in atTop,
      let f := G.terminalNeckEmbedding e N N.epsilon k
      f.source = N.cylinderDomain ∧
      f.target = (fun x => ((e k).toFun (0, x)).2) '' N.carrier ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f N.cylinderDomain ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f.symm f.target ∧
      f '' (univ ×ˢ ({0} : Set ℝ)) ⊆ f.target := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hN
  filter_upwards [eventually_ge_atTop j] with k hk
  have hcarrier : N.carrier ⊆ G.exhaustion k :=
    subset_closure.trans (hj.trans (G.exhaustion_monotone hk))
  have hsource := G.terminalNeckEmbedding_full_source e N k hcarrier
  exact ⟨hsource, G.terminalNeckEmbedding_full_target e N k hcarrier,
    G.terminalNeckEmbedding_coordinates_of_source e N N.epsilon_pos k hsource⟩

end M23InteriorConvergence

end PoincareConjecture
