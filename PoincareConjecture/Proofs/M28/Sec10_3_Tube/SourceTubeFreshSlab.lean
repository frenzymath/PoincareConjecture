import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeShortPathCapture
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.ThreeQuarterSlabCompetitors

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28.SourceTubeData

variable {epsilon C A D0 D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D0 D}
  {S : CounterexampleNeckSegment E}

theorem exists_central_slab_competitor_in_tube (T : SourceTubeData S)
    (hsmall : epsilon ≤ (1 / 10000 : ℝ)) (f : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hbound : ∀ q, |f q| < epsilon⁻¹ / 32)
    (N : EpsilonNeck (E.flow.metric E.time)) (heps : N.epsilon = epsilon)
    (hscale : N.scale ≤ (101 / 100 : ℝ) * (T.list.node 0).2.scale)
    {p : (E.flow.slice E.time).carrier} (hp : p ∈ N.central_sphere)
    (hpT : p ∈ (T.carrierOpen : Set _))
    (hside : p ∉ (T.list.node 0).2.belowGraph_m28 f)
    (hterminal : Disjoint N.carrier
      (closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)))
    {x : (E.flow.slice E.time).carrier} (hx : x ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x).2| ≤ 3 * epsilon⁻¹ / 4) :
    ∃ gamma : ℝ → (E.flow.slice E.time).carrier,
      gamma 0 = p ∧ gamma 1 = x ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc (0 : ℝ) 1) ∧
      MapsTo gamma (Icc (0 : ℝ) 1) N.carrier ∧
      MapsTo gamma (Icc (0 : ℝ) 1) (T.carrierOpen : Set _) ∧
      (E.flow.metric E.time).pathELength gamma 0 1 <
        ENNReal.ofReal ((151 / 200 : ℝ) * N.scale * epsilon⁻¹) := by
  have hepspos : 0 < epsilon := heps ▸ N.epsilon_pos
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr hepspos
  obtain ⟨gamma, h0, h1, hgamma, hN, hlength⟩ := N.exists_three_quarter_slab_competitor
    (by rwa [heps]) hp hx (by rwa [heps])
  rw [heps] at hlength
  have hroot : (99 / 100 : ℝ) ≤ Real.sqrt (1 - epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - epsilon)]
  have hscale0 := (T.list.node 0).2.scale_pos
  have hupper := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 151 / 200)) hA.le
  have hlower := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hroot hscale0.le)
    (by positivity : 0 ≤ 27 * epsilon⁻¹ / 32)
  have hgap : (151 / 200 : ℝ) * N.scale * epsilon⁻¹ <
      ((T.list.node 0).2.scale * Real.sqrt (1 - epsilon)) * (27 * epsilon⁻¹ / 32) := by
    nlinarith only [hupper, hlower, mul_pos hscale0 hA]
  have hT := T.short_path_mapsTo_of_terminal_avoidance (by linarith) f hf hbound
    hgamma (by rwa [h0]) (by rwa [h0])
    (fun t ht => Set.disjoint_left.mp hterminal (hN ht))
    (hlength.trans_le (ENNReal.ofReal_le_ofReal hgap.le))
  exact ⟨gamma, h0, h1, hgamma, hN, hT, hlength⟩

theorem exists_fresh_slab_competitor_in_tube (T : SourceTubeData S)
    (hsmall : epsilon ≤ (1 / 10000 : ℝ)) (f : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hbound : ∀ q, |f q| < epsilon⁻¹ / 32)
    (N : EpsilonNeck (E.flow.metric E.time)) (heps : N.epsilon = epsilon)
    (hscale : N.scale ≤ (101 / 100 : ℝ) * (T.list.node 0).2.scale)
    (hcenter : N.center ∈ (T.carrierOpen : Set _))
    (hside : N.center ∉ (T.list.node 0).2.belowGraph_m28 f)
    (hterminal : Disjoint N.carrier
      (closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)))
    {x : (E.flow.slice E.time).carrier} (hx : x ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x).2| ≤ 3 * epsilon⁻¹ / 4) :
    ∃ gamma : ℝ → (E.flow.slice E.time).carrier,
      gamma 0 = N.center ∧ gamma 1 = x ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc (0 : ℝ) 1) ∧
      MapsTo gamma (Icc (0 : ℝ) 1) N.carrier ∧
      MapsTo gamma (Icc (0 : ℝ) 1) (T.carrierOpen : Set _) ∧
      (E.flow.metric E.time).pathELength gamma 0 1 <
        ENNReal.ofReal ((151 / 200 : ℝ) * N.scale * epsilon⁻¹) :=
  T.exists_central_slab_competitor_in_tube hsmall f hf hbound N heps hscale
    N.center_on_central_sphere hcenter hside hterminal hx hheight

theorem fresh_three_quarter_slab_subset (T : SourceTubeData S)
    (hsmall : epsilon ≤ (1 / 10000 : ℝ)) (f : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hbound : ∀ q, |f q| < epsilon⁻¹ / 32)
    (N : EpsilonNeck (E.flow.metric E.time)) (heps : N.epsilon = epsilon)
    (hscale : N.scale ≤ (101 / 100 : ℝ) * (T.list.node 0).2.scale)
    (hcenter : N.center ∈ (T.carrierOpen : Set _))
    (hside : N.center ∉ (T.list.node 0).2.belowGraph_m28 f)
    (hterminal : Disjoint N.carrier
      (closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier))) :
    N.coordinate_map '' (univ ×ˢ Icc (-(3 * epsilon⁻¹ / 4)) (3 * epsilon⁻¹ / 4)) ⊆
      (T.carrierOpen : Set _) := by
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr (heps ▸ N.epsilon_pos)
  rintro _ ⟨z, hz, rfl⟩
  have hzdom : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [heps]
    constructor <;> linarith [hz.2.1, hz.2.2]
  have hheight : |(N.coordinate_inverse (N.coordinate_map z)).2| ≤
      3 * epsilon⁻¹ / 4 := by
    rw [N.coordinate_inverse_coordinate_map_of_axial z hzdom]
    exact abs_le.mpr hz.2
  obtain ⟨gamma, _, h1, _, _, hT, _⟩ := T.exists_fresh_slab_competitor_in_tube
    hsmall f hf hbound N heps hscale hcenter hside hterminal
    (N.coordinate_map_mem_of_axial z hzdom) hheight
  simpa only [h1] using hT (right_mem_Icc.mpr zero_le_one)

end PoincareConjecture.M28.SourceTubeData
