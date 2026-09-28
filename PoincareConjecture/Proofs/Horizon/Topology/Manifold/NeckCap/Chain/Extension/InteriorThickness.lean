import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceLower
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.CompactScale










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Manifold Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem edist_lower_of_axis_le_of_not_mem_carrier {p x : M} {r : ℝ}
    (hp : p ∈ N.carrier) (hr : 0 ≤ r) (hrL : r < N.epsilon⁻¹)
    (haxis : |(N.coordinate_inverse p).2| ≤ r) (hx : x ∉ N.carrier) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (N.epsilon⁻¹ - r)) ≤
      g.edist p x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hfactor : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  have hbound (s : ℝ) (hs : s ∈ Ioo r N.epsilon⁻¹) :
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (s - r)) ≤
        g.edist p x := by
    by_contra h
    have hdist : Manifold.riemannianEDist (𝓡 3) p x <
        ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (s - r)) :=
      lt_of_not_ge h
    obtain ⟨γ, hγ0, hγ1, hγ, hlength, -, -⟩ :=
      exists_lt_locally_constant_of_riemannianEDist_lt hdist (show (0 : ℝ) < 1 by norm_num)
    have hleft : -N.epsilon⁻¹ < -s := neg_lt_neg hs.2
    have hstart : γ 0 ∈ N.region (-s) s := by
      rw [hγ0]
      exact ⟨hp, by linarith [(abs_le.mp haxis).1, hs.1],
        by linarith [(abs_le.mp haxis).2, hs.1]⟩
    have hout : γ 1 ∉ N.coordinate_map '' (univ ×ˢ Icc (-s) s) := by
      rw [hγ1]
      exact fun hmem => hx ((N.mem_coordinate_slab_iff hleft hs.2).mp hmem).1
    obtain ⟨t, ht, hcarrier, hboundary, -⟩ := N.exists_initial_segment_to_slab_boundary
      (show (0 : ℝ) ≤ 1 by norm_num) hleft hs.2 hγ.continuous.continuousOn hstart hout
    have hvalue : s - r ≤ |(N.coordinate_inverse (γ t)).2 -
        (N.coordinate_inverse (γ 0)).2| := by
      rw [hγ0]
      have hb : |(N.coordinate_inverse (γ t)).2| = s := by
        rcases hboundary with hneg | hpos
        · rw [hneg, abs_neg, abs_of_nonneg (hr.trans hs.1.le)]
        · rw [hpos, abs_of_nonneg (hr.trans hs.1.le)]
      have htriangle := abs_sub_abs_le_abs_sub
        (N.coordinate_inverse (γ t)).2 (N.coordinate_inverse p).2
      rw [hb] at htriangle
      linarith
    have hax := (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left hvalue hfactor)).trans
      (N.axial_displacement_le_pathELength ht.1.le hγ hcarrier)
    have hmono : g.pathELength γ 0 t ≤ g.pathELength γ 0 1 :=
      Manifold.pathELength_mono le_rfl ht.2
    exact (not_lt_of_ge (hax.trans hmono)) hlength
  have hclosed : IsClosed {s : ℝ |
      ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (s - r)) ≤ g.edist p x} :=
    isClosed_le (ENNReal.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.sub continuous_const))) continuous_const
  have hclosure := hclosed.closure_subset_iff.mpr (show Ioo r N.epsilon⁻¹ ⊆
      {s : ℝ | ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon) * (s - r)) ≤
        g.edist p x} from hbound)
  rw [closure_Ioo hrL.ne] at hclosure
  exact hclosure ⟨hrL.le, le_rfl⟩



theorem quarter_width_le_edist_of_mem_middle_half {p x : M}
    (hp : p ∈ N.region (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2))
    (hx : x ∉ N.carrier) :
    ENNReal.ofReal (N.scale * N.epsilon⁻¹ / 4) ≤ g.edist p x := by
  have hi := inv_pos.mpr N.epsilon_pos
  have hroot : (1 / 2 : ℝ) ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith [N.epsilon_lt_half])
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon), N.epsilon_lt_half]
  have haxis : |(N.coordinate_inverse p).2| ≤ N.epsilon⁻¹ / 2 :=
    abs_le.mpr ⟨by linarith [hp.2.1], hp.2.2.le⟩
  apply (ENNReal.ofReal_le_ofReal ?_).trans
    (N.edist_lower_of_axis_le_of_not_mem_carrier hp.1 (by positivity)
      (by linarith) haxis hx)
  have h := mul_le_mul_of_nonneg_left hroot (mul_nonneg N.scale_pos.le hi.le)
  nlinarith



theorem closure_iUnion_region_subset {ι : Type*}
    (N : ι → EpsilonNeck g) {epsilon : ℝ} (hε : ∀ i, (N i).epsilon = epsilon)
    {r : ℝ} (hr : 0 ≤ r) (hrL : r < epsilon⁻¹) :
    closure (⋃ i, (N i).region (-r) r) ⊆
      ⋃ i, (N i).carrier := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp
  | inr h =>
    let i₀ : ι := Classical.choice h
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
    let : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
    intro x hx
    by_contra hout
    have hroot : 0 < Real.sqrt (1 - epsilon) := Real.sqrt_pos.mpr (by
      have hsmall := (N i₀).epsilon_lt_half
      rw [hε i₀] at hsmall
      linarith)
    obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
    obtain ⟨ρ, hρ, hbound⟩ :=
      exists_scale_lower_bound_of_meets_compact (N i₀).connection epsilon hK
    have hradius : 0 < ENNReal.ofReal (ρ * Real.sqrt (1 - epsilon) * (epsilon⁻¹ - r)) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨p, hpball, hpmid⟩ := mem_closure_iff_nhds.mp hx
      (Metric.eball x (ENNReal.ofReal (ρ * Real.sqrt (1 - epsilon) * (epsilon⁻¹ - r))) ∩ K)
      (inter_mem (Metric.eball_mem_nhds x hradius) hxK)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hpmid
    have hscale : ρ ≤ (N i).scale := hbound (N i) (hε i) ⟨p, hi.1, hpball.2⟩
    have hnot : x ∉ (N i).carrier := fun hxi => hout (mem_iUnion.mpr ⟨i, hxi⟩)
    have haxis : |((N i).coordinate_inverse p).2| ≤ r := abs_le.mpr ⟨hi.2.1.le, hi.2.2.le⟩
    have hlower := (N i).edist_lower_of_axis_le_of_not_mem_carrier hi.1 hr
      (by rwa [hε i]) haxis hnot
    rw [hε i] at hlower
    have hle : ENNReal.ofReal (ρ * Real.sqrt (1 - epsilon) * (epsilon⁻¹ - r)) ≤
        g.edist p x := by
      apply (ENNReal.ofReal_le_ofReal ?_).trans hlower
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hroot.le)
        (sub_nonneg.mpr hrL.le)
    exact (not_lt_of_ge hle) hpball.1



theorem closure_iUnion_middle_half_subset {ι : Type*}
    (N : ι → EpsilonNeck g) {epsilon : ℝ} (hε : ∀ i, (N i).epsilon = epsilon) :
    closure (⋃ i, (N i).region (-epsilon⁻¹ / 2) (epsilon⁻¹ / 2)) ⊆
      ⋃ i, (N i).carrier := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => simp
  | inr h =>
    have he := inv_pos.mpr (hε (Classical.choice h) ▸ (N (Classical.choice h)).epsilon_pos)
    simpa only [neg_div] using closure_iUnion_region_subset N hε
      (r := epsilon⁻¹ / 2) (by positivity) (by linarith)

end PoincareConjecture.EpsilonNeck
