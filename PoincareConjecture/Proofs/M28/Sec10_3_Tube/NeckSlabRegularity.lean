import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapBoundarySlabEscape
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricBalls
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.Regularity













set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.EpsilonNeck

open M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}




theorem ball_subset_centered_region (N : EpsilonNeck g) {p : M}
    (hp : p ∈ N.carrier) {r : ℝ} (hr : 0 < r)
    (hrA : r < N.epsilon⁻¹ - |(N.coordinate_inverse p).2|) :
    g.ball p ((N.scale * Real.sqrt (1 - N.epsilon)) * r) ⊆
      N.region ((N.coordinate_inverse p).2 - r)
        ((N.coordinate_inverse p).2 + r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let h : ℝ := (N.coordinate_inverse p).2
  let W : Set M := N.region (h - r) (h + r)
  let K : Set M := N.coordinate_map '' (univ ×ˢ Icc (h - r) (h + r))
  have hlo : -N.epsilon⁻¹ < h - r := by
    have habs := neg_abs_le h
    change r < N.epsilon⁻¹ - |h| at hrA
    linarith
  have hhi : h + r < N.epsilon⁻¹ := by
    have habs := le_abs_self h
    change r < N.epsilon⁻¹ - |h| at hrA
    linarith
  have hW : IsOpen W := N.region_open _ _
  have hK : IsCompact K := N.isCompact_coordinate_slab_intrinsic hlo hhi
  have hKN : K ⊆ N.carrier := N.coordinate_slab_subset_carrier_m28 hlo hhi
  have hWK : W ⊆ K := by
    intro x hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hx.1⟩
  have hclosure : closure W ⊆ K := closure_minimal hWK hK.isClosed
  have hpW : p ∈ W := by
    change p ∈ N.carrier ∧ h - r < h ∧ h < h + r
    exact ⟨hp, by linarith, by linarith⟩
  intro x hx
  obtain ⟨γ, h0, h1, hγ, hlength⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hx
  change x ∈ W
  by_contra hxW
  let T : Set ℝ := Icc 0 1 ∩ γ ⁻¹' Wᶜ
  have hT : IsCompact T := isCompact_Icc.of_isClosed_subset
    (hγ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hW.isClosed_compl)
    inter_subset_left
  obtain ⟨t, ht, hleast⟩ := hT.exists_isLeast
    ⟨1, right_mem_Icc.mpr zero_le_one, by
      change γ 1 ∉ W
      simpa only [h1] using hxW⟩
  have ht0 : 0 < t := lt_of_le_of_ne ht.1.1 (by
    intro heq
    apply ht.2
    simpa only [← heq, h0] using hpW)
  have hprefix : MapsTo γ (Ico 0 t) W := by
    intro s hs
    by_contra hsW
    have hts : t ≤ s := hleast ⟨⟨hs.1, hs.2.le.trans ht.1.2⟩, hsW⟩
    exact (not_lt_of_ge hts) hs.2
  have hγprefix : ContinuousOn γ (closure (Ico 0 t)) := by
    rw [closure_Ico ht0.ne]
    exact hγ.continuousOn.mono (Icc_subset_Icc le_rfl ht.1.2)
  have hprefixClosed : MapsTo γ (Icc 0 t) (closure W) := by
    simpa only [closure_Ico ht0.ne] using hprefix.closure_of_continuousOn hγprefix
  have hprefixN : MapsTo γ (Icc 0 t) N.carrier :=
    fun s hs => hKN (hclosure (hprefixClosed hs))
  have hshort : g.pathELength γ 0 t <
      ENNReal.ofReal ((N.scale * Real.sqrt (1 - N.epsilon)) * r) :=
    (Manifold.pathELength_mono le_rfl ht.1.2).trans_lt hlength
  have hinside := path_endpoint_mem_slab_of_short_length N ht0.le
    (hγ.mono (Icc_subset_Icc le_rfl ht.1.2)) hprefixN hr
    (by simpa only [h0] using hrA) hshort
  apply ht.2
  simpa only [h0] using hinside




theorem precompact_ball_of_axial_margin (N : EpsilonNeck g) {p : M}
    (hp : p ∈ N.carrier) {r : ℝ}
    (hr : r < (N.scale * Real.sqrt (1 - N.epsilon)) *
      (N.epsilon⁻¹ - |(N.coordinate_inverse p).2|)) :
    IsCompact (closure (g.ball p r)) ∧ closure (g.ball p r) ⊆ N.carrier := by
  by_cases hr0 : r ≤ 0
  · have hball : g.ball p r = ∅ := by
      ext x
      simp [RiemannianMetric.ball, ENNReal.ofReal_eq_zero.mpr hr0]
    rw [hball, closure_empty]
    exact ⟨isCompact_empty, empty_subset _⟩
  have hrpos : 0 < r := lt_of_not_ge hr0
  let c : ℝ := N.scale * Real.sqrt (1 - N.epsilon)
  let h : ℝ := (N.coordinate_inverse p).2
  have hc : 0 < c := mul_pos N.scale_pos
    (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  have hratio : r / c < N.epsilon⁻¹ - |h| := by
    apply (div_lt_iff₀ hc).mpr
    change r < c * (N.epsilon⁻¹ - |h|) at hr
    nlinarith only [hr]
  obtain ⟨w, hrw, hw⟩ := exists_between hratio
  have hw0 : 0 < w := (div_pos hrpos hc).trans hrw
  have hrw' : r < c * w := by
    have hmul := (div_lt_iff₀ hc).mp hrw
    nlinarith only [hmul]
  have hlo : -N.epsilon⁻¹ < h - w := by
    have habs := neg_abs_le h
    linarith
  have hhi : h + w < N.epsilon⁻¹ := by
    have habs := le_abs_self h
    linarith
  let K : Set M := N.coordinate_map '' (univ ×ˢ Icc (h - w) (h + w))
  have hK : IsCompact K := N.isCompact_coordinate_slab_intrinsic hlo hhi
  have hballK : g.ball p r ⊆ K := by
    intro x hx
    have hinside := N.ball_subset_centered_region hp hw0 hw
      (hx.trans_le (ENNReal.ofReal_le_ofReal hrw'.le))
    exact ⟨N.coordinate_inverse x,
      ⟨mem_univ _, hinside.2.1.le, hinside.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hinside.1⟩
  have hclosure : closure (g.ball p r) ⊆ K := closure_minimal hballK hK.isClosed
  exact ⟨hK.of_isClosed_subset isClosed_closure hclosure,
    hclosure.trans (N.coordinate_slab_subset_carrier_m28 hlo hhi)⟩



theorem mem_regularPoints_of_axial_margin (N : EpsilonNeck g) {p : M}
    (hp : p ∈ N.carrier) :
    p ∈ regularPoints g ((N.scale * Real.sqrt (1 - N.epsilon)) *
      (N.epsilon⁻¹ - |(N.coordinate_inverse p).2|)) := by
  intro r hr
  exact (N.precompact_ball_of_axial_margin hp hr).1



theorem central_sphere_subset_regularPoints (N : EpsilonNeck g) :
    N.central_sphere ⊆
      regularPoints g (N.scale * Real.sqrt (1 - N.epsilon) * N.epsilon⁻¹) := by
  intro p hp
  have hzero : (N.coordinate_inverse p).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier (N.central_sphere_subset hp)).mp hp
  simpa only [hzero, abs_zero, sub_zero] using
    N.mem_regularPoints_of_axial_margin (N.central_sphere_subset hp)




theorem mem_regularPoints_of_three_quarter (N : EpsilonNeck g) {p : M}
    (hp : p ∈ N.carrier)
    (hquarter : |(N.coordinate_inverse p).2| ≤ 3 * N.epsilon⁻¹ / 4) :
    p ∈ regularPoints g
      (N.scale * Real.sqrt (1 - N.epsilon) * N.epsilon⁻¹ / 4) := by
  have hmargin : N.epsilon⁻¹ / 4 ≤
      N.epsilon⁻¹ - |(N.coordinate_inverse p).2| := by linarith
  have hfactor : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  apply regularPoints_antitone g _ (N.mem_regularPoints_of_axial_margin hp)
  nlinarith only [mul_le_mul_of_nonneg_left hmargin hfactor]




theorem mem_regularPoints_intrinsicOpenMetric_of_axial_margin
    (N : EpsilonNeck g) (V : TopologicalSpace.Opens M)
    (hNV : N.carrier ⊆ (V : Set M)) (p : V) (hp : (p : M) ∈ N.carrier) :
    p ∈ regularPoints (intrinsicOpenMetric g V)
      ((N.scale * Real.sqrt (1 - N.epsilon)) *
        (N.epsilon⁻¹ - |(N.coordinate_inverse (p : M)).2|)) := by
  intro r hr
  obtain ⟨hcompact, hcarrier⟩ := N.precompact_ball_of_axial_margin hp hr
  have hclosure : closure (g.ball (p : M) r) ⊆ (V : Set M) := hcarrier.trans hNV
  have hball : g.ball (p : M) r ⊆ (V : Set M) := subset_closure.trans hclosure
  rw [intrinsicOpenMetric_closure_ball_eq_preimage g V p hball]
  apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hcompact
  intro x hx
  exact ⟨⟨x, hclosure hx⟩, rfl⟩




theorem mem_regularPoints_intrinsicOpenMetric_of_three_quarter
    (N : EpsilonNeck g) (V : TopologicalSpace.Opens M)
    (hNV : N.carrier ⊆ (V : Set M)) (p : V) (hp : (p : M) ∈ N.carrier)
    (hquarter : |(N.coordinate_inverse (p : M)).2| ≤ 3 * N.epsilon⁻¹ / 4) :
    p ∈ regularPoints (intrinsicOpenMetric g V)
      (N.scale * Real.sqrt (1 - N.epsilon) * N.epsilon⁻¹ / 4) := by
  have hmargin : N.epsilon⁻¹ / 4 ≤
      N.epsilon⁻¹ - |(N.coordinate_inverse (p : M)).2| := by linarith
  have hfactor : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)
  apply regularPoints_antitone (intrinsicOpenMetric g V) _
    (N.mem_regularPoints_intrinsicOpenMetric_of_axial_margin V hNV p hp)
  nlinarith only [mul_le_mul_of_nonneg_left hmargin hfactor]

end PoincareConjecture.EpsilonNeck
