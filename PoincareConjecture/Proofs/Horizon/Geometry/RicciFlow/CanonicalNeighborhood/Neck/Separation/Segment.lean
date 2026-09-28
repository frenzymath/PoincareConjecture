import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Uniqueness
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
private theorem exists_initial_segment_in_closed_set
    {γ : ℝ → M} {L : ℝ} (hL : 0 ≤ L)
    {U K : Set M} (hU : IsOpen U) (hK : IsClosed K) (hUK : U ⊆ K)
    (hγ : ContinuousOn γ (Icc 0 L)) (hstart : γ 0 ∈ U) (hout : γ L ∉ K) :
    ∃ t ∈ Ioc 0 L, γ t ∈ K ∧ γ t ∉ U ∧ MapsTo γ (Ico 0 t) U := by
  let S : Set ℝ := Icc 0 L ∩ γ ⁻¹' Uᶜ
  have hSclosed : IsClosed S :=
    hγ.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl
  have hSne : S.Nonempty := ⟨L, ⟨⟨hL, le_rfl⟩, fun h => hout (hUK h)⟩⟩
  have hSbdd : BddBelow S := ⟨0, fun _ ht => ht.1.1⟩
  let t := sInf S
  have htS : t ∈ S := hSclosed.csInf_mem hSne hSbdd
  have ht : t ∈ Ioc 0 L := ⟨lt_of_le_of_ne htS.1.1 (by
    intro heq
    exact htS.2 (heq ▸ hstart)), htS.1.2⟩
  have hbefore : MapsTo γ (Ico 0 t) U := by
    intro s hs
    by_contra hnot
    have hsS : s ∈ S := ⟨⟨hs.1, hs.2.le.trans ht.2⟩, hnot⟩
    exact (not_le_of_gt hs.2) (csInf_le hSbdd hsS)
  have htK : γ t ∈ K := by
    have hpre : IsClosed (Icc 0 L ∩ γ ⁻¹' K) :=
      hγ.preimage_isClosed_of_isClosed isClosed_Icc hK
    have hsub : Ico 0 t ⊆ Icc 0 L ∩ γ ⁻¹' K :=
      fun s hs => ⟨⟨hs.1, hs.2.le.trans ht.2⟩, hUK (hbefore hs)⟩
    have hmem : t ∈ Icc 0 L ∩ γ ⁻¹' K := by
      apply hpre.closure_subset_iff.mpr hsub
      rw [closure_Ico (ne_of_lt ht.1)]
      exact ⟨ht.1.le, le_rfl⟩
    exact hmem.2
  exact ⟨t, ht, htK, htS.2, hbefore⟩

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] in
theorem mem_coordinate_slab_iff {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹) {x : M} :
    x ∈ N.coordinate_map '' (univ ×ˢ Icc a b) ↔
      x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ∈ Icc a b := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hzN : z ∈ N.cylinderDomain :=
      ⟨mem_univ _, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩
    refine ⟨N.coordinate_map_mem hzN, ?_⟩
    rw [N.coordinate_inverse_coordinate_map hzN]
    exact hz.2
  · rintro ⟨hx, haxis⟩
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, haxis⟩,
      N.coordinate_map_coordinate_inverse hx⟩

theorem exists_initial_segment_to_slab_boundary {γ : ℝ → M} {L a b : ℝ}
    (hL : 0 ≤ L) (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹)
    (hγ : ContinuousOn γ (Icc 0 L)) (hstart : γ 0 ∈ N.region a b)
    (hout : γ L ∉ N.coordinate_map '' (univ ×ˢ Icc a b)) :
    ∃ t ∈ Ioc 0 L, MapsTo γ (Icc 0 t) N.carrier ∧
      ((N.coordinate_inverse (γ t)).2 = a ∨ (N.coordinate_inverse (γ t)).2 = b) ∧
      MapsTo γ (Ico 0 t) (N.region a b) := by
  have hsub : N.region a b ⊆ N.coordinate_map '' (univ ×ˢ Icc a b) := by
    intro x hx
    exact (N.mem_coordinate_slab_iff ha hb).mpr ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  obtain ⟨t, ht, htK, htU, hbefore⟩ := exists_initial_segment_in_closed_set
    hL (N.isOpen_region a b) (N.isCompact_coordinate_slab ha hb).isClosed
    hsub hγ hstart hout
  have htcoord := (N.mem_coordinate_slab_iff ha hb).mp htK
  refine ⟨t, ht, ?_, ?_, hbefore⟩
  · intro s hs
    rcases hs.2.eq_or_lt with rfl | hst
    · exact htcoord.1
    · exact (hbefore ⟨hs.1, hst⟩).1
  · by_contra hne
    push Not at hne
    exact htU ⟨htcoord.1, lt_of_le_of_ne htcoord.2.1 hne.1.symm,
      lt_of_le_of_ne htcoord.2.2 hne.2⟩

theorem exists_initial_segment_to_half_neck {γ : ℝ → M} {L : ℝ}
    (hL : 0 ≤ L) (hε : N.epsilon ≤ 1 / 4)
    (hγ : ContinuousOn γ (Icc 0 L)) (hstart : γ 0 ∈ N.carrier)
    (haxis0 : |(N.coordinate_inverse (γ 0)).2| ≤ 1)
    (hout : γ L ∉ N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2))) :
    ∃ t ∈ Ioc 0 L, MapsTo γ (Icc 0 t) N.carrier ∧
      |(N.coordinate_inverse (γ t)).2| = N.epsilon⁻¹ / 2 ∧
      MapsTo γ (Ico 0 t) (N.region (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) := by
  have hi : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hi4 : 4 ≤ N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ N.epsilon_pos).mpr
    linarith
  have ha : -N.epsilon⁻¹ < -N.epsilon⁻¹ / 2 := by linarith
  have hb : N.epsilon⁻¹ / 2 < N.epsilon⁻¹ := by linarith
  have hstart' : γ 0 ∈ N.region (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2) :=
    ⟨hstart, by linarith [(abs_le.mp haxis0).1], by linarith [(abs_le.mp haxis0).2]⟩
  obtain ⟨t, ht, hcarrier, hboundary, hbefore⟩ :=
    N.exists_initial_segment_to_slab_boundary hL ha hb hγ hstart' hout
  refine ⟨t, ht, hcarrier, ?_, hbefore⟩
  rcases hboundary with hboundary | hboundary
  · rw [hboundary, abs_of_neg (by linarith)]
    ring
  · rw [hboundary, abs_of_pos (by positivity)]

omit [T2Space M] in

theorem axial_displacement_le_of_unit_speed {γ : ℝ → M} {L : ℝ}
    (hL : 0 ≤ L) (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hcarrier : MapsTo γ (Icc 0 L) N.carrier)
    (hspeed : ∀ t ∈ Icc 0 L,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1) :
    |(N.coordinate_inverse (γ L)).2 - (N.coordinate_inverse (γ 0)).2| ≤
      (N.scale * Real.sqrt (1 - N.epsilon))⁻¹ * L := by
  let f : ℝ → ℝ := fun t => (N.coordinate_inverse (γ t)).2
  let v : ℝ → ℝ := fun t =>
    mvfderiv (𝓡 3) (fun x => (N.coordinate_inverse x).2) (γ t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
  have hv (t : ℝ) (ht : t ∈ Icc 0 L) : HasDerivAt f (v t) t := by
    have hi := (N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds (hcarrier ht))).snd.mdifferentiableAt (by simp)
    have hg := (hγ.contMDiffAt ht).mdifferentiableAt one_ne_zero
    have hd := (hi.hasMFDerivAt.comp t hg.hasMFDerivAt).hasFDerivAt.hasDerivAt
    exact hd
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  have hbound (t : ℝ) (ht : t ∈ Ico 0 L) :
      ‖v t‖ ≤ (N.scale * Real.sqrt (1 - N.epsilon))⁻¹ := by
    have ht' : t ∈ Icc 0 L := ⟨ht.1, ht.2.le⟩
    have h := N.axial_mvfderiv_bound (hcarrier ht')
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1)
    rw [hspeed t ht'] at h
    rw [Real.norm_eq_abs]
    simpa only [mul_one] using (le_inv_mul_iff₀ hfactor).mpr h
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t ht => (hv t ht).hasDerivWithinAt) hbound L ⟨hL, le_rfl⟩
  simpa only [Real.norm_eq_abs, sub_zero] using h

omit [T2Space M] in

theorem half_neck_time_gt_of_unit_speed {γ : ℝ → M} {L : ℝ}
    (hL : 0 ≤ L) (hε : N.epsilon ≤ 1 / 4)
    (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hcarrier : MapsTo γ (Icc 0 L) N.carrier)
    (hspeed : ∀ t ∈ Icc 0 L,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1)
    (haxis0 : |(N.coordinate_inverse (γ 0)).2| ≤ 1)
    (haxisL : |(N.coordinate_inverse (γ L)).2| = N.epsilon⁻¹ / 2) :
    N.scale / (100 * N.epsilon) < L := by
  have hr := N.scale_pos
  have he := N.epsilon_pos
  have hroot : 1 / 2 ≤ Real.sqrt (1 - N.epsilon) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - N.epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 - N.epsilon)]
  have hfactor : 0 < N.scale * Real.sqrt (1 - N.epsilon) := by positivity
  have hdisp := N.axial_displacement_le_of_unit_speed hL hγ hcarrier hspeed
  have hscaled : N.scale * Real.sqrt (1 - N.epsilon) *
      |(N.coordinate_inverse (γ L)).2 - (N.coordinate_inverse (γ 0)).2| ≤ L :=
    (le_inv_mul_iff₀ hfactor).mp hdisp
  have htriangle := abs_sub_abs_le_abs_sub
    (N.coordinate_inverse (γ L)).2 (N.coordinate_inverse (γ 0)).2
  rw [haxisL] at htriangle
  have hinv : N.epsilon⁻¹ * N.epsilon = 1 := inv_mul_cancel₀ he.ne'
  have hdiff : 1 / (4 * N.epsilon) ≤
      |(N.coordinate_inverse (γ L)).2 - (N.coordinate_inverse (γ 0)).2| := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * N.epsilon)).mpr
    have h := mul_le_mul_of_nonneg_right htriangle he.le
    have h0 := mul_le_mul_of_nonneg_right haxis0 he.le
    nlinarith
  have hlow : N.scale / (8 * N.epsilon) ≤ L := by
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left hroot hr.le) hdiff
      (by positivity) (by positivity : 0 ≤ N.scale * Real.sqrt (1 - N.epsilon))
    have heq : (N.scale * (1 / 2)) * (1 / (4 * N.epsilon)) =
        N.scale / (8 * N.epsilon) := by ring
    rw [heq] at hm
    exact hm.trans hscaled
  apply lt_of_lt_of_le _ hlow
  exact div_lt_div_of_pos_left hr (by positivity) (by linarith)

theorem exists_long_initial_segment_to_half_neck {γ : ℝ → M} {L : ℝ}
    (hL : 0 ≤ L) (hε : N.epsilon ≤ 1 / 4)
    (hγ : g.IsGeodesicOn γ (Icc 0 L))
    (hspeed : ∀ t ∈ Icc 0 L,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ t 1) = 1)
    (hstart : γ 0 ∈ N.carrier)
    (haxis0 : |(N.coordinate_inverse (γ 0)).2| ≤ 1)
    (hout : γ L ∉ N.coordinate_map ''
      (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2))) :
    ∃ t ∈ Ioc 0 L, N.scale / (100 * N.epsilon) < t ∧
      MapsTo γ (Icc 0 t) N.carrier ∧
      |(N.coordinate_inverse (γ t)).2| = N.epsilon⁻¹ / 2 ∧
      MapsTo γ (Ico 0 t) (N.region (-N.epsilon⁻¹ / 2) (N.epsilon⁻¹ / 2)) := by
  have hcont : ContinuousOn γ (Icc 0 L) :=
    fun t ht => (hγ.contMDiffAt ht).continuousAt.continuousWithinAt
  obtain ⟨t, ht, hcarrier, haxis, hbefore⟩ :=
    N.exists_initial_segment_to_half_neck hL hε hcont hstart haxis0 hout
  have hsub : Icc 0 t ⊆ Icc 0 L := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
  refine ⟨t, ht, ?_, hcarrier, haxis, hbefore⟩
  exact N.half_neck_time_gt_of_unit_speed ht.1.le hε
    (fun s hs => hγ s (hsub hs)) hcarrier (fun s hs => hspeed s (hsub hs)) haxis0 haxis

end PoincareConjecture.EpsilonNeck
