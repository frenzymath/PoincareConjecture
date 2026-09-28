import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Overlap.Cylinder.FiberConnected
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.AxialSign












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck




theorem exists_axial_overlap_fiber_positive_deriv_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N Q : EpsilonNeck g), N.epsilon ≤ ε₀ → Q.epsilon ≤ ε₀ →
          N.carrier ∩ Q.carrier ⊆
            N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
              Q.region (-Q.epsilon⁻¹) (Q.epsilon⁻¹ / 2) →
          ∀ (q : UnitTwoSphere) (b : ℝ),
            b ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ → Q.coordinate_map (q, b) ∈ N.carrier →
            (0.9 : ℝ) ≤ deriv (fun t => (N.coordinate_inverse (Q.coordinate_map (q, t))).2) b ∧
              deriv (fun t => (N.coordinate_inverse (Q.coordinate_map (q, t))).2) b ≤ (1.1 : ℝ) := by
  obtain ⟨ε₁, hε₁, hsmall, hconnected⟩ := exists_axial_overlap_fiber_preconnected_threshold.{u}
  obtain ⟨ε₂, hε₂, -, hderiv⟩ := exists_transition_axis_deriv_bounds.{u}
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N Q hN hQ hoverlap q b hbdom hbN
  let γ : ℝ → M := fun t => Q.coordinate_map (q, t)
  let f : ℝ → ℝ := fun t => (N.coordinate_inverse (γ t)).2
  let S : Set ℝ := {t | t ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ ∧ γ t ∈ N.carrier}
  have hbS : b ∈ S := ⟨hbdom, hbN⟩
  have hS : IsPreconnected S := hconnected N Q
    (hN.trans (min_le_left _ _)) (hQ.trans (min_le_left _ _)) hoverlap q
  have hsmooth (t : ℝ) (ht : t ∈ S) : ContDiffAt ℝ ∞ f t :=
    N.transition_axis_contDiffAt Q q ht.1 ht.2
  have hcont' : ContinuousOn (deriv f) S := by
    intro t ht
    exact ((hsmooth t ht).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ S) : (0.9 : ℝ) ≤ |deriv f t| ∧ |deriv f t| ≤ (1.1 : ℝ) :=
    hderiv N Q (hN.trans (min_le_right _ _)) (hQ.trans (min_le_right _ _)) q ht.1 ht.2
  have hne (t : ℝ) (ht : t ∈ S) : deriv f t ≠ 0 := by
    intro heq
    have h := (hd t ht).1
    rw [heq, abs_zero] at h
    norm_num at h
  rcases hS.mapsTo_Ioi_or_Iio hcont' hne with hpos | hneg
  · have hp : 0 < deriv f b := hpos hbS
    simpa only [abs_of_pos hp] using hd b hbS
  have hanti : StrictAntiOn f S := strictAntiOn_of_deriv_neg hS.ordConnected.convex
    (fun t ht => (hsmooth t ht).continuousAt.continuousWithinAt)
    (fun t ht => hneg (interior_subset ht))
  have hRN : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hRQ : 0 < Q.epsilon⁻¹ := inv_pos.mpr Q.epsilon_pos
  have hγ : ContinuousOn γ (Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹) := by
    apply Q.coordinate_map_smooth.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro t ht
    exact ⟨mem_univ _, ht⟩
  have hSn : S ∈ 𝓝 b := Filter.inter_mem (isOpen_Ioo.mem_nhds hbdom)
    ((hγ.continuousAt (isOpen_Ioo.mem_nhds hbdom)).preimage_mem_nhds
      (N.carrier_open.mem_nhds hbN))
  obtain ⟨l, r, hbr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hSn
  obtain ⟨c, hlc, hcb⟩ := exists_between hbr.1
  have hcS : c ∈ S := hsub ⟨hlc, hcb.trans hbr.2⟩
  have hdrop : f b < f c := hanti hcS hbS hcb
  have hbounds (t : ℝ) (ht : t ∈ S) :
      -N.epsilon⁻¹ / 2 < f t ∧ t < Q.epsilon⁻¹ / 2 := by
    have h := hoverlap ⟨ht.2, Q.coordinate_map_mem ⟨mem_univ _, ht.1⟩⟩
    refine ⟨h.1.2.1, ?_⟩
    have hheight := h.2.2.2
    change (Q.coordinate_inverse (Q.coordinate_map (q, t))).2 < Q.epsilon⁻¹ / 2 at hheight
    rwa [Q.coordinate_inverse_coordinate_map ⟨mem_univ _, ht.1⟩] at hheight
  have hbupper := (hbounds b hbS).2
  have hdom : Icc c (Q.epsilon⁻¹ / 2) ⊆ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ :=
    fun t ht => ⟨hcS.1.1.trans_le ht.1, by linarith [ht.2]⟩
  have hlo : -N.epsilon⁻¹ < -N.epsilon⁻¹ / 2 := by linarith
  have hhi : f b < N.epsilon⁻¹ := (N.coordinate_inverse_mem _ hbN).2.2
  let K := N.coordinate_map '' (univ ×ˢ Icc (-N.epsilon⁻¹ / 2) (f b))
  have hK : IsCompact K := N.isCompact_coordinate_slab hlo hhi
  have hKsub : K ⊆ N.carrier := fun x hx =>
    ((N.mem_coordinate_slab_iff hlo hhi).mp hx).1
  let A := Icc c (Q.epsilon⁻¹ / 2) ∩ γ ⁻¹' K
  have hAclosed : IsClosed A :=
    (hγ.mono hdom).preimage_isClosed_of_isClosed isClosed_Icc hK.isClosed
  have hA : IsCompact A := isCompact_Icc.of_isClosed_subset hAclosed inter_subset_left
  have hbA : b ∈ A := by
    refine ⟨⟨hcb.le, hbupper.le⟩, ?_⟩
    exact (N.mem_coordinate_slab_iff hlo hhi).mpr ⟨hbN, (hbounds b hbS).1.le, le_rfl⟩
  have hfA : ContinuousOn f A := fun t ht =>
    (hsmooth t ⟨hdom ht.1, hKsub ht.2⟩).continuousAt.continuousWithinAt
  obtain ⟨x, hxA, hmin⟩ := hA.exists_isMinOn ⟨b, hbA⟩ hfA
  have hxS : x ∈ S := ⟨hdom hxA.1, hKsub hxA.2⟩
  have hcx : c < x := by
    by_contra h
    have heq : x = c := le_antisymm (le_of_not_gt h) hxA.1.1
    have hminb := hmin hbA
    rw [heq] at hminb
    exact not_lt_of_ge hminb hdrop
  have hxd : x < Q.epsilon⁻¹ / 2 := (hbounds x hxS).2
  have hγx : ContinuousAt γ x := hγ.continuousAt (isOpen_Ioo.mem_nhds hxS.1)
  have hlocal : IsLocalMin f x := by
    change ∀ᶠ t in 𝓝 x, f x ≤ f t
    filter_upwards [Ioo_mem_nhds hcx hxd,
      hγx.preimage_mem_nhds (N.carrier_open.mem_nhds hxS.2)] with t ht htN
    by_cases htb : f t ≤ f b
    · apply hmin
      refine ⟨Ioo_subset_Icc_self ht, ?_⟩
      exact (N.mem_coordinate_slab_iff hlo hhi).mpr
        ⟨htN, (hbounds t ⟨hdom (Ioo_subset_Icc_self ht), htN⟩).1.le, htb⟩
    · exact (hmin hbA).trans (le_of_not_ge htb)
  exact False.elim (hne x hxS hlocal.deriv_eq_zero)

end PoincareConjecture.EpsilonNeck
