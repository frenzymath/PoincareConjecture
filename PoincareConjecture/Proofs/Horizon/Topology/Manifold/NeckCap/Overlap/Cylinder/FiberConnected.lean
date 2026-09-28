import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.AxialMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Segment
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_axial_overlap_fiber_preconnected_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N Q : EpsilonNeck g), N.epsilon ≤ ε₀ → Q.epsilon ≤ ε₀ →
          N.carrier ∩ Q.carrier ⊆
            N.region (-N.epsilon⁻¹ / 2) N.epsilon⁻¹ ∩
              Q.region (-Q.epsilon⁻¹) (Q.epsilon⁻¹ / 2) →
          ∀ q : UnitTwoSphere,
            IsPreconnected {t : ℝ | t ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ ∧
              Q.coordinate_map (q, t) ∈ N.carrier} := by
  obtain ⟨ε₀, hε₀, hsmall, hderiv⟩ := exists_transition_axis_deriv_bounds.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N Q hN hQ hoverlap q
  let γ : ℝ → M := fun t => Q.coordinate_map (q, t)
  let f : ℝ → ℝ := fun t => (N.coordinate_inverse (γ t)).2
  have hRN : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hRQ : 0 < Q.epsilon⁻¹ := inv_pos.mpr Q.epsilon_pos
  have hγ : ContinuousOn γ (Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹) := by
    apply Q.coordinate_map_smooth.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro t ht
    exact ⟨mem_univ _, ht⟩
  have hbounds (t : ℝ) (ht : t ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹)
      (htN : γ t ∈ N.carrier) :
      -N.epsilon⁻¹ / 2 < f t ∧ t < Q.epsilon⁻¹ / 2 := by
    have h := hoverlap ⟨htN, Q.coordinate_map_mem ⟨mem_univ _, ht⟩⟩
    refine ⟨h.1.2.1, ?_⟩
    have hheight := h.2.2.2
    change (Q.coordinate_inverse (Q.coordinate_map (q, t))).2 < Q.epsilon⁻¹ / 2 at hheight
    rwa [Q.coordinate_inverse_coordinate_map ⟨mem_univ _, ht⟩] at hheight
  apply Set.OrdConnected.isPreconnected
  constructor
  intro a ha b hb c hc
  have hcdom : c ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ :=
    ⟨ha.1.1.trans_le hc.1, hc.2.trans_lt hb.1.2⟩
  refine ⟨hcdom, ?_⟩
  by_contra hcN
  have hbN : γ b ∈ N.carrier := hb.2
  have hcb : c < b := lt_of_le_of_ne hc.2 (by
    intro heq
    exact hcN (heq ▸ hbN))
  have hbupper := (hbounds b hb.1 hbN).2
  have hd : Q.epsilon⁻¹ / 2 ∈ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ := by
    constructor <;> linarith
  have hdN : γ (Q.epsilon⁻¹ / 2) ∉ N.carrier := by
    intro h
    exact lt_irrefl _ (hbounds _ hd h).2
  have hdom : Icc c (Q.epsilon⁻¹ / 2) ⊆ Ioo (-Q.epsilon⁻¹) Q.epsilon⁻¹ :=
    fun t ht => ⟨hcdom.1.trans_le ht.1, ht.2.trans_lt hd.2⟩
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
    exact (N.mem_coordinate_slab_iff hlo hhi).mpr
      ⟨hbN, (hbounds b hb.1 hbN).1.le, le_rfl⟩
  have hfA : ContinuousOn f A := by
    intro t ht
    exact (N.transition_axis_contDiffAt Q q (hdom ht.1)
      (hKsub ht.2)).continuousAt.continuousWithinAt
  obtain ⟨x, hxA, hmin⟩ := hA.exists_isMinOn ⟨b, hbA⟩ hfA
  have hxN : γ x ∈ N.carrier := hKsub hxA.2
  have hxdom := hdom hxA.1
  have hcx : c < x := by
    by_contra h
    have heq : x = c := le_antisymm (le_of_not_gt h) hxA.1.1
    exact hcN (heq ▸ hxN)
  have hxd : x < Q.epsilon⁻¹ / 2 := by
    by_contra h
    have heq : x = Q.epsilon⁻¹ / 2 := le_antisymm hxA.1.2 (le_of_not_gt h)
    exact hdN (heq ▸ hxN)
  have hγx : ContinuousAt γ x := hγ.continuousAt (isOpen_Ioo.mem_nhds hxdom)
  have hlocal : IsLocalMin f x := by
    change ∀ᶠ t in 𝓝 x, f x ≤ f t
    filter_upwards [Ioo_mem_nhds hcx hxd,
      hγx.preimage_mem_nhds (N.carrier_open.mem_nhds hxN)] with t ht htN
    by_cases htb : f t ≤ f b
    · apply hmin
      refine ⟨Ioo_subset_Icc_self ht, ?_⟩
      exact (N.mem_coordinate_slab_iff hlo hhi).mpr
        ⟨htN, (hbounds t (hdom (Ioo_subset_Icc_self ht)) htN).1.le, htb⟩
    · exact (hmin hbA).trans (le_of_not_ge htb)
  have hnonzero := (hderiv N Q hN hQ q hxdom hxN).1
  change (0.9 : ℝ) ≤ |deriv f x| at hnonzero
  rw [hlocal.deriv_eq_zero, abs_zero] at hnonzero
  norm_num at hnonzero

end PoincareConjecture.EpsilonNeck
