import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] {g : RiemannianMetric 3 M}



theorem exists_first_neck_collar_subarc (N : EpsilonNeck g)
    {r : ℝ} (hr : 0 < r) (hrA : r < N.epsilon⁻¹)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∈ N.central_sphere)
    (hb : γ b ∉ N.region (-r) r) :
    ∃ c : ℝ, a < c ∧ c ≤ b ∧ MapsTo γ (Icc a c) N.carrier ∧
      |(N.coordinate_inverse (γ c)).2 - (N.coordinate_inverse (γ a)).2| =
        r := by
  let W : Set M := N.region (-r) r
  let S : Set M := N.coordinate_map '' (univ ×ˢ Icc (-r) r)
  have hlo : -N.epsilon⁻¹ < -r := neg_lt_neg hrA
  have hhi : r < N.epsilon⁻¹ := hrA
  have hW : IsOpen W := N.region_open _ _
  have hS : IsCompact S := N.isCompact_coordinate_slab_intrinsic hlo hhi
  have hSN : S ⊆ N.carrier := N.coordinate_slab_subset_carrier_m28 hlo hhi
  have hWS : W ⊆ S := by
    intro x hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hx.1⟩
  have hclosure : closure W ⊆ S := closure_minimal hWS hS.isClosed
  have haW : γ a ∈ W :=
    N.central_sphere_subset_region (neg_lt_zero.mpr hr) hr ha
  let K : Set ℝ := Icc a b ∩ γ ⁻¹' Wᶜ
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hγ.preimage_isClosed_of_isClosed isClosed_Icc hW.isClosed_compl)
    inter_subset_left
  obtain ⟨c, hc, hleast⟩ := hK.exists_isLeast
    ⟨b, right_mem_Icc.mpr hab, hb⟩
  have hac : a < c := lt_of_le_of_ne hc.1.1 (by
    intro heq
    exact hc.2 (heq ▸ haW))
  have hprefix : MapsTo γ (Ico a c) W := by
    intro t ht
    by_contra htW
    have hct : c ≤ t := hleast ⟨⟨ht.1, ht.2.le.trans hc.1.2⟩, htW⟩
    exact (not_lt_of_ge hct) ht.2
  have hγac : ContinuousOn γ (closure (Ico a c)) := by
    rw [closure_Ico hac.ne]
    exact hγ.mono (Icc_subset_Icc le_rfl hc.1.2)
  have hprefixClosed : MapsTo γ (Icc a c) (closure W) := by
    simpa only [closure_Ico hac.ne] using hprefix.closure_of_continuousOn hγac
  have hprefixN : MapsTo γ (Icc a c) N.carrier :=
    fun t ht => hSN (hclosure (hprefixClosed ht))
  have hcS : γ c ∈ S := hclosure (hprefixClosed (right_mem_Icc.mpr hac.le))
  have hcN : γ c ∈ N.carrier := hSN hcS
  have ha0 : (N.coordinate_inverse (γ a)).2 = 0 :=
    (N.mem_central_sphere_iff_of_mem_carrier (N.central_sphere_subset ha)).mp ha
  have hheight : (N.coordinate_inverse (γ c)).2 ∈
      Icc (-r) r := by
    obtain ⟨z, hz, hzγ⟩ := hcS
    rw [← hzγ, N.coordinate_inverse_coordinate_map_of_axial z
      ⟨hlo.trans_le hz.2.1, hz.2.2.trans_lt hhi⟩]
    exact hz.2
  refine ⟨c, hac, hc.1.2, hprefixN, ?_⟩
  rw [ha0, sub_zero]
  apply le_antisymm (abs_le.mpr hheight)
  by_contra hsmall
  have hinside := abs_lt.mp (lt_of_not_ge hsmall)
  exact hc.2 ⟨hcN, hinside⟩



theorem exists_first_half_neck_subarc (N : EpsilonNeck g)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∈ N.central_sphere)
    (hb : γ b ∉ N.region (-(N.epsilon⁻¹ / 2)) (N.epsilon⁻¹ / 2)) :
    ∃ c : ℝ, a < c ∧ c ≤ b ∧ MapsTo γ (Icc a c) N.carrier ∧
      |(N.coordinate_inverse (γ c)).2 - (N.coordinate_inverse (γ a)).2| =
        N.epsilon⁻¹ / 2 := by
  have hA : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  exact N.exists_first_neck_collar_subarc (by positivity) (by linarith) hab hγ ha hb

end PoincareConjecture.EpsilonNeck
