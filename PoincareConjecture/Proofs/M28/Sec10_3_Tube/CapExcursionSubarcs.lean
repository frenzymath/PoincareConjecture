import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapRecutBoundary
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

private theorem path_enters_open_frontier {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∉ U) (hb : γ b ∈ U) :
    ∃ t ∈ Icc a b, γ t ∈ frontier U := by
  have hconn : IsPreconnected (γ '' Icc a b) :=
    isPreconnected_Icc.image γ hγ
  by_contra hcross
  push Not at hcross
  have hsubset : γ '' Icc a b ⊆ U := by
    apply hconn.subset_of_closure_inter_subset hU
      ⟨γ b, ⟨b, right_mem_Icc.mpr hab, rfl⟩, hb⟩
    rintro x ⟨hxcl, t, ht, rfl⟩
    by_contra hxnot
    exact hcross t ht (hU.frontier_eq.symm ▸ And.intro hxcl hxnot)
  exact ha (hsubset ⟨a, left_mem_Icc.mpr hab, rfl⟩)

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem exists_incoming_neck_subarc (N : CapCertificate g) {q : ℝ}
    (hqlo : -N.epsilon⁻¹ < q) (hq : q < 0)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b))
    (ha : γ a ∈ N.end_neck.central_sphere) (hb : γ b ∈ N.closed_core) :
    ∃ v u : ℝ, a ≤ v ∧ v < u ∧ u ≤ b ∧
      γ v ∈ N.end_neck.central_sphere ∧
      γ u ∈ N.end_neck.coordinate_map '' (univ ×ˢ ({q} : Set ℝ)) ∧
      MapsTo γ (Icc v u)
        (N.end_neck.coordinate_map '' (univ ×ˢ Icc q 0)) := by
  let Wq : Set M := N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q
  let W0 : Set M := N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) 0
  have h0hi : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have h0lo : -N.epsilon⁻¹ < 0 := neg_neg_of_pos h0hi
  have hqhi : q < N.epsilon⁻¹ := hq.trans h0hi
  have hWq : IsOpen Wq := N.isOpen_recut hqlo hqhi
  have hW0 : IsOpen W0 := N.isOpen_recut h0lo h0hi
  have hfrontq : frontier Wq =
      N.end_neck.coordinate_map '' (univ ×ˢ ({q} : Set ℝ)) :=
    N.frontier_innerRecut hqlo hqhi
  have hfront0 : frontier W0 = N.end_neck.central_sphere := by
    rw [N.end_neck.central_sphere_eq]
    exact N.frontier_innerRecut h0lo h0hi
  have haN : γ a ∈ N.end_neck.carrier := N.end_neck.central_sphere_subset ha
  have ha0 : (N.end_neck.coordinate_inverse (γ a)).2 = 0 :=
    (N.end_neck.mem_central_sphere_iff_of_mem_carrier haN).mp ha
  have haWq : γ a ∉ Wq := by
    rintro (hcore | hregion)
    · rw [N.closed_core_eq_complement_end] at hcore
      exact hcore.2 haN
    · have hlt := hregion.2.2
      rw [ha0] at hlt
      exact (not_lt_of_ge hq.le) hlt
  obtain ⟨t₀, ht₀, hfront₀⟩ :=
    path_enters_open_frontier hWq hab hγ haWq (Or.inl hb)
  let Kq : Set ℝ := Icc a b ∩ γ ⁻¹' frontier Wq
  have hKq : IsCompact Kq := isCompact_Icc.of_isClosed_subset
    (hγ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_frontier) inter_subset_left
  obtain ⟨u, hu, huleast⟩ := hKq.exists_isLeast ⟨t₀, ht₀, hfront₀⟩
  have huq : γ u ∈ N.end_neck.coordinate_map '' (univ ×ˢ ({q} : Set ℝ)) :=
    hfrontq ▸ hu.2
  obtain ⟨z, hz, hzγ⟩ := huq
  have hzq : z.2 = q := hz.2
  have hzN : z.2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    rw [N.end_neck_epsilon, hzq]
    exact ⟨hqlo, hqhi⟩
  have huN : γ u ∈ N.end_neck.carrier :=
    hzγ ▸ N.end_neck.coordinate_map_mem_of_axial z hzN
  have huheight : (N.end_neck.coordinate_inverse (γ u)).2 = q := by
    rw [← hzγ, N.end_neck.coordinate_inverse_coordinate_map_of_axial z hzN]
    exact hzq
  have huW0 : γ u ∈ W0 := Or.inr ⟨huN, by rw [huheight]; exact ⟨hqlo, hq⟩⟩
  have huNotFront0 : γ u ∉ frontier W0 := by
    intro h
    exact (hW0.frontier_eq ▸ h).2 huW0
  let K0 : Set ℝ := Icc a u ∩ γ ⁻¹' frontier W0
  have hγau : ContinuousOn γ (Icc a u) :=
    hγ.mono (Icc_subset_Icc le_rfl hu.1.2)
  have hK0 : IsCompact K0 := isCompact_Icc.of_isClosed_subset
    (hγau.preimage_isClosed_of_isClosed isClosed_Icc isClosed_frontier) inter_subset_left
  obtain ⟨v, hv, hvgreatest⟩ := hK0.exists_isGreatest
    ⟨a, left_mem_Icc.mpr hu.1.1, hfront0.symm ▸ ha⟩
  have hvu : v < u := lt_of_le_of_ne hv.1.2 (by
    intro heq
    exact huNotFront0 (heq ▸ hv.2))
  refine ⟨v, u, hv.1.1, hvu, hu.1.2, hfront0 ▸ hv.2,
    ⟨z, hz, hzγ⟩, ?_⟩
  intro t ht
  have htab : t ∈ Icc a b := ⟨hv.1.1.trans ht.1, ht.2.trans hu.1.2⟩
  have htNotWq : γ t ∉ Wq := by
    intro htWq
    have htu : t < u := lt_of_le_of_ne ht.2 (by
      intro heq
      exact (hWq.frontier_eq ▸ hu.2).2 (heq ▸ htWq))
    obtain ⟨s, hs, hsfront⟩ := path_enters_open_frontier hWq htab.1
      (hγ.mono (Icc_subset_Icc le_rfl htab.2)) haWq htWq
    have hus : u ≤ s := huleast ⟨⟨hs.1, hs.2.trans htab.2⟩, hsfront⟩
    exact (not_lt_of_ge (hus.trans hs.2)) htu
  have htClosure : γ t ∈ closure W0 := by
    by_contra htout
    have hvt : v < t := lt_of_le_of_ne ht.1 (by
      intro heq
      exact htout (heq ▸ frontier_subset_closure hv.2))
    obtain ⟨s, hs, hsfront⟩ := path_enters_open_frontier hW0 ht.2
      (hγ.mono (Icc_subset_Icc htab.1 hu.1.2))
      (fun htW0 => htout (subset_closure htW0)) huW0
    have hsv : s ≤ v := hvgreatest ⟨⟨htab.1.trans hs.1, hs.2⟩, hsfront⟩
    exact (not_lt_of_ge hsv) (hvt.trans_le hs.1)
  have htcap : γ t ∈ N.carrier :=
    (N.open_precompact_recut h0lo h0hi).2.2 htClosure
  have htN : γ t ∈ N.end_neck.carrier := by
    by_contra htNotN
    apply htNotWq
    apply Or.inl
    rw [N.closed_core_eq_complement_end]
    exact ⟨htcap, htNotN⟩
  have htlo : -N.epsilon⁻¹ < (N.end_neck.coordinate_inverse (γ t)).2 := by
    simpa only [N.end_neck_epsilon] using
      (N.end_neck.coordinate_inverse_mem (γ t) htN).2.1
  have htq : q ≤ (N.end_neck.coordinate_inverse (γ t)).2 := by
    by_contra h
    exact htNotWq (Or.inr ⟨htN, htlo, lt_of_not_ge h⟩)
  have htzero : (N.end_neck.coordinate_inverse (γ t)).2 ≤ 0 := by
    rw [closure_eq_self_union_frontier] at htClosure
    rcases htClosure with htW0 | htfront
    · rcases htW0 with htcore | htregion
      · exact False.elim (htNotWq (Or.inl htcore))
      · exact htregion.2.2.le
    · exact ((N.end_neck.mem_central_sphere_iff_of_mem_carrier htN).mp (hfront0 ▸ htfront)).le
  exact ⟨N.end_neck.coordinate_inverse (γ t), ⟨mem_univ _, htq, htzero⟩,
    N.end_neck.coordinate_map_coordinate_inverse htN⟩

end PoincareConjecture.CapCertificate
