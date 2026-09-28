import PoincareConjecture.Proofs.M25.AppA_21_Local.CapCuts

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

theorem CapCertificate.end_neck_isSeparating
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : CapCertificate g) : C.end_neck.IsSeparating := by
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ inferInstance)
  let N := C.end_neck
  let L := C.epsilon⁻¹
  let K := C.carrier \ N.region 0 L
  let B := connectedComponent N.center \ N.central_sphere
  have hN : N.epsilon = C.epsilon := C.end_neck_epsilon
  have hL : 0 < L := inv_pos.mpr C.epsilon_pos
  have h0 : (0 : ℝ) ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ :=
    ⟨neg_lt_zero.mpr hL, hL⟩
  have hK : IsClosed K := (C.isCompact_end_neck_lower_cut h0).isClosed
  have hfront : frontier K = N.central_sphere := by
    rw [N.central_sphere_eq]
    exact (C.end_neck_lower_cut_topology h0).2.2.2.2.2.1
  refine ⟨N.m25_component_diff_central_sphere_nonempty, ?_⟩
  intro hcon
  have hcover : B ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · apply Or.inl
      by_contra hxi
      have hxf : x ∈ frontier K := by
        rw [hK.frontier_eq]
        exact ⟨hxK, hxi⟩
      exact hx.2 (hfront ▸ hxf)
    · exact Or.inr hxK
  have hdisj : Disjoint (interior K) Kᶜ := by
    apply disjoint_left.mpr
    intro x hx hxK
    exact hxK (interior_subset hx)
  have hsplit := hcon.isPreconnected.subset_or_subset
    isOpen_interior hK.isOpen_compl hdisj hcover
  let q := (N.coordinate_inverse N.center).1
  have hpoint (s : ℝ) (hs : s ∈ Ioo (-L) L) (hs0 : s ≠ 0) :
      N.coordinate_map (q, s) ∈ B := by
    have hsN : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      simpa only [hN] using hs
    refine ⟨N.m25_carrier_subset_connectedComponent
      (N.coordinate_map_mem ⟨mem_univ _, hsN⟩), ?_⟩
    intro hx
    have hzero := ((N.mem_central_sphere_iff _).mp hx).2
    rw [N.coordinate_inverse_map (q, s) hsN] at hzero
    exact hs0 hzero
  have hm : -L / 2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [hN]
    change -L / 2 ∈ Ioo (-L) L
    constructor <;> linarith
  have hp : L / 2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [hN]
    change L / 2 ∈ Ioo (-L) L
    constructor <;> linarith
  have hmB : N.coordinate_map (q, -L / 2) ∈ B :=
    hpoint _ (by constructor <;> linarith) (by linarith)
  have hpB : N.coordinate_map (q, L / 2) ∈ B :=
    hpoint _ (by constructor <;> linarith) (by linarith)
  have hmK : N.coordinate_map (q, -L / 2) ∈ K := by
    refine ⟨C.end_neck_subset (N.coordinate_map_mem ⟨mem_univ _, hm⟩), ?_⟩
    intro hx
    have hsign := hx.2.1
    rw [N.coordinate_inverse_map (q, -L / 2) hm] at hsign
    dsimp at hsign
    linarith
  have hpregion : N.coordinate_map (q, L / 2) ∈ N.region 0 L := by
    refine ⟨N.coordinate_map_mem ⟨mem_univ _, hp⟩, ?_, ?_⟩ <;>
      rw [N.coordinate_inverse_map (q, L / 2) hp] <;> dsimp <;> linarith
  rcases hsplit with hin | hout
  · exact (interior_subset (hin hpB)).2 hpregion
  · exact hout hmB hmK

end PoincareConjecture
