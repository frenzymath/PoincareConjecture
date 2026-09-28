import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.OpenRecut

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem frontier_innerRecut (N : CapCertificate g) {q : ℝ}
    (hq : -N.epsilon⁻¹ < q) (hq' : q < N.epsilon⁻¹) :
    frontier (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q) =
      N.end_neck.coordinate_map '' (univ ×ˢ ({q} : Set ℝ)) := by
  let W : Set M := N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q
  obtain ⟨hWopen, _, hWcap⟩ := N.open_precompact_recut hq hq'
  have hqN : q ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    rw [N.end_neck_epsilon]
    exact ⟨hq, hq'⟩
  ext x
  constructor
  · intro hx
    have hxcl : x ∈ closure W := frontier_subset_closure hx
    have hxnot : x ∉ W := (hWopen.frontier_eq ▸ hx).2
    have hxend : x ∈ N.end_neck.carrier := by
      by_contra hxend
      apply hxnot
      apply Or.inl
      rw [N.closed_core_eq_complement_end]
      exact ⟨hWcap hxcl, hxend⟩
    have hlow : -N.epsilon⁻¹ < (N.end_neck.coordinate_inverse x).2 := by
      simpa only [N.end_neck_epsilon] using
        (N.end_neck.coordinate_inverse_mem x hxend).2.1
    have hhigh : (N.end_neck.coordinate_inverse x).2 < N.epsilon⁻¹ := by
      simpa only [N.end_neck_epsilon] using
        (N.end_neck.coordinate_inverse_mem x hxend).2.2
    have heq : (N.end_neck.coordinate_inverse x).2 = q := by
      rcases lt_trichotomy (N.end_neck.coordinate_inverse x).2 q with hlt | heq | hgt
      · exact False.elim (hxnot (Or.inr ⟨hxend, hlow, hlt⟩))
      · exact heq
      · obtain ⟨y, hyouter, hyW⟩ := mem_closure_iff.mp hxcl
          (N.end_neck.region q N.epsilon⁻¹)
          (N.end_neck.region_open q N.epsilon⁻¹) ⟨hxend, hgt, hhigh⟩
        rcases hyW with hycore | hyinner
        · rw [N.closed_core_eq_complement_end] at hycore
          exact False.elim (hycore.2 hyouter.1)
        · exact False.elim ((not_lt_of_ge hyinner.2.2.le) hyouter.2.1)
    exact ⟨N.end_neck.coordinate_inverse x, ⟨mem_univ _, heq⟩,
      N.end_neck.coordinate_map_coordinate_inverse hxend⟩
  · rintro ⟨z, hz, rfl⟩
    have hzq : z.2 = q := hz.2
    have hzN : z.2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ :=
      hzq.symm ▸ hqN
    have hzcl : z ∈ closure (univ ×ˢ Ioo (-N.epsilon⁻¹) q) := by
      rw [closure_prod_eq, closure_univ, closure_Ioo hq.ne]
      exact ⟨mem_univ _, by rw [hzq]; exact ⟨hq.le, le_rfl⟩⟩
    have hcont : ContinuousAt N.end_neck.coordinate_map z :=
      N.end_neck.coordinate_map_smooth.continuousOn.continuousAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hzN⟩)
    have himage : N.end_neck.coordinate_map ''
        (univ ×ˢ Ioo (-N.epsilon⁻¹) q) ⊆ W := by
      rintro y ⟨w, hw, rfl⟩
      have hwN : w.2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
        rw [N.end_neck_epsilon]
        exact ⟨hw.2.1, hw.2.2.trans hq'⟩
      refine Or.inr ⟨N.end_neck.coordinate_map_mem_of_axial w hwN, ?_⟩
      rw [N.end_neck.coordinate_inverse_coordinate_map_of_axial w hwN]
      exact hw.2
    have hxcl : N.end_neck.coordinate_map z ∈ closure W :=
      closure_mono himage (hcont.continuousWithinAt.mem_closure_image hzcl)
    have hxnot : N.end_neck.coordinate_map z ∉ W := by
      rintro (hxcore | hxinner)
      · rw [N.closed_core_eq_complement_end] at hxcore
        exact hxcore.2 (N.end_neck.coordinate_map_mem_of_axial z hzN)
      · have hlt := hxinner.2.2
        rw [N.end_neck.coordinate_inverse_coordinate_map_of_axial z hzN, hzq] at hlt
        exact (lt_irrefl q) hlt
    exact hWopen.frontier_eq.symm ▸ And.intro hxcl hxnot

theorem path_from_core_crosses_recut_sphere (N : CapCertificate g) {q : ℝ}
    (hq : -N.epsilon⁻¹ < q) (hq' : q < N.epsilon⁻¹)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∈ N.closed_core)
    (hb : γ b ∉ N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q) :
    ∃ t ∈ Icc a b,
      γ t ∈ N.end_neck.coordinate_map '' (univ ×ˢ ({q} : Set ℝ)) := by
  let W : Set M := N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) q
  have hW : IsOpen W := N.isOpen_recut hq hq'
  have hconn : IsPreconnected (γ '' Icc a b) :=
    isPreconnected_Icc.image γ hγ
  by_contra hcross
  push Not at hcross
  have hsubset : γ '' Icc a b ⊆ W := by
    apply hconn.subset_of_closure_inter_subset hW
      ⟨γ a, ⟨a, left_mem_Icc.mpr hab, rfl⟩, Or.inl ha⟩
    rintro x ⟨hxcl, t, ht, rfl⟩
    by_contra hxnot
    have hfront : γ t ∈ frontier W := hW.frontier_eq.symm ▸ And.intro hxcl hxnot
    have hsphere : γ t ∈ N.end_neck.coordinate_map ''
        (univ ×ˢ ({q} : Set ℝ)) := N.frontier_innerRecut hq hq' ▸ hfront
    exact hcross t ht hsphere
  exact hb (hsubset ⟨b, right_mem_Icc.mpr hab, rfl⟩)

end PoincareConjecture.CapCertificate
