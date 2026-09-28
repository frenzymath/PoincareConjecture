import PoincareConjecture.Proofs.M47.BlowupControlsCapOutwardTopology
import PoincareConjecture.Proofs.M45.Ch12_Standard.CapDefiningFunction

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : CapCertificate g)

theorem cap_outward_tail_relative_frontier {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹) :
    N.carrier ∩ frontier (N.end_neck.region b N.epsilon⁻¹) =
      N.end_neck.coordinate_map '' (univ ×ˢ ({b} : Set ℝ)) := by
  ext x
  constructor
  · rintro ⟨hx, hxfront⟩
    have hnot : x ∉ N.end_neck.region b N.epsilon⁻¹ := by
      simpa only [(N.end_neck.region_isOpen _ _).interior_eq] using hxfront.2
    have hxK : x ∈ closure (N.recutCarrier b) :=
      (cap_outward_core_eq_complement N hb hb').symm ▸ ⟨hx, hnot⟩
    rw [closure_eq_self_union_frontier,
      N.recutCarrier_frontier_eq_axial_sphere hb hb'] at hxK
    rcases hxK with hxV | hxS
    · obtain ⟨y, hyV, hyTail⟩ := mem_closure_iff.mp hxfront.1 _
        (N.recutCarrier_isOpen hb hb') hxV
      have hyK : y ∈ closure (N.recutCarrier b) := subset_closure hyV
      rw [cap_outward_core_eq_complement N hb hb'] at hyK
      exact (hyK.2 hyTail).elim
    · exact hxS
  · intro hxS
    have hxcl := cap_outward_sphere_subset_tail_closure N hb hb' hxS
    obtain ⟨z, hz, rfl⟩ := hxS
    have hzB : z.2 = b := hz.2
    have hzN : z.2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
      simpa only [hzB, N.end_neck_epsilon, mem_Ioo] using And.intro hb hb'
    refine ⟨N.end_neck_subset (N.end_neck.coordinate_map_mem_of_axial_mem hzN), hxcl, ?_⟩
    rw [(N.end_neck.region_isOpen _ _).interior_eq]
    intro hxTail
    have hlt := hxTail.2.1
    rw [N.end_neck.coordinate_inverse_coordinate_map_of_axial_mem hzN, hzB] at hlt
    exact (lt_irrefl b) hlt

theorem cap_outward_core_iff_axial_le {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹)
    {x : M} (hx : x ∈ N.end_neck.carrier) :
    x ∈ closure (N.recutCarrier b) ↔ (N.end_neck.coordinate_inverse x).2 ≤ b := by
  rw [cap_outward_core_eq_complement N hb hb']
  have hz := (N.end_neck.coordinate_inverse_mem x hx).2
  rw [N.end_neck_epsilon] at hz
  constructor
  · intro h
    exact le_of_not_gt (fun hlt => h.2 ⟨hx, hlt, hz.2⟩)
  · intro hle
    exact ⟨N.end_neck_subset hx, fun htail => (not_lt_of_ge hle) htail.2.1⟩

theorem cap_outward_boundary_local_defining_function {b : ℝ}
    (hb : -N.epsilon⁻¹ < b) (hb' : b < N.epsilon⁻¹)
    {x : M} (hx : x ∈ frontier (closure (N.recutCarrier b))) :
    ∃ U : Set M, ∃ f : M → ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ N.carrier ∧
      (∀ y ∈ U, y ∈ closure (N.recutCarrier b) ↔ f y ≤ 0) ∧ f x = 0 ∧
      ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ f U ∧
      ∃ d : TangentSpace (𝓡 3) x, d ≠ 0 ∧ mvfderiv (𝓡 3) f x d ≠ 0 := by
  rw [cap_outward_core_frontier N hb hb'] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hzB : z.2 = b := hz.2
  have hzN : z.2 ∈ Ioo (-N.end_neck.epsilon⁻¹) N.end_neck.epsilon⁻¹ := by
    simpa only [hzB, N.end_neck_epsilon, mem_Ioo] using And.intro hb hb'
  have hxN := N.end_neck.coordinate_map_mem_of_axial_mem hzN
  obtain ⟨d, hd⟩ := M45.neck_axial_derivative N.end_neck hxN
  have hdne : d ≠ 0 := by
    intro h
    simp only [h, map_zero, zero_ne_one] at hd
  let f : M → ℝ := fun y => (N.end_neck.coordinate_inverse y).2 - b
  refine ⟨N.end_neck.carrier, f, N.end_neck.carrier_open, hxN,
    N.end_neck_subset, ?_, ?_, ?_, d, hdne, ?_⟩
  · intro y hy
    exact (cap_outward_core_iff_axial_le N hb hb' hy).trans sub_nonpos.symm
  · dsimp [f]
    rw [N.end_neck.coordinate_inverse_coordinate_map_of_axial_mem hzN, hzB, sub_self]
  · intro y hy
    exact (N.end_neck.coordinate_inverse_smooth y hy).snd.sub contMDiffWithinAt_const
  · have hdiff := ((N.end_neck.coordinate_inverse_smooth _ hxN).snd.contMDiffAt
        (N.end_neck.carrier_open.mem_nhds hxN)).mdifferentiableAt (by simp)
    change (mvfderiv (𝓡 3)
      ((fun y => (N.end_neck.coordinate_inverse y).2) - fun _ => b) _ ) d ≠ 0
    rw [mvfderiv_sub hdiff mdifferentiableAt_const, mvfderiv_const, sub_zero, hd]
    exact one_ne_zero

end PoincareConjecture.M47
