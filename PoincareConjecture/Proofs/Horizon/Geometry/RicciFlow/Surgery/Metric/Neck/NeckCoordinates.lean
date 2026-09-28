import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Local








set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.MetricSurgery

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem neck_coordinate_mem (N : EpsilonNeck g) (z : StandardCylinderSpace)
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_map z ∈ N.carrier := by
  let w : NeckDomain N.epsilon := (z.1, ⟨z.2, hz.2⟩)
  rw [← N.coordinate_map_eq w]
  exact (N.coordinate w).property

theorem neck_inverse_coordinate (N : EpsilonNeck g) (z : StandardCylinderSpace)
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    N.coordinate_inverse (N.coordinate_map z) = z := by
  let w : NeckDomain N.epsilon := (z.1, ⟨z.2, hz.2⟩)
  rw [← N.coordinate_map_eq w]
  exact N.coordinate_inverse_left w

theorem neck_coordinate_inverse (N : EpsilonNeck g) {x : M} (hx : x ∈ N.carrier) :
    N.coordinate_map (N.coordinate_inverse x) = x := by
  have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
  rw [N.coordinate_map_eq] at h
  exact h

theorem neck_coordinate_contMDiffAt (N : EpsilonNeck g)
    {z : StandardCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate_map z :=
  (N.coordinate_map_smooth z hz).contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)

theorem neck_inverse_contMDiffAt (N : EpsilonNeck g) {x : M} (hx : x ∈ N.carrier) :
    ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ N.coordinate_inverse x :=
  (N.coordinate_inverse_smooth x hx).contMDiffAt (N.carrier_open.mem_nhds hx)

theorem neck_region_subset (N : EpsilonNeck g) (a b : ℝ) :
    N.region a b ⊆ N.carrier := fun _ hx => hx.1

theorem neck_region_isOpen (N : EpsilonNeck g) (a b : ℝ) :
    IsOpen (N.region a b) := by
  change IsOpen (N.carrier ∩ (fun x => (N.coordinate_inverse x).2) ⁻¹' Set.Ioo a b)
  exact N.coordinate_inverse_smooth.continuousOn.snd.isOpen_inter_preimage
    N.carrier_open isOpen_Ioo

theorem neck_central_iff (N : EpsilonNeck g) {x : M} :
    x ∈ N.central_sphere ↔ x ∈ N.carrier ∧ (N.coordinate_inverse x).2 = 0 := by
  constructor
  · intro hx
    have hmem := N.central_sphere_subset hx
    rw [N.central_sphere_eq] at hx
    rcases hx with ⟨⟨theta, s⟩, hs, rfl⟩
    have hs0 : s = 0 := hs.2
    subst s
    refine ⟨hmem, ?_⟩
    rw [neck_inverse_coordinate N _ ⟨Set.mem_univ _, by
      constructor <;> linarith [inv_pos.mpr N.epsilon_pos]⟩]
  · rintro ⟨hx, hs⟩
    rw [N.central_sphere_eq]
    exact ⟨N.coordinate_inverse x, ⟨Set.mem_univ _, hs⟩, neck_coordinate_inverse N hx⟩

theorem neck_retained_iff (N : EpsilonNeck g) {x : M} :
    x ∈ N.region (-N.epsilon⁻¹) 0 ∪ N.central_sphere ↔
      x ∈ N.carrier ∧ (N.coordinate_inverse x).2 ≤ 0 := by
  rw [Set.mem_union, neck_central_iff]
  constructor
  · rintro (hx | hx)
    · exact ⟨hx.1, hx.2.2.le⟩
    · exact ⟨hx.1, hx.2.le⟩
  · rintro ⟨hx, hs⟩
    rcases hs.lt_or_eq with hs | hs
    · exact Or.inl ⟨hx, (N.coordinate_inverse_mem x hx).2.1, hs⟩
    · exact Or.inr ⟨hx, hs⟩

end PoincareConjecture.MetricSurgery
