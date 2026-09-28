import PoincareConjecture.Proofs.M36.NeckCoordinates
import PoincareConjecture.Proofs.M44.Mathlib.PartialHomeomorphCompact










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}



noncomputable def neckPartialDiffeomorph (N : EpsilonNeck g) :
    PartialDiffeomorph IC (𝓡 3) RoundCylinderSpace M ∞ where
  toFun := N.coordinate_map
  invFun := N.coordinate_inverse
  source := univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
  target := N.carrier
  map_source' := fun z hz => neck_coordinate_mem N z hz
  map_target' := N.coordinate_inverse_mem
  left_inv' := fun z hz => neck_inverse_coordinate N z hz
  right_inv' := fun _ hx => neck_coordinate_inverse N hx
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := N.carrier_open
  contMDiffOn_toFun := N.coordinate_map_smooth
  contMDiffOn_invFun := N.coordinate_inverse_smooth



theorem neck_region_eq_image (N : EpsilonNeck g) {b : ℝ} (hb : b < N.epsilon⁻¹) :
    N.region (-b) b = N.coordinate_map '' (univ ×ˢ Ioo (-b) b) := by
  ext x
  constructor
  · intro hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2⟩, neck_coordinate_inverse N hx.1⟩
  · rintro ⟨z, hz, rfl⟩
    have hsource : z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨mem_univ _, by linarith [hz.2.1], hz.2.2.trans hb⟩
    refine ⟨neck_coordinate_mem N z hsource, ?_⟩
    rw [neck_inverse_coordinate N z hsource]
    exact hz.2




theorem neck_closure_region [T2Space M] (N : EpsilonNeck g)
    {b : ℝ} (hb0 : 0 < b) (hb : b < N.epsilon⁻¹) :
    closure (N.region (-b) b) = N.coordinate_map '' (univ ×ˢ Icc (-b) b) := by
  have hcl : closure (univ ×ˢ Ioo (-b) b : Set RoundCylinderSpace) =
      univ ×ˢ Icc (-b) b := by
    rw [closure_prod_eq, closure_univ, closure_Ioo (neg_lt_self hb0).ne]
  have hcompact : IsCompact (closure (univ ×ˢ Ioo (-b) b : Set RoundCylinderSpace)) := by
    rw [hcl]
    exact isCompact_univ.prod isCompact_Icc
  have hsource : closure (univ ×ˢ Ioo (-b) b : Set RoundCylinderSpace) ⊆
      (neckPartialDiffeomorph N).source := by
    rw [hcl]
    intro z hz
    exact ⟨mem_univ _, by linarith [hz.2.1], hz.2.2.trans_lt hb⟩
  have h := (neckPartialDiffeomorph N).toOpenPartialHomeomorph.image_closure_of_compact_buffer
    hcompact hsource
  rw [hcl] at h
  rw [neck_region_eq_image N hb]
  exact h.symm



theorem neck_closure_region_subset [T2Space M] (N : EpsilonNeck g)
    {b : ℝ} (hb0 : 0 < b) (hb : b < N.epsilon⁻¹) :
    closure (N.region (-b) b) ⊆ N.carrier := by
  rw [neck_closure_region N hb0 hb]
  rintro _ ⟨z, hz, rfl⟩
  exact neck_coordinate_mem N z ⟨mem_univ _, by linarith [hz.2.1], hz.2.2.trans_lt hb⟩




theorem neck_frontier_region_height [T2Space M] (N : EpsilonNeck g)
    {b : ℝ} (hb0 : 0 < b) (hb : b < N.epsilon⁻¹)
    {x : M} (hx : x ∈ frontier (N.region (-b) b)) :
    x ∈ N.carrier ∧ |(N.coordinate_inverse x).2| = b := by
  have hcl := frontier_subset_closure hx
  have hxN := neck_closure_region_subset N hb0 hb hcl
  have hnot : x ∉ N.region (-b) b := by
    simpa only [(neck_region_isOpen N (-b) b).interior_eq] using hx.2
  rw [neck_closure_region N hb0 hb] at hcl
  obtain ⟨z, hz, rfl⟩ := hcl
  have hs : z ∈ univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨mem_univ _, by linarith [hz.2.1], hz.2.2.trans_lt hb⟩
  have heq := neck_inverse_coordinate N z hs
  refine ⟨hxN, ?_⟩
  rw [heq]
  have hno : ¬ (-b < z.2 ∧ z.2 < b) := by
    intro hi
    apply hnot
    exact ⟨hxN, by rw [heq]; exact hi⟩
  rcases le_total z.2 0 with hneg | hpos
  · rw [abs_of_nonpos hneg]
    push Not at hno
    have hlo : z.2 = -b := by
      by_contra hn
      have hgt : -b < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm hn)
      linarith [hno hgt]
    linarith
  · rw [abs_of_nonneg hpos]
    push Not at hno
    exact le_antisymm hz.2.2 (hno (by linarith))

end PoincareConjecture.M44
