import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FreeFaceCarrierBounds
import PoincareConjecture.Proofs.M76.Mathlib.MinimalFaceRadialTransport
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms



set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem convex_subset_affine_of_ball
    {C : Set E} (hC : Convex ℝ C) {x : E} (hx : x ∈ C)
    {ε : ℝ} (hε : 0 < ε) (A : AffineSubspace ℝ E)
    (hlocal : C ∩ Metric.ball x ε ⊆ A) : C ⊆ A := by
  have hxA : x ∈ A := hlocal ⟨hx, Metric.mem_ball_self hε⟩
  intro y hy
  obtain ⟨r, hr, hrball⟩ := Set.exists_pos_smul_mem_of_mem_nhds
    (Metric.ball_mem_nhds (0 : E) hε) (y - x)
  let z := r • (y - x) + x
  have hzEq : z = AffineMap.lineMap x y r := by
    simp only [z, AffineMap.lineMap_apply_module]
    module
  have hzC : z ∈ C := hzEq.symm ▸
    hC.segment_subset hx hy (lineMap_mem_segment ℝ x y ⟨hr.1.le, hr.2⟩)
  have hzball : z ∈ Metric.ball x ε := by
    simpa only [z, Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hrball
  have hd := A.direction.smul_mem r⁻¹ (A.vsub_mem_direction (hlocal ⟨hzC, hzball⟩) hxA)
  have hd' : y - x ∈ A.direction := by
    simpa only [vsub_eq_sub, z, add_sub_cancel_right, inv_smul_smul₀ hr.1.ne'] using hd
  change y ∈ A
  simpa only [vadd_eq_add, sub_add_cancel] using A.vadd_mem_of_mem_direction hd' hxA

theorem pure_of_finite_same_carrier
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    (hspace : L.space = K.space) {n : ℕ}
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = n ∧ s ⊆ t) :
    ∀ s ∈ L.faces, ∃ t ∈ L.faces, t.card = n ∧ s ⊆ t := by
  classical
  have hboundK : ∀ s ∈ K.faces, s.card ≤ n := by
    intro s hs
    obtain ⟨t, _, htc, hst⟩ := hpure s hs
    exact htc ▸ Finset.card_le_card hst
  have hboundL : ∀ s ∈ L.faces, s.card ≤ n := by
    intro s hs
    exact L.face_card_le_of_hull_subset_finite_carrier K hK hs
      ((L.convexHull_subset_space hs).trans hspace.subset) hboundK
  intro s hs
  obtain ⟨x, hxs⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
    (Finset.coe_nonempty.mpr (L.nonempty_of_mem_faces hs)).convexHull
  obtain ⟨a, ha, hxa⟩ := mem_space_iff.mp
    (hspace.subset (L.convexHull_subset_space hs (intrinsicInterior_subset hxs)))
  obtain ⟨t, ht, htc, hat⟩ := hpure a ha
  have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono hat hxa
  obtain ⟨U, hU, hxU, hUfaces⟩ := L.exists_open_face_hulls_contain_point hL x
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  by_contra hnot
  let A : Set (Finset E) := {a | a ∈ L.faces ∧ s ⊆ a}
  have hA : A.Finite := hL.subset fun _ ha => ha.1
  let : Finite A := hA.to_subtype
  let planes : A → AffineSubspace ℝ E := fun a => affineSpan ℝ (a.val : Set E)
  have hcover : convexHull ℝ (t : Set E) ∩ Metric.ball x ε ⊆
      ⋃ a, (planes a : Set E) := by
    rintro y ⟨hyt, hyball⟩
    obtain ⟨a, ha, hya⟩ := mem_space_iff.mp
      (hspace.symm.subset (K.convexHull_subset_space ht hyt))
    have hxa := hUfaces a ha ⟨y, hya, hball hyball⟩
    have hsa := L.subset_of_mem_intrinsicInterior_face hs ha hxs hxa
    exact mem_iUnion.mpr ⟨⟨a, ha, hsa⟩, convexHull_subset_affineSpan _ hya⟩
  obtain ⟨a, ha⟩ := Convex.exists_subset_affineSubspace_of_subset_iUnion
    ((convex_convexHull ℝ (t : Set E)).inter (convex_ball x ε))
    ⟨x, hxt, Metric.mem_ball_self hε⟩ planes hcover
  have hwhole := convex_subset_affine_of_ball (convex_convexHull ℝ (t : Set E))
    hxt hε (planes a) ha
  have hle := (K.indep ht).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ (t : Set E)).trans hwhole)
  have heq : a.val.card = n := Nat.le_antisymm (hboundL a.val a.property.1)
    (htc ▸ hle)
  exact hnot ⟨a.val, a.property.1, heq, a.property.2⟩

theorem IsSubdivision.pure_of_finite
    {K L : SimplicialComplex ℝ E} (hLK : L.IsSubdivision K)
    (hK : K.faces.Finite) (hL : L.faces.Finite) {n : ℕ}
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = n ∧ s ⊆ t) :
    ∀ s ∈ L.faces, ∃ t ∈ L.faces, t.card = n ∧ s ⊆ t :=
  K.pure_of_finite_same_carrier L hK hL hLK.space_eq hpure

end Geometry.SimplicialComplex
