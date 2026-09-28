import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskNormalLabels









set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (V2 × ℝ)
local notation "Cube" => closedBall (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : Cube ≃ₜ D}



noncomputable def HamiltonProperDiskTriangulation.dualRegion
    (T : HamiltonProperDiskTriangulation R D b) (s : Finset E) : Set E :=
  let : Fintype T.ambient.faces := T.finite.fintype
  (T.ambient.barycentricDualBlock s).space ∩ R

omit [DecidableEq E] in
private theorem dual_point_in_original_coface
    (K : SimplicialComplex ℝ E) [Fintype K.faces] {s : Finset E} {x : E}
    (hx : x ∈ (K.barycentricDualBlock s).space) :
    ∃ t ∈ K.faces, s ⊆ t ∧ x ∈ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨f, hf, hxf⟩ := SimplicialComplex.mem_space_iff.mp hx
  obtain ⟨a, ha, hchain, hfa⟩ := (K.barycentricSubdivision_faces f).mp hf.1
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
  have him (i : K.faces) (hi : i ∈ a) : i.val ⊆ m.val := by
    rcases hchain i hi m hm with h | h
    · exact h
    · exact hmax hi h
  have hcent : m.val.centroid ℝ id ∈ f := hfa.symm ▸ Finset.mem_image.mpr ⟨m, hm, rfl⟩
  obtain ⟨u, hu, hsu, hum⟩ := hf.2 _ hcent
  have humEq : (⟨u, hu⟩ : K.faces) = m := K.faceCentroid_injective hum
  have hum' : u = m.val := congrArg Subtype.val humEq
  refine ⟨m.val, m.property, hum' ▸ hsu, ?_⟩
  apply convexHull_min _ (convex_convexHull ℝ _) hxf
  intro y hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hfa ▸ hy)
  exact convexHull_mono (him i hi)
    (i.val.centroid_mem_convexHull (K.nonempty_of_mem_faces i.property))





theorem HamiltonProperDiskTriangulation.exists_full_coface_of_dualRegion
    [FiniteDimensional ℝ E] (T : HamiltonProperDiskTriangulation R D b)
    (p : T.disk.vertices) (c : E ≃ᴬ[ℝ] V) {s : Finset E} (hps : (p : E) ∈ s)
    {x : E} (hx : x ∈ T.dualRegion s) :
    ∃ u ∈ T.ambient.faces, s ⊆ u ∧ u.card = 4 ∧ x ∈ convexHull ℝ (u : Set E) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  obtain ⟨t, ht, hst, hxt⟩ := dual_point_in_original_coface T.ambient hx.1
  have hpt := hst hps
  have htstar : t ∈ (T.ambient.closedStar p).faces :=
    ⟨ht, by simpa only [Finset.insert_eq_of_mem hpt] using ht⟩
  have hpS : (p : E) ∈ (T.pairChart p).chart.source := T.star_source p
    ((T.ambient.closedStar p).subset_space htstar hpt)
  have hpD : (p : E) ∈ D := T.disk_space.subset (T.disk.vertices_subset_space p.property)
  have hpR : (p : E) ∈ R := by
    rcases (T.pairChart p).model with ⟨hi, _⟩ | ⟨hr, hd⟩
    · exact interior_subset (hi hpS)
    · exact (hr p hpS).mpr ((hd p hpS).mp hpD).1
  obtain ⟨u, hu, htu, huc⟩ := T.ambient.exists_full_coface_of_hull_meets_interior
    T.finite ht ⟨p, subset_convexHull ℝ _ hpt, T.region_interior hpR⟩
  have hdim : Module.finrank ℝ E = 3 := by
    simpa [Module.finrank_prod] using c.toAffineEquiv.linear.finrank_eq
  exact ⟨u, hu, hst.trans htu, by simpa [hdim] using huc, convexHull_mono htu hxt⟩



theorem HamiltonProperDiskTriangulation.dualRegion_subset_chart_source
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    {s : Finset E} (hps : (p : E) ∈ s) :
    T.dualRegion s ⊆ (T.pairChart p).chart.source := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  intro x hx
  obtain ⟨t, ht, hst, hxt⟩ := dual_point_in_original_coface T.ambient hx.1
  have hpt := hst hps
  exact T.star_source p ((T.ambient.closedStar p).convexHull_subset_space
    ⟨ht, by simpa only [Finset.insert_eq_of_mem hpt] using ht⟩ hxt)




theorem HamiltonProperDiskNormalLabels.half_eq_on_triangle_dual
    [FiniteDimensional ℝ E] {T : HamiltonProperDiskTriangulation R D b}
    {c : E ≃ᴬ[ℝ] V} (O : HamiltonProperDiskNormalLabels T c)
    (p q : T.disk.vertices) {s : Finset E} (hs : s ∈ T.disk.faces)
    (hsc : s.card = 3) (hps : (p : E) ∈ s) (hqs : (q : E) ∈ s) :
    T.dualRegion s ∩ {x | 0 ≤ O.height p x} =
      T.dualRegion s ∩ {x | 0 ≤ O.height q x} := by
  have hpS := T.dualRegion_subset_chart_source p hps
  have hqS := T.dualRegion_subset_chart_source q hqs
  have hR : T.dualRegion s ⊆ R := inter_subset_right
  have hpoint (x : E) (hx : x ∈ T.dualRegion s) (hxD : x ∉ D) :
      0 < O.height p x * O.height q x := by
    obtain ⟨u, hu, hsu, huc, hxu⟩ := T.exists_full_coface_of_dualRegion p c hps hx
    have hpn : ((T.pairChart p).chart x).2 ≠ 0 := by
      intro h
      apply hxD
      apply (O.height_eq_zero_iff p (hpS hx) (hR hx)).mp
      exact mul_eq_zero_of_right _ h
    have hqn : ((T.pairChart q).chart x).2 ≠ 0 := by
      intro h
      apply hxD
      apply (O.height_eq_zero_iff q (hqS hx) (hR hx)).mp
      exact mul_eq_zero_of_right _ h
    exact O.mul_pos_on_common_triangle p q hs hsc hps hqs hu huc hsu hxu hpn hqn
  apply O.half_eq_of_whole_signs p q hR hpS hqS
  · intro x hx
    by_cases hxD : x ∈ D
    · change 0 ≤ O.height q x
      rw [(O.height_eq_zero_iff q (hqS hx.1) (hR hx.1)).mpr hxD]
    · have hprod := hpoint x hx.1 hxD
      by_contra hn
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hx.2 (le_of_not_ge hn))) hprod
  · intro x hx
    by_cases hxD : x ∈ D
    · change O.height q x ≤ 0
      rw [(O.height_eq_zero_iff q (hqS hx.1) (hR hx.1)).mpr hxD]
    · have hprod := hpoint x hx.1 hxD
      by_contra hn
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hx.2 (le_of_not_ge hn))) hprod

end PoincareConjecture.M76.HamiltonIndexOne
