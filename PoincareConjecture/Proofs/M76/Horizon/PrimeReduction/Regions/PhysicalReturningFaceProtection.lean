import PoincareConjecture.Proofs.M76.PrimeReduction.ReturningArcProtection










set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex




theorem exists_physical_returning_face_neighborhood
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace X] [T2Space X]
    {K M : SimplicialComplex ℝ E} (hK : K.faces.Finite) (hMK : M ≤ K)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {Z : Set X} (hZ : IsClosed Z)
    (hmark : ∀ x ∈ K.space, g x ∈ Z ↔ x ∈ M.space)
    {s a : Finset E} (hs : s ∈ K.faces) (ha : a ∈ K.faces)
    (hs3 : s.card = 3) (ha2 : a.card = 2) (has : a ⊆ s)
    {u : E} (hu : u ∈ intrinsicInterior ℝ (convexHull ℝ (a : Set E)))
    (huZ : g u ∉ Z) :
    ∃ U : Set X, IsOpen U ∧
      g '' (intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∪
        intrinsicInterior ℝ (convexHull ℝ (a : Set E))) ⊆ U ∧
      Disjoint U Z ∧ Disjoint U (g '' K.vertices) ∧
      ∀ t ∈ K.faces, t.card ≤ 2 → t ≠ a →
        Disjoint U (g '' convexHull ℝ (t : Set E)) := by
  classical
  have hua : u ∈ K.space := K.convexHull_subset_space ha (intrinsicInterior_subset hu)
  have haM : a ∉ M.faces := by
    intro h
    exact huZ ((hmark u hua).mpr (M.convexHull_subset_space h (intrinsicInterior_subset hu)))
  have hsM : s ∉ M.faces := fun h => haM
    (M.down_closed h has (K.nonempty_of_mem_faces ha))
  let B : Set (Finset E) := {t ∈ K.faces | t.card ≤ 2 ∧ t ≠ a}
  let C := intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∪
    intrinsicInterior ℝ (convexHull ℝ (a : Set E))
  let bad : Set X := Z ∪ ⋃ t ∈ B, g '' convexHull ℝ (t : Set E)
  have hB : B.Finite := hK.subset (fun _ ht => ht.1)
  have hbad : IsClosed bad := hZ.union (hB.isClosed_biUnion fun t ht =>
    (t.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (hgc.mono (K.convexHull_subset_space ht.1)) |>.isClosed)
  have hCK : C ⊆ K.space := by
    rintro x (hx | hx)
    · exact K.convexHull_subset_space hs (intrinsicInterior_subset hx)
    · exact K.convexHull_subset_space ha (intrinsicInterior_subset hx)
  have hCZ (x : E) (hx : x ∈ C) : g x ∉ Z := by
    intro hxZ
    have hxM := (hmark x (hCK hx)).mp hxZ
    rcases hx with hx | hx
    · exact hsM ((mem_subcomplex_of_mem_intrinsicInterior_iff hMK hs hx).mp hxM)
    · exact haM ((mem_subcomplex_of_mem_intrinsicInterior_iff hMK ha hx).mp hxM)
  have hCU : g '' C ⊆ badᶜ := by
    rintro _ ⟨x, hx, rfl⟩ (hxZ | hxB)
    · exact hCZ x hx hxZ
    · obtain ⟨t, ht, y, hyt, heq⟩ := mem_iUnion₂.mp hxB
      have hyx : y = x := hgi (K.convexHull_subset_space ht.1 hyt) (hCK hx) heq
      have hxt := hyx ▸ hyt
      rcases hx with hx | hx
      · have hsub := K.subset_of_mem_intrinsicInterior_face hs ht.1 hx hxt
        have hcard := Finset.card_le_card hsub
        have htc := ht.2.1
        omega
      · have hsub := K.subset_of_mem_intrinsicInterior_face ha ht.1 hx hxt
        have htc := ht.2.1
        exact ht.2.2 (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hdis (t : Finset E) (ht : t ∈ K.faces) (ht2 : t.card ≤ 2) (hta : t ≠ a) :
      Disjoint badᶜ (g '' convexHull ℝ (t : Set E)) := by
    apply disjoint_left.mpr
    intro x hx hxt
    exact hx (Or.inr (mem_iUnion₂.mpr ⟨t, ⟨ht, ht2, hta⟩, hxt⟩))
  refine ⟨badᶜ, hbad.isOpen_compl, hCU,
    disjoint_left.mpr (fun _ hx hz => hx (Or.inl hz)), ?_, hdis⟩
  apply disjoint_left.mpr
  rintro x hx ⟨v, hv, rfl⟩
  have hne : ({v} : Finset E) ≠ a := by
    intro heq
    have hc := congrArg Finset.card heq
    simp only [Finset.card_singleton, ha2] at hc
    omega
  exact disjoint_left.mp (hdis {v} hv (by simp) hne) hx
    (mem_image_of_mem g (by simp))

end Geometry.SimplicialComplex
