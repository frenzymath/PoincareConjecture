import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.SurfaceCountInclusionExclusion









set_option autoImplicit false
open Set Geometry
open scoped BigOperators
namespace PoincareConjecture.M76.PrismBelt

theorem surfaceEulerCount_double_cover
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (C D : ι → SimplicialComplex ℝ E)
    (hC : ∀ i, (C i).faces ⊆ K.faces)
    (hcover : ∀ s ∈ K.faces, ∃ i, s ∈ (C i).faces)
    (hcontact : ∀ i s, s ∈ (D i).faces ↔
      s ∈ (C i).faces ∧ ∃ j, j ≠ i ∧ s ∈ (C j).faces)
    (hnoThree : ∀ s ∈ K.faces, ∀ i j k,
      s ∈ (C i).faces → s ∈ (C j).faces → s ∈ (C k).faces →
      i = j ∨ i = k ∨ j = k) :
    2 * K.surfaceEulerCount =
      ∑ i, (2 * (C i).surfaceEulerCount - (D i).surfaceEulerCount) := by
  classical
  have hsum (L : SimplicialComplex ℝ E) (hL : L.faces ⊆ K.faces) :
      L.surfaceEulerCount = ∑ s ∈ hK.toFinset,
        if s ∈ L.faces then SimplicialComplex.surfaceFaceWeight s else 0 := by
    rw [L.surfaceEulerCount_eq_sum (hK.subset hL),← Finset.sum_filter]
    congr 1
    ext s
    simp only [Set.Finite.mem_toFinset,Finset.mem_filter]
    exact ⟨fun hs => ⟨hL hs,hs⟩,fun hs => hs.2⟩
  have hD (i : ι) : (D i).faces ⊆ K.faces := fun s hs =>
    hC i ((hcontact i s).mp hs).1
  simp_rw [hsum _ (hC _),hsum _ (hD _),Finset.mul_sum,← Finset.sum_sub_distrib]
  rw [K.surfaceEulerCount_eq_sum hK,Finset.mul_sum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  have hsK : s ∈ K.faces := hK.mem_toFinset.mp hs
  obtain ⟨i,hi⟩ := hcover s hsK
  by_cases hother : ∃ j, j ≠ i ∧ s ∈ (C j).faces
  · obtain ⟨j,hji,hj⟩ := hother
    have hmem (k : ι) : s ∈ (C k).faces ↔ k = i ∨ k = j := by
      constructor
      · intro hk
        rcases hnoThree s hsK i j k hi hj hk with h | h | h
        · exact (hji h.symm).elim
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · rintro (rfl | rfl) <;> assumption
    have hDc (k : ι) : s ∈ (D k).faces ↔ k = i ∨ k = j := by
      rw [hcontact k s,hmem k]
      constructor
      · exact And.left
      · intro hk
        refine ⟨hk,?_⟩
        rcases hk with rfl | rfl
        · exact ⟨j,hji,hj⟩
        · exact ⟨i,Ne.symm hji,hi⟩
    simp_rw [hmem,hDc]
    have hsmall := Finset.sum_subset (s₁ := {i,j}) (s₂ := Finset.univ)
      (f := fun k => 2 * (if k = i ∨ k = j then SimplicialComplex.surfaceFaceWeight s else 0) -
        if k = i ∨ k = j then SimplicialComplex.surfaceFaceWeight s else 0)
      (Finset.subset_univ _) (by
        intro k _ hk
        have hn : k ≠ i ∧ k ≠ j := by simpa using hk
        simp [hn.1,hn.2])
    rw [← hsmall]
    simp only [Finset.sum_pair (Ne.symm hji),true_or,ite_true,or_true]
    ring
  · have hmem (k : ι) : s ∈ (C k).faces ↔ k = i := by
      constructor
      · intro hk
        by_contra hki
        exact hother ⟨k,hki,hk⟩
      · rintro rfl
        exact hi
    have hDc (k : ι) : s ∉ (D k).faces := by
      rintro hk
      obtain ⟨hk,j,hjk,hj⟩ := (hcontact k s).mp hk
      exact hjk ((hmem j).mp hj |>.trans ((hmem k).mp hk).symm)
    simp_rw [hmem,if_neg (hDc _),sub_zero]
    simp

end PoincareConjecture.M76.PrismBelt
