import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.PositionedCircleDisk

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_protected_circle_cap_neighborhood
    {E X ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (g : E → X) (hgc : ContinuousOn g K.space) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    {D r Z : Set X} (hZ : IsClosed Z) (hDZ : Disjoint D Z)
    (hDs : D ⊆ g '' intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hcap : D ∩ (⋃ j, S j) = r) (i : κ) (hri : r ⊆ S i)
    (Q : OpenPartialHomeomorph X V3) (hDQ : D ⊆ Q.source) :
    ∃ O : Set X, IsOpen O ∧ D ⊆ O ∧ O ⊆ Q.source ∧ Disjoint O Z ∧
      (∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
        Disjoint O (g '' convexHull ℝ (a : Set E))) ∧
      ∀ j, j ≠ i → Disjoint O (S j) := by
  classical
  let bad : Set X := ⋃ a ∈ K.faces, ⋃ (_ : a.card ≤ 3), ⋃ (_ : a ≠ s),
    g '' convexHull ℝ (a : Set E)
  have hbad : IsClosed bad := hK.isClosed_biUnion fun a ha =>
    isClosed_iUnion_of_finite fun _ => isClosed_iUnion_of_finite fun _ =>
      ((a.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
        (hgc.mono (K.convexHull_subset_space ha))).isClosed
  have hDbad : Disjoint D bad := by
    apply disjoint_left.mpr
    intro x hxD hxb
    obtain ⟨u, hu, rfl⟩ := hDs hxD
    simp only [bad, mem_iUnion] at hxb
    obtain ⟨a, ha, hac, hane, v, hv, hvg⟩ := hxb
    have huv : v = u := hgi (K.convexHull_subset_space ha hv)
      (K.convexHull_subset_space hs (intrinsicInterior_subset hu)) hvg
    have hsa : s ⊆ a := K.subset_of_mem_intrinsicInterior_face hs ha hu (huv ▸ hv)
    exact hane (Finset.eq_of_subset_of_card_le hsa (by omega)).symm
  let others : Set X := ⋃ j : {j : κ // j ≠ i}, S j.val
  have hothers : IsClosed others :=
    isClosed_iUnion_of_finite fun j : {j : κ // j ≠ i} => (sS j.val).isCompact.isClosed
  have hDothers : Disjoint D others := by
    apply disjoint_left.mpr
    intro x hxD hxO
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxO
    have hxi := hri (hcap.subset ⟨hxD, (subset_iUnion S j.val) hxj⟩)
    exact disjoint_left.mp (hdis j.property) hxj hxi
  let O := Q.source ∩ (Z ∪ bad ∪ others)ᶜ
  refine ⟨O, Q.open_source.inter ((hZ.union hbad).union hothers).isOpen_compl,
    ?_, inter_subset_left, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨hDQ hx, ?_⟩
    rintro ((hz | hb) | ho)
    · exact disjoint_left.mp hDZ hx hz
    · exact disjoint_left.mp hDbad hx hb
    · exact disjoint_left.mp hDothers hx ho
  · exact disjoint_left.mpr (fun _ hx hz => hx.2 (Or.inl (Or.inl hz)))
  · intro a ha hac hane
    apply disjoint_left.mpr
    intro x hx hxa
    apply hx.2
    exact Or.inl (Or.inr (mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha,
      mem_iUnion.mpr ⟨hac, mem_iUnion.mpr ⟨hane, hxa⟩⟩⟩⟩))
  · intro j hji
    exact disjoint_left.mpr (fun _ hx hxj =>
      hx.2 (Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hxj⟩)))

end PoincareConjecture.M76
