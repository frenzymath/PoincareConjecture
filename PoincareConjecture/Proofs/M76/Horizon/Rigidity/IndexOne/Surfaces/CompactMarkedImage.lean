import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.LocalPolyhedralImage

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

theorem exists_compact_marked_polyhedral_image
    {M E G ι : Type*} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (e : ι → OpenPartialHomeomorph M E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {F : M → G}
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    {S B : Set M} (hS : IsCompact S) (hinj : InjOn F S)
    (hcharts : ∀ x ∈ S, ∃ (T : OpenPartialHomeomorph M E)
        (V : Set M) (cuts marks : Finset (E →ᵃ[ℝ] ℝ)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ T.source ∧
      (∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid E) ∧
      (∀ y ∈ V, y ∈ S ↔ ∀ a ∈ cuts, a (T y) ≤ 0) ∧
      ∀ y ∈ V, y ∈ B ↔ ∀ a ∈ marks, a (T y) ≤ 0) :
    ∃ K L : SimplicialComplex ℝ G, K.faces.Finite ∧ L.faces.Finite ∧
      K.space = F '' S ∧ L.space = F '' (S ∩ B) := by
  classical
  have hlocal (x : S) :
      ∃ (U D : Set M) (K L : SimplicialComplex ℝ G),
        IsOpen U ∧ (x : M) ∈ U ∧ D ⊆ S ∧ U ∩ S ⊆ D ∧
        K.faces.Finite ∧ L.faces.Finite ∧
        K.space = F '' D ∧ L.space = F '' (D ∩ B) := by
    obtain ⟨T, V, cuts, marks, hV, hxV, hVT, hT, hVS, hVB⟩ := hcharts x x.property
    exact exists_local_polyhedral_image_pair hinj T
      (OpenPartialHomeomorph.locallyPiecewiseAffineOn_compatible_chart e hcover hF T hT)
      cuts marks hV hVT hVS hVB hxV
  choose U D K L hU hxU hDS hUD hK hL hKD hLD using hlocal
  obtain ⟨s, hs⟩ := hS.elim_finite_subcover U hU
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  have hDcover : (⋃ a : s, D a) = S := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨a, hxa⟩ := mem_iUnion.mp hx
      exact hDS a hxa
    · intro x hx
      obtain ⟨a, has, hxa⟩ := mem_iUnion₂.mp (hs hx)
      exact mem_iUnion.mpr ⟨⟨a, has⟩, hUD a ⟨hxa, hx⟩⟩
  obtain ⟨K', hK', hKs, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion (fun a : s => K a) (fun a => hK a)
  obtain ⟨L', hL', hLs, _⟩ :=
    SimplicialComplex.exists_finite_triangulation_iUnion (fun a : s => L a) (fun a => hL a)
  refine ⟨K', L', hK', hL', ?_, ?_⟩
  · rw [hKs]
    simp_rw [hKD]
    rw [← image_iUnion, hDcover]
  · rw [hLs]
    simp_rw [hLD]
    rw [← image_iUnion, ← iUnion_inter, hDcover]

end PoincareConjecture.M76.HamiltonIntervalTorus
