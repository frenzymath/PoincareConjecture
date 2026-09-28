import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Contacts.ExceptionalValues









set_option autoImplicit false
open Set Geometry Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier} {R Fmark : Set M}

namespace MarkedSurfacePositionData

variable (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)

omit [FiniteDimensional ℝ V] in
theorem projected_region : MapsTo D.projected D.K.space (s.projection ⁻¹' R) := by
  intro x hx
  have h := (D.states D.length).region hx
  change t.projection (D.endpoint x) ∈ R at h
  change s.projection (step.projection (step.inclusion (D.endpoint x))) ∈ R
  rwa [← step.original_eq]

omit [FiniteDimensional ℝ V] in
theorem projected_proper : ∀ x ∈ D.K.space,
    D.projected x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ A₀.space := by
  intro x hx
  have h := (D.states D.length).proper x hx
  rw [step.frontier_preimage R] at h
  exact h

theorem double_point_interior_of_not_exceptional
    {x y : V} (hx : x ∈ D.K.space) (hy : y ∈ D.K.space) (hne : x ≠ y)
    (hxy : D.projected x = D.projected y) (hex : D.projected x ∉ D.exceptionalValues) :
    D.projected x ∈ interior (s.projection ⁻¹' R) := by
  obtain ⟨i, x', y', old, a, b, hswap, hxface, _, _, _, _, _, _, _, hi3, _⟩ :=
    D.exists_triangle_interiors_of_not_exceptional hx hy hne hxy hex
  have hbase : D.projected x' = D.projected x := by
    rcases hswap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact hxy.symm
  have hxK := D.K.convexHull_subset_space (D.order i).property (intrinsicInterior_subset hxface)
  by_contra hn
  have hfront : D.projected x' ∈ frontier (s.projection ⁻¹' R) :=
    hbase.symm ▸ ⟨subset_closure (D.projected_region hx), hn⟩
  have hxA := D.boundary_space.symm.subset ((D.projected_proper x' hxK).mp hfront)
  obtain ⟨c, hc, hxc⟩ := D.A.mem_space_iff.mp hxA
  have hsub := D.K.subset_of_mem_intrinsicInterior_face (D.order i).property
    (D.boundary_subcomplex hc) hxface hxc
  have hcard := (Finset.card_le_card hsub).trans (D.boundary_dimension c hc)
  omega

omit [FiniteDimensional ℝ V] in
theorem projected_fiber_finite (z : s.Carrier) :
    (D.K.space ∩ D.projected ⁻¹' {z}).Finite := by
  apply (step.projectionInclusion_fiber z).1.of_injOn (f := D.endpoint) (fun _ hx => hx.2)
  intro a ha b hb hab
  exact congrArg Subtype.val ((D.states D.length).embedding.injective
    (a₁ := ⟨a, ha.1⟩) (a₂ := ⟨b, hb.1⟩) hab)

omit [FiniteDimensional ℝ V] in
theorem exceptional_pairs_finite :
    {z : V × V | z.1 ∈ D.K.space ∧ z.2 ∈ D.K.space ∧
      D.projected z.1 = D.projected z.2 ∧ D.projected z.1 ∈ D.exceptionalValues}.Finite := by
  have hfinite : (⋃ q ∈ D.exceptionalValues,
      (D.K.space ∩ D.projected ⁻¹' {q}) ×ˢ (D.K.space ∩ D.projected ⁻¹' {q})).Finite :=
    D.exceptionalValues_finite.biUnion fun q _ =>
      (D.projected_fiber_finite q).prod (D.projected_fiber_finite q)
  apply hfinite.subset
  intro z hz
  exact mem_iUnion₂.mpr ⟨D.projected z.1, hz.2.2.2,
    ⟨hz.1, rfl⟩, hz.2.1, hz.2.2.1.symm⟩

end MarkedSurfacePositionData
end Geometry.OriginalPLTower
