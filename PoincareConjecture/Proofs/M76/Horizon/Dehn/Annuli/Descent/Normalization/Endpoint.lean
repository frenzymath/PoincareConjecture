import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.ExceptionalValues











set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ V} {j : V → t.Carrier} {R : Set M} {boundary : Set V}

namespace OriginalRelativeNormalization

variable (D : OriginalRelativeNormalization step K j R boundary)

def endpoint : V → t.Carrier := (D.states D.length).map

def projected : V → s.Carrier := (step.projection ∘ step.inclusion) ∘ D.endpoint

omit [FiniteDimensional ℝ V] in
theorem endpoint_PL : PolyhedralPLInCharts t.charts D.endpoint K.space := by
  change PolyhedralPLInCharts t.charts (D.states D.length).map K.space
  rw [← D.subdivision.space_eq]
  exact (D.states D.length).original_PL

omit [FiniteDimensional ℝ V] in
theorem endpoint_embedding : IsEmbedding (fun x : K.space ↦ D.endpoint x) :=
  (D.states D.length).embedding.comp (Homeomorph.setCongr D.subdivision.space_eq.symm).isEmbedding

omit [FiniteDimensional ℝ V] in
theorem endpoint_boundary : EqOn D.endpoint j boundary :=
  (D.fixes_protected D.length le_rfl).mono D.boundary_protected

omit [FiniteDimensional ℝ V] in
theorem projected_boundary : EqOn D.projected ((step.projection ∘ step.inclusion) ∘ j) boundary :=
  fun _ hx ↦ congrArg (step.projection ∘ step.inclusion) (D.endpoint_boundary hx)

omit [FiniteDimensional ℝ V] in
theorem projected_region : MapsTo D.projected K.space (s.projection ⁻¹' R) := by
  intro x hx
  have h := (D.states D.length).region (D.subdivision.space_eq.symm.subset hx)
  change t.projection (D.endpoint x) ∈ R at h
  change s.projection (step.projection (step.inclusion (D.endpoint x))) ∈ R
  rwa [← step.original_eq]

omit [FiniteDimensional ℝ V] in
theorem projected_proper : ∀ x ∈ K.space,
    D.projected x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ boundary := by
  intro x hx
  have h := (D.states D.length).proper x (D.subdivision.space_eq.symm.subset hx)
  rw [step.frontier_preimage R] at h
  exact h



theorem exists_endpoint_double_locus (hK : K.faces.Finite) :
    PolyhedralPLInCharts s.charts D.projected K.space ∧
      IsLocallyInjective (fun x : K.space ↦ D.projected x) ∧
      ∃ (L : SimplicialComplex ℝ (V × V)) (G : SimplicialComplex ℝ V),
        L.faces.Finite ∧ G.faces.Finite ∧
        L.space = {z | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧
          D.projected z.1 = D.projected z.2 ∧ z.1 ≠ z.2} ∧
        G.space = Prod.fst '' L.space ∧ G.space = doubleLocusOn D.projected K.space ∧
        IsCompact G.space ∧ G.space ⊆ K.space :=
  step.exists_finite_source_double_locus K hK D.endpoint_PL D.endpoint_embedding

omit [FiniteDimensional ℝ V] in
theorem endpoint_mate_unique {x y z : V}
    (hx : x ∈ K.space) (hy : y ∈ K.space) (hz : z ∈ K.space)
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hpy : D.projected x = D.projected y) (hpz : D.projected x = D.projected z) : y = z := by
  apply step.projected_source_mate_unique (j := D.endpoint) ?_ hx hy hz hxy hxz hpy hpz
  intro a ha b hb hab
  exact congrArg Subtype.val (D.endpoint_embedding.injective
    (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)

omit [FiniteDimensional ℝ V] in
theorem projected_fiber_finite (z : s.Carrier) : (K.space ∩ D.projected ⁻¹' {z}).Finite := by
  apply (step.projectionInclusion_fiber z).1.of_injOn
    (f := D.endpoint) (fun _ hx ↦ hx.2)
  intro a ha b hb hab
  exact congrArg Subtype.val (D.endpoint_embedding.injective
    (a₁ := ⟨a, ha.1⟩) (a₂ := ⟨b, hb.1⟩) hab)

omit [FiniteDimensional ℝ V] in


theorem exceptional_pairs_finite :
    {z : V × V | z.1 ∈ K.space ∧ z.2 ∈ K.space ∧
      D.projected z.1 = D.projected z.2 ∧ D.projected z.1 ∈ D.exceptionalValues}.Finite := by
  have hfinite : (⋃ q ∈ D.exceptionalValues,
      (K.space ∩ D.projected ⁻¹' {q}) ×ˢ (K.space ∩ D.projected ⁻¹' {q})).Finite :=
    D.exceptionalValues_finite.biUnion fun q _ ↦
      (D.projected_fiber_finite q).prod (D.projected_fiber_finite q)
  apply hfinite.subset
  intro z hz
  exact mem_iUnion₂.mpr ⟨D.projected z.1, hz.2.2.2,
    ⟨hz.1, rfl⟩, hz.2.1, hz.2.2.1.symm⟩



theorem exists_endpoint_boundary_neighborhood (hK : K.faces.Finite)
    (hb : IsCompact boundary) (hrim : InjOn (t.projection ∘ j) boundary) :
    ∃ (O : Set s.Carrier) (ε : ℝ),
      IsOpen O ∧ D.projected '' boundary ⊆ O ∧ 0 < ε ∧
      cthickening ε boundary ⊆ (doubleLocusOn D.projected K.space)ᶜ ∧
      K.space ∩ D.projected ⁻¹' O = K.space \ doubleLocusOn D.projected K.space ∧
      ∀ x ∈ K.space, x ∈ cthickening ε boundary →
        ∀ y ∈ K.space, D.projected x = D.projected y → x = y := by
  have hbK : boundary ⊆ K.space := D.boundary_protected.trans
    ((SimplicialComplex.space_subset_of_le D.protected_le).trans D.subdivision.space_eq.subset)
  have hproper : ∀ x ∈ K.space,
      D.endpoint x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ boundary := by
    intro x hx
    exact (D.states D.length).proper x (D.subdivision.space_eq.symm.subset hx)
  have hrim' : InjOn (t.projection ∘ D.endpoint) boundary := by
    intro x hx y hy hxy
    apply hrim hx hy
    change t.projection (j x) = t.projection (j y)
    change t.projection (D.endpoint x) = t.projection (D.endpoint y) at hxy
    rwa [D.endpoint_boundary hx, D.endpoint_boundary hy] at hxy
  obtain ⟨G, O, ε, _, hGs, _, _, _, hO, hbO, hε, hcollar, hpre, _, hsingle⟩ :=
    step.exists_protected_boundary_projection K hK D.endpoint_PL D.endpoint_embedding
      boundary hb hbK R hproper hrim'
  rw [hGs] at hcollar hpre
  exact ⟨O, ε, hO, hbO, hε, hcollar, hpre, hsingle⟩

end OriginalRelativeNormalization
end Geometry.OriginalPLTower
