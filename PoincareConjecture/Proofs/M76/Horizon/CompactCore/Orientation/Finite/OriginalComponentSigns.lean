import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Orientation.Finite.AllEdgeSigns

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains
open AbstractSimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_frontier_component_all_edge_signs
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3)
    (hcover : ∀ x : X, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K) (hA : A.faces.Finite)
    (g : E → X) (N : Set X)
    (hgi : InjOn g K.space) (hfront : MapsTo g A.space (frontier N))
    (hstars : ∀ p ∈ K.vertices, ∃ D : OpenPartialHomeomorph X V3,
      (∀ i, (e i).symm.trans D ∈ piecewiseAffineGroupoid V3) ∧
      MapsTo g (K.closedStar p).space D.source ∧
      (K.closedStar p).AffineOnFaces (D ∘ g) ∧
      (D.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (n : V3),
        ell.contLinear n = 1 ∧ ∀ y ∈ D.source, y ∈ N ↔ 0 ≤ ell (D y)))
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {R C F T : Set X} (HC : (A.edgeComponentComplex c).space ≃ₜ T)
    (hHC : ∀ z, (HC z : X) = g z)
    (hTF : T ⊆ F) (hFU : F ⊆ R \ C)
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
    let J := A.edgeComponentComplex c
    ∃ (number : J.vertices ↪ ℕ)
      (sigma : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex → ZMod 2),
      ∀ (t u : Triangle J.vertexAbstractComplex.toPreAbstractSimplicialComplex), t ≠ u →
        ∀ s : Edge J.vertexAbstractComplex.toPreAbstractSimplicialComplex,
          s.val ⊆ t.val → s.val ⊆ u.val →
          (sigma t + boundaryFaceParity number t.val s.val) +
            (sigma u + boundaryFaceParity number u.val s.val) = 1 := by
  let J := A.edgeComponentComplex c
  have hJK : J ≤ K := (A.edgeComponentComplex_le c).trans hAK
  have hJ : J.faces.Finite := hA.subset (A.edgeComponentComplex_le c)
  have hfrontJ : MapsTo g J.space (frontier N) :=
    fun _ hz => hfront (Geometry.SimplicialComplex.space_subset_of_le (A.edgeComponentComplex_le c) hz)
  have hlabels := exists_frontier_component_compatible_chart_labels
    e hcover hcompat A hA c HC hTF hFU hloops
  obtain ⟨hq, label, hchange⟩ := hlabels
  let charts := {H : OpenPartialHomeomorph X V3 |
    ∀ i, (e i).symm.trans H ∈ piecewiseAffineGroupoid V3}
  let restrict (H : charts) : C({z : J.space | g z ∈ H.val.source},
      {z : J.space | (HC z : X) ∈ H.val.source}) :=
    ⟨fun z => ⟨z.val, by
      change (HC z.val : X) ∈ H.val.source
      rw [hHC]
      exact z.property⟩,
      continuous_subtype_val.subtype_mk
        (fun z => by
          change (HC z.val : X) ∈ H.val.source
          rw [hHC]
          exact z.property)⟩
  let labels (H : charts) := LocallyConstant.comap (restrict H) (label H)
  apply exists_frontier_all_edge_signs_of_chart_labels e K J hJK hJ g N hgi hfrontJ hstars
    hq labels
  intro H D z hH hD
  have hH' : (HC z : X) ∈ H.val.source := (hHC z).symm ▸ hH
  have hD' : (HC z : X) ∈ D.val.source := (hHC z).symm ▸ hD
  have h := hchange H D z hH' hD'
  dsimp only [labels, LocallyConstant.coe_comap_apply, restrict, ContinuousMap.coe_mk]
  have hs : (⟨g z, hH, hD⟩ : (H.val.source ∩ D.val.source : Set X)) =
      ⟨HC z, hH', hD'⟩ := Subtype.ext (hHC z).symm
  have hsign := congrArg (plAtlasTransitionSign (fun H : charts => H.val) hq H D) hs
  rw [hsign]
  exact h

end PoincareConjecture.M76
