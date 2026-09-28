import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.Extension.RegionMotion



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.PeriodicSquare
local notation "I" => unitInterval
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

theorem SourceSquareMap.exists_original_torus_translation_motion
    {E X ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R S : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hconn : IsConnected R)
    (hSB : S ⊆ frontier R) (hS : IsClopen ((Subtype.val : frontier R → X) ⁻¹' S))
    {p : ℝ} [Fact (0 < p)] {A : SimplicialComplex ℝ E}
    (model : SourceSquareMap p A) (hA : A.faces.Finite)
    (F : E → X) (hF : PolyhedralPLInCharts e F A.space)
    (H : A.space ≃ₜ S) (hFval : ∀ x : A.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (model.map z)) (v : P2) :
    ∃ M : I → R ≃ₜ R,
      Continuous (fun z : I × R => M z.1 z.2) ∧
      Continuous (fun z : I × R => (M z.1).symm z.2) ∧
      M 0 = Homeomorph.refl R ∧
      (∀ t, ChartwisePLHomeomorph e e (M t)) ∧
      (∀ t (x : S),
        (M t ⟨x, he.closed.frontier_subset (hSB x.property)⟩ : X) =
          h (h.symm x + (((t : ℝ) * v.1 : AddCircle p), ((t : ℝ) * v.2 : AddCircle p)))) ∧
      (∀ t (x : R), (x : X) ∈ frontier R → (x : X) ∉ S → M t x = x) ∧
      (∀ t (x : R), (M t x : X) ∈ frontier R ↔ (x : X) ∈ frontier R) ∧
      ∀ t (x : R), (M t x : X) ∈ S ↔ (x : X) ∈ S := by
  obtain ⟨G, track, hG, hGi, hG0, htrack, htrackval, htranslate⟩ :=
    model.exists_finitePL_translation_track he.compatible hA H F hF hFval h hvalue v
  obtain ⟨M, hM, hMi, hM0, hMPL, hMval, hout, hfront⟩ :=
    he.exists_original_boundary_component_motion hR hconn hSB hS A hA F hF H hFval
      G hG hGi hG0 track htrack htrackval
  refine ⟨M, hM, hMi, hM0, hMPL, ?_, hout, hfront, ?_⟩
  · intro t x
    obtain ⟨z, rfl⟩ := H.surjective x
    rw [hMval]
    exact congrArg Subtype.val (htranslate t z)
  · intro t x
    constructor
    · intro hx
      let z : A.space := (G t).symm (H.symm ⟨M t x, hx⟩)
      have hMx : (M t ⟨H z, he.closed.frontier_subset (hSB (H z).property)⟩ : X) = M t x := by
        rw [hMval]
        change (H (G t ((G t).symm (H.symm ⟨M t x, hx⟩))) : X) = M t x
        rw [(G t).apply_symm_apply, H.apply_symm_apply]
      have hxval := congrArg Subtype.val ((M t).injective (Subtype.ext hMx))
      exact hxval ▸ (H z).property
    · intro hx
      let z : A.space := H.symm ⟨x, hx⟩
      have hzval : (H z : X) = x := congrArg Subtype.val (H.apply_symm_apply ⟨x, hx⟩)
      have hinput : (⟨H z, he.closed.frontier_subset (hSB (H z).property)⟩ : R) = x :=
        Subtype.ext hzval
      rw [← hinput, hMval]
      exact (H (G t z)).property

end PoincareConjecture.M76.PeriodicSquare
