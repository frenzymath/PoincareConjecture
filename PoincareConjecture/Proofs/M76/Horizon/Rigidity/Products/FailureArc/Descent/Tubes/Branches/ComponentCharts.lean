import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Branches.ComponentNeighborhoods
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Tubes.Branches.FiniteChart

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)

theorem SourceDoubleComponents.exists_paired_component_charts
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {sourceSet rimSet : Set E} [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    (M : SourceDoubleComponents e f sourceSet rimSet R) (hf : PolyhedralPLInCharts e f sourceSet)
    (i : M.Index) (hi : M.mate i ≠ i) :
    ∃ (P Q : SimplicialComplex ℝ E) (U V : Set sourceSet) (O : Set X)
        (B : f '' M.pieces i → OpenPartialHomeomorph X V3),
      P.faces.Finite ∧ Q.faces.Finite ∧ P.space ⊆ sourceSet ∧ Q.space ⊆ sourceSet ∧
      Disjoint P.space Q.space ∧ IsOpen U ∧ IsOpen V ∧
      (Subtype.val : sourceSet → E) ⁻¹' M.pieces i ⊆ U ∧
      (Subtype.val : sourceSet → E) ⁻¹' M.pieces (M.mate i) ⊆ V ∧
      Subtype.val '' U ⊆ P.space ∧ Subtype.val '' V ⊆ Q.space ∧
      M.pieces i ⊆ P.space ∧ M.pieces (M.mate i) ⊆ Q.space ∧
      IsEmbedding (fun x : P.space ↦ f x) ∧ IsEmbedding (fun x : Q.space ↦ f x) ∧
      PolyhedralPLInCharts e f P.space ∧ PolyhedralPLInCharts e f Q.space ∧
      IsOpen O ∧ f '' M.pieces i ⊆ O ∧
      (∀ x ∈ sourceSet, f x ∈ O → x ∈ P.space ∪ Q.space) ∧
      O ∩ (f '' P.space ∩ f '' Q.space) = f '' M.pieces i ∧
      ∀ y : f '' M.pieces i,
        (y : X) ∈ (B y).source ∧ (B y).source ⊆ O ∧
        (∀ k, (e k).symm.trans (B y) ∈ piecewiseAffineGroupoid V3) ∧
        (∀ z ∈ (B y).source, z ∈ f '' P.space ↔ B y z 0 = 0 ∧ z ∈ R) ∧
        (∀ z ∈ (B y).source, z ∈ f '' Q.space ↔ B y z 1 = 0 ∧ z ∈ R) ∧
        (∀ z ∈ (B y).source,
          z ∈ f '' M.pieces i ↔ z ∈ R ∧ B y z 0 = 0 ∧ B y z 1 = 0) ∧
        ((B y).source ⊆ interior R ∨
          ((∀ z ∈ (B y).source, z ∈ R ↔ 0 ≤ B y z 2) ∧
            ∀ z ∈ (B y).source, z ∈ frontier R ↔ B y z 2 = 0)) := by
  classical
  obtain ⟨P, Q, U, V, O, hP, hQ, hPD, hQD, hPQ, hU, hV,
      hiU, hmV, hUP, hVQ, hiP, hmQ, hPi, hQi, hPPL, hQPL,
      hO, hTO, hfull, hinter⟩ := M.exists_paired_component_neighborhoods hf i hi
  have hiPf : InjOn f P.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hPi.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hiQf : InjOn f Q.space := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hQi.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hcharts (y : f '' M.pieces i) : ∃ T : OpenPartialHomeomorph X V3,
      (y : X) ∈ T.source ∧ T.source ⊆ O ∧
      (∀ k, (e k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (∀ z ∈ T.source, z ∈ f '' P.space ↔ T z 0 = 0 ∧ z ∈ R) ∧
      (∀ z ∈ T.source, z ∈ f '' Q.space ↔ T z 1 = 0 ∧ z ∈ R) ∧
      (∀ z ∈ T.source, z ∈ f '' M.pieces i ↔ z ∈ R ∧ T z 0 = 0 ∧ T z 1 = 0) ∧
      (T.source ⊆ interior R ∨
        ((∀ z ∈ T.source, z ∈ R ↔ 0 ≤ T z 2) ∧
          ∀ z ∈ T.source, z ∈ frontier R ↔ T z 2 = 0)) := by
    obtain ⟨x, hx, hxy⟩ := y.property
    let a : M.graph.space := ⟨x, M.pieces_subset i hx⟩
    have haQ : (M.partner a : E) ∈ Q.space := hmQ ((M.partner_component i a).mp hx)
    have hne : x ≠ (M.partner a : E) := (M.free a).symm
    have hval : f x = f (M.partner a) := (M.value a).symm
    obtain ⟨C⟩ := M.crossings x (M.space.subset a.property).1 (M.partner a) (M.space.subset (M.partner a).property).1 hne hval
    obtain ⟨T, hxT, hTO', hcompat, hleft, hright, haxis, hregion, _⟩ :=
      C.exists_finite_branch_chart hf (P.isCompact_space_of_finite hP)
        (Q.isCompact_space_of_finite hQ) hPD hQD hiPf hiQf (hiP hx) haQ hval
        hO (hTO ⟨x, hx, rfl⟩) hfull hinter
    exact ⟨T, hxy ▸ hxT, hTO', hcompat, hleft, hright, haxis, hregion⟩
  choose B hB using hcharts
  exact ⟨P, Q, U, V, O, B, hP, hQ, hPD, hQD, hPQ, hU, hV,
    hiU, hmV, hUP, hVQ, hiP, hmQ, hPi, hQi, hPPL, hQPL,
    hO, hTO, hfull, hinter, hB⟩

end PoincareConjecture.M76.Dehn.Annuli
