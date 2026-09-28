import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Intervals.PairedComponentNeighborhoods
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Crossings.FiniteBranchCrossingCharts









set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1



theorem OrdinaryDoubleCurveModel.exists_paired_component_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    (M : OrdinaryDoubleCurveModel e f R) (hf : PolyhedralPLInCharts e f D2)
    (i : M.Index) (hi : M.mate i ≠ i) :
    ∃ (P Q : SimplicialComplex ℝ V2) (U V : Set D2) (O : Set X)
        (B : f '' M.pieces i → OpenPartialHomeomorph X V3),
      P.faces.Finite ∧ Q.faces.Finite ∧ P.space ⊆ D2 ∧ Q.space ⊆ D2 ∧
      Disjoint P.space Q.space ∧ IsOpen U ∧ IsOpen V ∧
      (Subtype.val : D2 → V2) ⁻¹' M.pieces i ⊆ U ∧
      (Subtype.val : D2 → V2) ⁻¹' M.pieces (M.mate i) ⊆ V ∧
      Subtype.val '' U ⊆ P.space ∧ Subtype.val '' V ⊆ Q.space ∧
      M.pieces i ⊆ P.space ∧ M.pieces (M.mate i) ⊆ Q.space ∧
      IsEmbedding (fun x : P.space ↦ f x) ∧ IsEmbedding (fun x : Q.space ↦ f x) ∧
      PolyhedralPLInCharts e f P.space ∧ PolyhedralPLInCharts e f Q.space ∧
      IsOpen O ∧ f '' M.pieces i ⊆ O ∧
      (∀ x ∈ D2, f x ∈ O → x ∈ P.space ∪ Q.space) ∧
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
    let a : doubleLocusOn f D2 := ⟨x, M.piece_subset_double i hx⟩
    have haQ : (M.partner a : V2) ∈ Q.space := hmQ (M.partner_component i a hx)
    have hne : x ≠ (M.partner a : V2) := (M.partner_free a).symm
    have hval : f x = f (M.partner a) := (M.partner_value a).symm
    obtain ⟨C⟩ := M.crossings x a.property.1 (M.partner a) (M.partner a).property.1 hne hval
    obtain ⟨T, hxT, hTO', hcompat, hleft, hright, haxis, hregion, _⟩ :=
      C.exists_finite_branch_chart hf (P.isCompact_space_of_finite hP)
        (Q.isCompact_space_of_finite hQ) hPD hQD hiPf hiQf (hiP hx) haQ hval
        hO (hTO ⟨x, hx, rfl⟩) hfull hinter
    exact ⟨T, hxy ▸ hxT, hTO', hcompat, hleft, hright, haxis, hregion⟩
  choose B hB using hcharts
  exact ⟨P, Q, U, V, O, B, hP, hQ, hPD, hQD, hPQ, hU, hV,
    hiU, hmV, hUP, hVQ, hiP, hmQ, hPi, hQi, hPPL, hQPL,
    hO, hTO, hfull, hinter, hB⟩

end PoincareConjecture.M76.Dehn
