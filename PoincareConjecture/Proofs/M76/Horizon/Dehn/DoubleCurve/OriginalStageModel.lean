import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.OrdinaryModel
import PoincareConjecture.Proofs.M76.Dehn.OriginalOrdinaryDoubleArcComponents

set_option autoImplicit false

open Set Metric Geometry Topology PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem Step.nonempty_ordinary_double_curve_model
    {M ι : Type*} [TopologicalSpace M]
    {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
    {f : V2 → M} {r : M → ℝ} {C : Set M}
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    {base : Fmark} {J : Subgroup (FundamentalGroup Fmark base)}
    (new : StageMarkedDisk t R Fmark base J)
    (hD2 : ∀ x ∈ D2, ∀ y ∈ D2, x ≠ y →
      step.projection (step.inclusion (new.map x)) =
        step.projection (step.inclusion (new.map y)) →
      ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
        (T : OpenPartialHomeomorph s.Carrier V3),
        ((new.map x ∈ w.left.source ∧ new.map y ∈ w.right.source) ∨
          (new.map x ∈ w.right.source ∧ new.map y ∈ w.left.source)) ∧
        step.projection (step.inclusion (new.map x)) ∈ T.source ∧
        T.source ⊆ w.target ∧
        (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
        (∀ z ∈ T.source,
          z ∈ (step.projection ∘ step.inclusion) '' (new.map '' D2 ∩ w.left.source) ↔
            T z 0 = 0 ∧ z ∈ s.projection ⁻¹' R) ∧
        (∀ z ∈ T.source,
          z ∈ (step.projection ∘ step.inclusion) '' (new.map '' D2 ∩ w.right.source) ↔
            T z 1 = 0 ∧ z ∈ s.projection ⁻¹' R) ∧
        (T.source ⊆ interior (s.projection ⁻¹' R) ∨
          ((∀ z ∈ T.source, z ∈ s.projection ⁻¹' R ↔ 0 ≤ T z 2) ∧
            ∀ z ∈ T.source, z ∈ frontier (s.projection ⁻¹' R) ↔ T z 2 = 0))) :
    Nonempty (OrdinaryDoubleCurveModel s.charts
      (step.projection ∘ step.inclusion ∘ new.map) (s.projection ⁻¹' R)) := by
  classical
  obtain ⟨G, p, hG, hGs, hp, _, hp2, hpfree, hpvalue, hpunique, hprim,
    _, _, _, pieces, mate, hFinite, _, hcover, hdisj, htop, hmodels, hmate, hmem, _, _, _⟩ :=
    step.exists_original_ordinary_double_components new hD2
  let lower := step.projection ∘ step.inclusion ∘ new.map
  have hGs' : G.space = doubleLocusOn lower D2 := by
    rw [hGs]
    ext x
    simp only [doubleLocusOn, mem_ofPred_eq, lower, Function.comp_apply]
    exact and_congr_right fun _ ↦ exists_congr fun _ ↦ and_congr_right fun _ ↦ and_comm
  let E := Homeomorph.setCongr hGs'
  have hE : E.IsFinitePL := Homeomorph.isFinitePL_setCongr hGs' G hG rfl
  let q := E.symm.trans (p.trans E)
  have hq2 : Function.Involutive q := by
    intro x
    change E (p (E.symm (E (p (E.symm x))))) = x
    rw [E.symm_apply_apply, hp2, E.apply_symm_apply]
  refine ⟨{
    Index := G.vertexAbstractComplex.edgeGraph.ConnectedComponent
    finiteIndex := hFinite
    pieces := pieces
    mate := mate
    mate_involutive := hmate
    cover := hcover.symm.trans hGs'
    compact := fun i ↦ (htop i).1
    connected := fun i ↦ (htop i).2.1
    disjoint := hdisj
    models := hmodels
    partner := q
    partnerPL := hE.symm.trans (hp.trans hE)
    partner_involutive := hq2
    partner_value := ?_
    partner_free := ?_
    partner_rim := ?_
    unique_partner := ?_
    partner_component := ?_
    crossings := step.nonempty_raw_crossing_charts new hD2 }⟩
  · intro x
    exact (hpvalue (E.symm x)).symm
  · intro x h
    exact hpfree (E.symm x) (Subtype.ext h)
  · intro x
    exact hprim (E.symm x)
  · intro x y hy hxy hne
    exact hpunique (E.symm x) y hy hne hxy
  · intro i x hx
    exact (hmem i (E.symm x)).mp hx

end Geometry.OriginalPLTower
