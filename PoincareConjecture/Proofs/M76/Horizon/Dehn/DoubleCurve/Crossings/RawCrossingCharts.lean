import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.RawChart
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteTowerDescent
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoBranchWindows

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

abbrev RawCrossingChart {X ι : Type*} [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X V3) (f : V2 → X) (R : Set X) (x y : V2) :=
  Annuli.RawSourceCrossing e f D2 R x y

theorem nonempty_rawCrossingChart_of_twoBranchWindow
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} (d : V2 → Y) (p : Y → X)
    (hd : IsEmbedding (fun z : D2 ↦ d z))
    {R : Set X} {x y : V2} (hx : x ∈ D2) (hy : y ∈ D2)
    (hxy : p (d x) = p (d y)) (w : TwoBranchWindow p)
    (T : OpenPartialHomeomorph X V3)
    (hlabels : (d x ∈ w.left.source ∧ d y ∈ w.right.source) ∨
      (d x ∈ w.right.source ∧ d y ∈ w.left.source))
    (hxT : p (d x) ∈ T.source) (hTw : T.source ⊆ w.target)
    (hcompat : ∀ k, (e k).symm.trans T ∈ piecewiseAffineGroupoid V3)
    (hleft : ∀ z ∈ T.source, z ∈ p '' (d '' D2 ∩ w.left.source) ↔
      T z 0 = 0 ∧ z ∈ R)
    (hright : ∀ z ∈ T.source, z ∈ p '' (d '' D2 ∩ w.right.source) ↔
      T z 1 = 0 ∧ z ∈ R)
    (hregion : T.source ⊆ interior R ∨
      ((∀ z ∈ T.source, z ∈ R ↔ 0 ≤ T z 2) ∧
        ∀ z ∈ T.source, z ∈ frontier R ↔ T z 2 = 0)) :
    Nonempty (RawCrossingChart e (p ∘ d) R x y) := by
  exact Annuli.nonempty_rawSourceCrossing_of_twoBranchWindow d p hd hx hy hxy w T hlabels hxT hTw
    hcompat hleft hright hregion

end PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

open PoincareConjecture.M76.Dehn

theorem Step.nonempty_raw_crossing_charts
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
    ∀ x ∈ D2, ∀ y ∈ D2, x ≠ y →
      (step.projection ∘ step.inclusion ∘ new.map) x =
        (step.projection ∘ step.inclusion ∘ new.map) y →
      Nonempty (RawCrossingChart s.charts (step.projection ∘ step.inclusion ∘ new.map)
        (s.projection ⁻¹' R) x y) := by
  intro x hx y hy hne hxy
  obtain ⟨w, T, hlabels, hxT, hTw, hcompat, hleft, hright, hregion⟩ :=
    hD2 x hx y hy hne hxy
  exact nonempty_rawCrossingChart_of_twoBranchWindow new.map
    (step.projection ∘ step.inclusion) new.embedding hx hy hxy w T hlabels hxT hTw
      hcompat hleft hright hregion

end Geometry.OriginalPLTower
