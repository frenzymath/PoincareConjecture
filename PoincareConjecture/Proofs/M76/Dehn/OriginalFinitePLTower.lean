import PoincareConjecture.Proofs.M76.Dehn.OriginalPLSuccessor
import PoincareConjecture.Proofs.M76.Dehn.InitialOriginalPLTower
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoverTowerCount
import Mathlib.Order.WellFounded

set_option autoImplicit false

universe u v w z a b

open Set Topology Geometry

namespace Geometry.OriginalPLTower

variable {U : Type u} {E : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem exists_terminal_reachable
    {G : Type b} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : M → G) (hq : InjOn q C) (hF : FinitePiecewiseAffineOn (q ∘ f) S.space)
    (hS : S.faces.Finite)
    [SimplyConnectedSpace S.space] [LocallyPathConnectedSpace S.space]
    (v0 : S.space) (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target)
    (s0 : Stage e S f r C) :
    ∃ t : Stage e S f r C, Reaches s0 t ∧
      ∀ (Y : Type a) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
        (p : Y → t.Carrier), IsCoveringMap p →
          (∀ x, (p ⁻¹' {x}).ncard = 2) → False := by
  classical
  obtain ⟨T, _, hcount⟩ :=
    hF.exists_strict_two_sheet_neighborhood_count ⟨v0, v0.property⟩
  let m : Stage e S f r C → ℕ := fun s => T.ncard - (s.source '' T).ncard
  have hdecrease {s t : Stage e S f r C} (step : Step s t) : m t < m s := by
    let H : (ContinuousMap.id s.Carrier).HomotopyRel s.endpoint (range s.source) :=
      { s.deformation.toHomotopy with
        prop' := fun tau x hx => s.deformation.eq_fst tau (s.range_source.subset hx) }
    have hend (x : s.Carrier) : s.endpoint x ∈ range s.source := by
      rw [s.range_source, ← s.endpoint_range]
      exact mem_range_self x
    have h := hcount s.Carrier (q ∘ s.projection) (s.graph_local q hq)
      step.Cover step.projection step.covering step.two t.Carrier
      step.inclusion step.openEmbedding.injective s.source
      (fun x => congrArg q (s.source_eq x x.property)) t.source
      (fun x => step.source_eq x x.property) s.endpoint H hend
    exact h.2.2.2
  let A : Set (Stage e S f r C) := {t | Reaches s0 t}
  have hA : A.Nonempty := ⟨s0, Relation.ReflTransGen.refl⟩
  let t := Function.argminOn m A hA
  have ht : t ∈ A := Function.argminOn_mem m A hA
  refine ⟨t, ht, ?_⟩
  intro Y instTop instT2 instConn p hp htwo
  obtain ⟨n, ⟨step⟩⟩ := exists_step_of_two_sheet_cover t hS v0 hr hrPL hp htwo
  have hn : n ∈ A := ht.tail ⟨step⟩
  exact Function.not_lt_argminOn m A hn (hdecrease step)

theorem exists_original_terminal_stage [T2Space M] [LocallyCompactSpace M]
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hS : S.faces.Finite)
    [SimplyConnectedSpace S.space] [LocallyPathConnectedSpace S.space]
    (hf : PolyhedralPLInCharts e f S.space) (v0 : S.space)
    {R : Set M} (hfR : MapsTo f S.space R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (r : M → ℝ) (W : Set M) (s : Finset (f '' S.space))
      (q : M → (s → ℝ × E)) (C : Set M) (s0 t : Stage e S f r C),
      IsOpen W ∧ IsCompact C ∧ f '' S.space ⊆ interior C ∧ C ⊆ W ∧
      Continuous r ∧
      (∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target) ∧
      Continuous q ∧
      (∀ i, LocallyPiecewiseAffineOn (q ∘ (e i).symm) (e i).target) ∧
      InjOn q C ∧ FinitePiecewiseAffineOn (q ∘ f) S.space ∧
      IsOpenEmbedding s0.projection ∧ Reaches s0 t ∧
      (∀ (Y : Type a) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
        (p : Y → t.Carrier), IsCoveringMap p →
          (∀ x, (p ⁻¹' {x}).ncard = 2) → False) ∧
      ∀ y ∈ W, (y ∈ R ↔ 0 ≤ r y) ∧
        (y ∈ frontier R ↔ r y = 0) ∧ (y ∈ interior R ↔ 0 < r y) := by
  obtain ⟨r, W, s, q, C, s0, hW, hC, hAC, hCW, hr, hrPL, hq, hqPL,
    hqinj, hF, hs0, hcut⟩ :=
    exists_original_graph_stage e hcompat hcover S hS hf v0 hfR hboundary
  obtain ⟨t, hreach, hterm⟩ := exists_terminal_reachable q hqinj hF hS v0 hr hrPL s0
  exact ⟨r, W, s, q, C, s0, t, hW, hC, hAC, hCW, hr, hrPL,
    hq, hqPL, hqinj, hF, hs0, hreach, hterm, hcut⟩

end Geometry.OriginalPLTower
