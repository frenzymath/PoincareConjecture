import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Towers.MarkedSuccessor
import PoincareConjecture.Proofs.M76.Dehn.InitialOriginalPLTower
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoverTowerCount
import Mathlib.Order.WellFounded













set_option autoImplicit false

universe v w z a b

open Set Metric Topology Geometry
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {E : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ (V1 × V2)}
  {f : (V1 × V2) → M} {r : M → ℝ} {C : Set M}




theorem exists_annulus_terminal_reachable
    {G : Type b} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (q : M → G) (hq : InjOn q C) (hF : FinitePiecewiseAffineOn (q ∘ f) S.space)
    (hS : S.faces.Finite) (hsource : S.space = ProtectedAnnulus.source)
    (v0 : S.space) (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target)
    (s0 : Stage e S f r C) :
    ∃ t : Stage e S f r C, Reaches s0 t ∧
      ∀ (Y : Type a) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
        (p : Y → t.Carrier), IsCoveringMap p →
          (∀ x, (p ⁻¹' {x}).ncard = 2) →
          ∀ negative : C(Q2, Y),
            (∀ u : Q2,
              p (negative u) = t.sourceMap (ProtectedAnnulus.endpoint false, u)) → False := by
  classical
  obtain ⟨T, _, hcount⟩ :=
    hF.exists_strict_two_sheet_neighborhood_count ⟨v0, v0.property⟩
  let m : Stage e S f r C → ℕ := fun s ↦ T.ncard - (s.source '' T).ncard
  have hdecrease {s t : Stage e S f r C} (step : Step s t) : m t < m s := by
    let H : (ContinuousMap.id s.Carrier).HomotopyRel s.endpoint (range s.source) :=
      { s.deformation.toHomotopy with
        prop' := fun tau x hx ↦ s.deformation.eq_fst tau (s.range_source.subset hx) }
    have hend (x : s.Carrier) : s.endpoint x ∈ range s.source := by
      rw [s.range_source, ← s.endpoint_range]
      exact mem_range_self x
    have h := hcount s.Carrier (q ∘ s.projection) (s.graph_local q hq)
      step.Cover step.projection step.covering step.two t.Carrier
      step.inclusion step.openEmbedding.injective s.source
      (fun x ↦ congrArg q (s.source_eq x x.property)) t.source
      (fun x ↦ step.source_eq x x.property) s.endpoint H hend
    exact h.2.2.2
  let A : Set (Stage e S f r C) := {t | Reaches s0 t}
  have hA : A.Nonempty := ⟨s0, Relation.ReflTransGen.refl⟩
  let t := Function.argminOn m A hA
  have ht : t ∈ A := Function.argminOn_mem m A hA
  refine ⟨t, ht, ?_⟩
  intro Y instTop instT2 instConn p hp htwo negative hnegative
  obtain ⟨n, ⟨step⟩⟩ :=
    exists_annulus_step_of_two_sheet_cover t hS hsource v0 hr hrPL hp htwo negative hnegative
  have hn : n ∈ A := ht.tail ⟨step⟩
  exact Function.not_lt_argminOn m A hn (hdecrease step)






theorem exists_original_annulus_terminal_stage [T2Space M] [LocallyCompactSpace M]
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hf : PolyhedralPLInCharts e f ProtectedAnnulus.source)
    {R : Set M} (hfR : MapsTo f ProtectedAnnulus.source R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ S : SimplicialComplex ℝ (V1 × V2),
      S.faces.Finite ∧ S.space = ProtectedAnnulus.source ∧
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
            (∀ x, (p ⁻¹' {x}).ncard = 2) →
            ∀ negative : C(Q2, Y),
              (∀ u : Q2,
                p (negative u) = t.sourceMap (ProtectedAnnulus.endpoint false, u)) → False) ∧
        ∀ y ∈ W, (y ∈ R ↔ 0 ≤ r y) ∧
          (y ∈ frontier R ↔ r y = 0) ∧ (y ∈ interior R ↔ 0 < r y) := by
  obtain ⟨S, hS, hsource⟩ := ProtectedAnnulus.exists_source_triangulation
  let : PathConnectedSpace ProtectedAnnulus.source := protectedAnnulus_pathConnectedSpace
  let : PathConnectedSpace S.space :=
    (Homeomorph.setCongr hsource).symm.surjective.pathConnectedSpace
      (Homeomorph.setCongr hsource).symm.continuous
  let v0 : S.space := ⟨(ProtectedAnnulus.endpoint false, squareRimBase),
    hsource.symm ▸ ⟨sphere_subset_closedBall (ProtectedAnnulus.endpoint_mem_sphere false),
      squareRimBase.property⟩⟩
  obtain ⟨r, W, s, q, C, s0, hW, hC, hAC, hCW, hr, hrPL, hq, hqPL,
    hqinj, hF, hs0, hcut⟩ :=
    exists_original_graph_stage e hcompat hcover S hS (hsource.symm ▸ hf) v0
      (hsource.symm ▸ hfR) hboundary
  obtain ⟨t, hreach, hterm⟩ :=
    exists_annulus_terminal_reachable q hqinj hF hS hsource v0 hr hrPL s0
  exact ⟨S, hS, hsource, r, W, s, q, C, s0, t, hW, hC, hAC, hCW, hr, hrPL,
    hq, hqPL, hqinj, hF, hs0, hreach, hterm, hcut⟩

end Geometry.OriginalPLTower
