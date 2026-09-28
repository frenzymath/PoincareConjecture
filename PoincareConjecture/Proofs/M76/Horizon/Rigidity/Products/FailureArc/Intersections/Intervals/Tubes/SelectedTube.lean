import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Source.SourceBranches
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Intervals.Source.SelectedComponent

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "stripSource" => PolygonalCrossingResolution.source

theorem SourceDoubleComponents.exists_selected_interval_tube
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X}
    {S Q C D : Set E} {R W : Set X}
    (old : SourceDoubleComponents e f S Q R) (hf : PolyhedralPLInCharts e f S)
    (he : PLDomain e R)
    (hball : IsFinitePLBallPair ℝ C (C ∩ Q))
    (hCsub : C ⊆ doubleLocusOn f S) (hrest : IsClosed (doubleLocusOn f S \ C))
    (hCinj : InjOn f C) (hDsub : D ⊆ S) (hdis : Disjoint C D)
    (hfull : ∀ x ∈ S, f x ∈ f '' C ↔ x ∈ C ∪ D)
    (hin : MapsTo f S R) (hfront : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ Q)
    (hW : IsOpen W) (hCW : f '' C ⊆ W) :
    ∃ (c : Bool → P2 → E) (τ : C3 → X),
      (∀ j, FinitePiecewiseAffineOn (c j) stripSource ∧
        IsEmbedding (fun p : stripSource => c j p) ∧ MapsTo (c j) stripSource S) ∧
      Disjoint (c false '' stripSource) (c true '' stripSource) ∧
      PolyhedralPLInCharts e τ tube ∧ IsEmbedding (fun z : tube => τ z) ∧
      MapsTo τ tube R ∧ MapsTo τ tube W ∧
      (∀ j p, p ∈ stripSource → f (c j p) = τ (originalStripSheet j p)) ∧
      S ∩ f ⁻¹' (τ '' tube) = c false '' stripSource ∪ c true '' stripSource ∧
      (∀ j, c j '' arm 0 = if j then D else C) ∧
      (∀ z ∈ tube, τ z ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1) ∧
      ∀ j p, p ∈ stripSource → (c j p ∈ Q ↔ p.1 = 0 ∨ p.1 = 1) := by
  obtain ⟨i,hi⟩ := old.exists_index_of_isolated_connected_set
    hball.isCompact hball.isConnected hCsub hrest
  obtain ⟨_,hmi⟩ := old.mate_eq_of_literal_fibers i (hi.symm ▸ hCinj) hDsub
    (hi.symm ▸ hdis) (hi.symm ▸ hfull)
  obtain ⟨c,τ,hc,hcd,hτ,hτi,hτR,hτW,hval,hpre,hcenter,hτfront,hrim⟩ :=
    old.exists_interval_tube_source_strips hf he i (hi.symm ▸ hball) hin hfront hW (hi.symm ▸ hCW)
  refine ⟨c,τ,hc,hcd,hτ,hτi,hτR,hτW,hval,hpre,?_,hτfront,hrim⟩
  intro j
  cases j
  · simpa only [Bool.false_eq_true,if_false,hi] using hcenter false
  · simpa only [if_true,hmi] using hcenter true

end PoincareConjecture.M76.Dehn.Annuli
