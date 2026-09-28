import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.LocalRepair



set_option autoImplicit false
open Set Geometry Topology unitInterval

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ P2} {j : P2 → t.Carrier} {R Fmark : Set M}

theorem MarkedSurfacePositionData.assemble_finite_marked_repairs
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (repair : ∀ (a b : D.K.space), a ≠ b → D.projected a = D.projected b →
      ∀ W : Set s.Carrier, IsOpen W → D.projected a ∈ W →
        W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a} →
        Nonempty (MarkedSurfaceExceptionRepair D a W)) :
    Nonempty (FiniteMarkedSurfaceRepairs D) := by
  classical
  obtain ⟨n, q, _, W, hW, hdis, _, _⟩ :=
    D.exists_exception_schedule D.repairPairs_finite D.repairPairs_subset_relation
  have hpairs (k : Fin n) : ∃ a b : D.K.space,
      a ≠ b ∧ D.projected a = (q k : s.Carrier) ∧
        D.projected b = (q k : s.Carrier) := by
    obtain ⟨a, b, hab, hpair, _, _, ha⟩ := (hW k).2.2.2.2.2
    have hz := D.relation_space.subset (D.repairPairs_subset_relation hpair)
    have hxy : D.projected a = D.projected b := by
      simpa only [MarkedSurfacePositionData.projected, MarkedSurfacePositionData.endpoint,
        ← D.final_state, Function.comp_apply] using hz.2.2.1
    have ha' : D.projected a = (q k : s.Carrier) := by
      simpa only [MarkedSurfacePositionData.projected, MarkedSurfacePositionData.endpoint,
        ← D.final_state, Function.comp_apply] using ha
    exact ⟨a, b, hab, ha', hxy.symm.trans ha'⟩
  choose a b hab ha hb using hpairs
  have hsingle (k : Fin n) :
      W k ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆
        {D.projected (a k)} := by
    intro z hz
    have hzB : z ∈ (fun z : P2 × P2 =>
        step.projection (step.inclusion (D.initial.map z.1))) '' D.repairPairs := by
      simpa only [MarkedSurfacePositionData.projected, MarkedSurfacePositionData.endpoint,
        ← D.final_state, Function.comp_apply] using hz.2
    have hm := (hW k).2.2.2.2.1.subset ⟨hzB, subset_closure hz.1⟩
    exact hm.trans (ha k).symm
  let N (k : Fin n) := Classical.choice
    (repair (a k) (b k) (hab k) ((ha k).trans (hb k).symm) (W k)
      (hW k).1 ((ha k).symm ▸ (hW k).2.1) (hsingle k))
  refine ⟨{
    size := n
    window := W
    motion := fun k => (N k).motion
    small := fun k => (N k).small
    disjoint := fun k l hkl => (hdis hkl).mono subset_closure subset_closure
    continuous := fun k => (N k).continuous
    inverse_continuous := fun k => (N k).inverse_continuous
    zero := fun k => (N k).zero
    piecewiseAffine := fun k => (N k).piecewiseAffine
    region := fun k => (N k).region
    mark := fun k => (N k).mark
    outside := fun k => (N k).outside
    compact := fun k => (N k).compact
    small_window := fun k => (N k).small_window
    source_fixed := fun k => (N k).source_fixed
    cover := ?_
    crossings := fun k => (N k).crossings }⟩
  intro z hz
  have hzB : z ∈ (fun z : P2 × P2 =>
      step.projection (step.inclusion (D.initial.map z.1))) '' D.repairPairs := by
    simpa only [MarkedSurfacePositionData.projected, MarkedSurfacePositionData.endpoint,
      ← D.final_state, Function.comp_apply] using hz
  obtain ⟨k, hk⟩ := q.surjective ⟨z, hzB⟩
  have hq : (q k : s.Carrier) = z := congrArg Subtype.val hk
  exact mem_iUnion.mpr ⟨k, ((ha k).trans hq) ▸ (N k).center⟩

end Geometry.OriginalPLTower
