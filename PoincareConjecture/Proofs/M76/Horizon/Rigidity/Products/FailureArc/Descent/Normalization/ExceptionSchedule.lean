import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.PositionData
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.FiniteExceptionNeighborhoods
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoBranchWindows
import PoincareConjecture.Proofs.M76.Dehn.OriginalBranchCoordinates

set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

omit [FiniteDimensional ℝ V] in

theorem MarkedSurfacePositionData.exists_exception_schedule
    {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
    {K₀ A₀ : SimplicialComplex ℝ V} {j : V → t.Carrier}
    (data : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    {E : Set (V × V)} (hE : E.Finite) (hErelation : E ⊆ data.relation.space) :
  let B := (fun z : V × V ↦
    step.projection (step.inclusion (data.initial.map z.1))) '' E
  ∃ (n : ℕ) (q : Fin n ≃ B)
    (w : Fin n → TwoBranchWindow (step.projection ∘ step.inclusion))
    (W : Fin n → Set s.Carrier),
    (∀ k, IsOpen (W k) ∧ (q k : s.Carrier) ∈ W k ∧
      IsCompact (closure (W k)) ∧ closure (W k) ⊆ (w k).target ∧
      B ∩ closure (W k) = {(q k : s.Carrier)} ∧
      ∃ a b : data.K.space, a ≠ b ∧ ((a : V), (b : V)) ∈ E ∧
        data.initial.map a ∈ (w k).left.source ∧ data.initial.map b ∈ (w k).right.source ∧
        step.projection (step.inclusion (data.initial.map a)) = (q k : s.Carrier)) ∧
    Pairwise (fun k l ↦ Disjoint (closure (W k)) (closure (W l))) ∧
    Pairwise (fun k l ↦
      Disjoint ((step.projection ∘ step.inclusion) ⁻¹' closure (W k))
        ((step.projection ∘ step.inclusion) ⁻¹' closure (W l))) ∧
    ∀ k a b,
      (t.charts a).symm.trans ((w k).left.trans (s.charts b)) ∈
        piecewiseAffineGroupoid V3 ∧
      (t.charts a).symm.trans ((w k).right.trans (s.charts b)) ∈
        piecewiseAffineGroupoid V3 := by
  classical
  let initial := data.initial
  have hZ := data.relation_space
  let p := step.projection ∘ step.inclusion
  let lower := p ∘ initial.map
  let B := (fun z : V × V ↦ lower z.1) '' E
  have hB : B.Finite := hE.image _
  have hdata (x : B) : ∃ (a b : data.K.space) (w : TwoBranchWindow p),
      a ≠ b ∧ ((a : V), (b : V)) ∈ E ∧
      initial.map a ∈ w.left.source ∧ initial.map b ∈ w.right.source ∧
      lower a = (x : s.Carrier) := by
    obtain ⟨z, hzE, hzx⟩ := x.property
    have hz := hZ.subset (hErelation hzE)
    let a : data.K.space := ⟨z.1, data.source_space.symm.subset hz.1⟩
    let b : data.K.space := ⟨z.2, data.source_space.symm.subset hz.2.1⟩
    have hab : a ≠ b := fun heq ↦ hz.2.2.2 (congrArg Subtype.val heq)
    have hmapne : initial.map a ≠ initial.map b := fun heq ↦
      hab (initial.embedding.injective heq)
    obtain ⟨w, ha, hb⟩ := step.projectionInclusion_local.exists_twoBranchWindow
      (fun y ↦ (step.projectionInclusion_fiber y).1)
      (fun y ↦ (step.projectionInclusion_fiber y).2) hz.2.2.1 hmapne
    exact ⟨a, b, w, hab, hzE, ha, hb, hzx⟩
  choose a b w hab hpair ha hb hvalue using hdata
  have hxW (x : B) : (x : s.Carrier) ∈ (w x).target := by
    rw [← hvalue x, ← (w x).left_target]
    change p (initial.map (a x)) ∈ (w x).left.target
    exact (congrFun (w x).left_eq _) ▸ (w x).left.map_source (ha x)
  obtain ⟨n, q, W, hV, hdis⟩ := exists_finite_exception_neighborhoods hB
    (fun x ↦ (w x).target) (fun x ↦ (w x).open_target) hxW
  refine ⟨n, q, w ∘ q, W,
    ?_, hdis, pairwise_disjoint_exception_preimages p W hdis, ?_⟩
  · intro k
    exact ⟨(hV k).1, (hV k).2.1, (hV k).2.2.1, (hV k).2.2.2.1,
      (hV k).2.2.2.2, a (q k), b (q k), hab _, hpair _, ha _, hb _, hvalue _⟩
  · intro k a b
    exact ⟨step.branch_chart_PL (w (q k)).left
      (fun x _ ↦ congrFun (w (q k)).left_eq x) a b,
      step.branch_chart_PL (w (q k)).right
      (fun x _ ↦ congrFun (w (q k)).right_eq x) a b⟩

end Geometry.OriginalPLTower
