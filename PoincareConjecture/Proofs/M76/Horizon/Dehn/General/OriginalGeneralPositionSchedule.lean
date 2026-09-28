import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalGeneralPositionData
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.FiniteExceptionNeighborhoods









set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}


theorem OriginalGeneralPositionData.exists_exception_schedule
    {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old) :
  let B := (fun z : V2 × V2 ↦
    step.projection (step.inclusion (data.initial.map z.1))) '' data.exceptional
  ∃ (n : ℕ) (q : Fin n ≃ B)
    (w : Fin n → TwoBranchWindow (step.projection ∘ step.inclusion))
    (V : Fin n → Set s.Carrier),
    (∀ k, IsOpen (V k) ∧ (q k : s.Carrier) ∈ V k ∧
      IsCompact (closure (V k)) ∧ closure (V k) ⊆ (w k).target ∧
      B ∩ closure (V k) = {(q k : s.Carrier)} ∧
      ∃ a b : D2, a ≠ b ∧ ((a : V2), (b : V2)) ∈ data.exceptional ∧
        data.initial.map a ∈ (w k).left.source ∧ data.initial.map b ∈ (w k).right.source ∧
        step.projection (step.inclusion (data.initial.map a)) = (q k : s.Carrier)) ∧
    Pairwise (fun k l ↦ Disjoint (closure (V k)) (closure (V l))) ∧
    Pairwise (fun k l ↦
      Disjoint ((step.projection ∘ step.inclusion) ⁻¹' closure (V k))
        ((step.projection ∘ step.inclusion) ⁻¹' closure (V l))) ∧
    ∀ k a b,
      (t.charts a).symm.trans ((w k).left.trans (s.charts b)) ∈
        piecewiseAffineGroupoid V3 ∧
      (t.charts a).symm.trans ((w k).right.trans (s.charts b)) ∈
        piecewiseAffineGroupoid V3 := by
  classical
  let initial := data.initial
  let E := data.exceptional
  have hE := data.exceptional_finite
  have hEs := data.exceptional_eq
  have hZ := data.relation_space
  let p := step.projection ∘ step.inclusion
  let lower := p ∘ initial.map
  let B := (fun z : V2 × V2 ↦ lower z.1) '' E
  have hB : B.Finite := hE.image _
  have hdata (x : B) : ∃ (a b : D2) (w : TwoBranchWindow p),
      a ≠ b ∧ ((a : V2), (b : V2)) ∈ E ∧
      initial.map a ∈ w.left.source ∧ initial.map b ∈ w.right.source ∧
      lower a = (x : s.Carrier) := by
    obtain ⟨z, hzE, hzx⟩ := x.property
    have hz := hZ.subset (hEs.subset hzE).1
    let a : D2 := ⟨z.1, hz.1⟩
    let b : D2 := ⟨z.2, hz.2.1⟩
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
  obtain ⟨n, q, V, hV, hdis⟩ := exists_finite_exception_neighborhoods hB
    (fun x ↦ (w x).target) (fun x ↦ (w x).open_target) hxW
  refine ⟨n, q, w ∘ q, V,
    ?_, hdis, pairwise_disjoint_exception_preimages p V hdis, ?_⟩
  · intro k
    exact ⟨(hV k).1, (hV k).2.1, (hV k).2.2.1, (hV k).2.2.2.1,
      (hV k).2.2.2.2, a (q k), b (q k), hab _, hpair _, ha _, hb _, hvalue _⟩
  · intro k a b
    exact ⟨step.branch_chart_PL (w (q k)).left
      (fun x _ ↦ congrFun (w (q k)).left_eq x) a b,
      step.branch_chart_PL (w (q k)).right
      (fun x _ ↦ congrFun (w (q k)).right_eq x) a b⟩

end Geometry.OriginalPLTower

