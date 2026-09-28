import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.Repairs.CarrierCrossings









set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.AnnulusBranchMotion

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "A" => (V1 × V2)
local notation "Rim" => Set.prod (sphere (0 : V1) 1) (sphere (0 : V2) 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K : SimplicialComplex ℝ A} {j : A → t.Carrier} {R : Set M}
  {D : OriginalRelativeNormalization step K j R Rim}
  {a b : K.space} {W : Set s.Carrier} {ε : ℝ}
  (N : AnnulusBranchMotion D a b W ε)

theorem exists_whole_crossing
    (hcard : ∀ q ∈ K.faces, q.card ≤ 3)
    (hW : W ∩ D.exceptionalDoubleValues ⊆ {D.projected a})
    {z : V3} (hz : z ∈ N.movedBranch.space)
    (hzJ : z ∈ interior N.support.space) (hz0 : (N.coordinates z).2 = 0)
    (V : Set s.Carrier) (hV : IsOpen V) (hzV : N.chart.symm z ∈ V) :
    ∃ T : OpenPartialHomeomorph s.Carrier V3,
      N.chart.symm z ∈ T.source ∧ T (N.chart.symm z) = 0 ∧
      T.source ⊆ V ∩ (N.chart.source ∩ interior (s.projection ⁻¹' R)) ∧
      (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
      (step.projection ∘ step.inclusion) ⁻¹' T.source =
        (N.window.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
          (N.window.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
      (∀ y ∈ T.source, y ∈ (step.projection ∘ step.inclusion) ''
        ((N.ambient 1 ∘ D.endpoint) '' K.space ∩ N.window.left.source) ↔
          (N.coordinates (T y)).1.1 = 0) ∧
      ∀ y ∈ T.source, y ∈ (step.projection ∘ step.inclusion) ''
        ((N.ambient 1 ∘ D.endpoint) '' K.space ∩ N.window.right.source) ↔
          (N.coordinates (T y)).2 = 0 := by
  let O := interior N.support.space ∩ (N.chart.target ∩ N.chart.symm ⁻¹' V)
  have hO : IsOpen O := isOpen_interior.inter
    (N.chart.symm.isOpen_inter_preimage hV)
  have hzO : z ∈ O := ⟨hzJ, N.support_target (interior_subset hzJ), hzV⟩
  obtain ⟨H, hzH, hHO, hH0, hHPL, hflat, hbranch⟩ :=
    N.exists_carrier_crossing hcard hW hz hzJ hz0 O hO hzO
  apply exists_two_branch_chart_of_local_carrier_chart s.charts
    (step.projection ∘ step.inclusion) N.window
    ((N.ambient 1 ∘ D.endpoint) '' K.space) N.chart N.coordinates
    N.support.space N.movedBranch.space (interior (s.projection ⁻¹' R)) V
    (fun y hy ↦ (N.chart_inside hy).2.2) N.lower_PL N.support_target
    N.moved_right_image hzJ H hzH hH0 hHO hHPL
    (fun y hy _ ↦ (N.chart_inside hy).2.1) ?_ hbranch
  intro y hy hyH
  rw [N.moved_left_image]
  exact (N.left_plane y hy).trans (hflat (N.chart y) hyH)

end Geometry.OriginalPLTower.AnnulusBranchMotion
