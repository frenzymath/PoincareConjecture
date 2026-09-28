import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.Composition.LocalRepair
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Assembly.Construction

set_option autoImplicit false
open Set Geometry Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => PLAnnularStrip.squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => PLAnnularStrip.depth 8 z = -1 ∨
  PLAnnularStrip.depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ P2} {j : P2 → t.Carrier} {R Fmark : Set M}

theorem MarkedSurfacePositionData.nonempty_marked_annulus_boundary_exception_repair
    (D : MarkedSurfacePositionData step K₀ A₀ j R Fmark)
    (hAnn : D.K.space = Ann) (hRim : A₀.space = Rim)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    (a b : D.K.space) (hab : a ≠ b) (haRim : (a : P2) ∈ A₀.space)
    (hpair : D.projected a = D.projected b)
    {W : Set s.Carrier} (hWopen : IsOpen W) (haW : D.projected a ∈ W)
    (hW : W ∩ ((fun z : P2 × P2 => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a}) :
    Nonempty (MarkedSurfaceExceptionRepair D a W) := by
  let a' : Ann := ⟨a, hAnn.subset a.property⟩
  let b' : Ann := ⟨b, hAnn.subset b.property⟩
  have hab' : a' ≠ b' := by
    intro h
    apply hab
    apply Subtype.ext
    exact congrArg (fun x : Ann => (x : P2)) h
  obtain ⟨N, Small, hSmall, _, hSmallW, hcenter, hfix, hcross⟩ :=
    D.exists_annulus_boundary_exception_repair hAnn hRim he hF hopen
      a' b' hab' (hRim.subset haRim) hpair hWopen haW hW 1 zero_lt_one
  exact ⟨{
    motion := N.ambient
    small := Small
    continuous := N.continuous
    inverse_continuous := N.continuous_inverse
    zero := N.zero
    piecewiseAffine := N.ambient_PL
    region := N.region
    mark := N.mark
    outside := fun u => right_branch_motion_fixed_off_window N.window N.chart
      N.support_target (fun _ hz => (N.chart_inside hz).2)
      (fun _ hz => (N.chart_inside hz).1) (N.outside u)
    compact := hSmall
    small_window := subset_union_left.trans hSmallW
    source_fixed := hfix
    center := hcenter
    crossings := hcross }⟩

end Geometry.OriginalPLTower
