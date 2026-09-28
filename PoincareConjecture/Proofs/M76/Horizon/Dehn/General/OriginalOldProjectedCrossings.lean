import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalGeneralPositionData
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.ProjectedDiskCrossing









set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D2" => closedBall (0 : V2) 1

private def oldCrossingCoordinates : C3 ≃L[ℝ] V3 where
  toFun z := ![z.2, z.1.1, z.1.2]
  invFun z := ((z 1, z 2), z 0)
  left_inv := fun _ ↦ rfl
  right_inv := by intro z; ext i; fin_cases i <;> rfl
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
  {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
  {old : StageMarkedDisk t R Fmark base Jgroup}



theorem OriginalGeneralPositionData.exists_old_projected_crossing
    (data : OriginalGeneralPositionData step old)
    (a b : D2) (hab : a ≠ b)
    (hpair : step.projection (step.inclusion (data.initial.map a)) =
      step.projection (step.inclusion (data.initial.map b)))
    (hex : ((a : V2), (b : V2)) ∉ data.exceptional)
    (W : Set s.Carrier) (hW : IsOpen W)
    (haW : step.projection (step.inclusion (data.initial.map a)) ∈ W) :
    ∃ B : ProjectedDiskCrossing s.charts
      (step.projection ∘ step.inclusion) data.initial.map
      (s.projection ⁻¹' R) a b, B.chart.source ⊆ W := by
  obtain ⟨a', b', w, c, T, hperm, hleft, hright, hpoint, hsource, _hzero,
    hPL, _hbranches, _hpre, hleftEq, hrightEq⟩ :=
    data.crossings a b hab hpair hex W hW haW
  let L := c.trans oldCrossingCoordinates
  let B := T.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hBs : B.source = T.source := by ext z; simp [B]
  have hcompat (k : s.Index) : (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    have hcomp := (locallyPiecewiseAffineOn_affine
      L.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp (hPL k).1
    exact hcomp.mono ((s.charts k).symm.trans B).open_source
      (fun z hz ↦ ⟨⟨hz.1, hBs.subset hz.2⟩, mem_univ _⟩)
  have hlabels :
      (data.initial.map a ∈ w.left.source ∧ data.initial.map b ∈ w.right.source) ∨
      (data.initial.map a ∈ w.right.source ∧ data.initial.map b ∈ w.left.source) := by
    rcases hperm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hleft, hright⟩
    · exact Or.inr ⟨hright, hleft⟩
  exact ⟨{
    window := w
    chart := B
    labels := hlabels
    point := hBs.symm ▸ hpoint
    source := fun z hz ↦ (hsource (hBs.subset hz)).2.2
    compatible := hcompat
    left_image := fun z hz ↦ (hleftEq z (hBs.subset hz)).trans
      ⟨fun h ↦ ⟨h, interior_subset (hsource (hBs.subset hz)).2.1⟩, And.left⟩
    right_image := fun z hz ↦ (hrightEq z (hBs.subset hz)).trans
      ⟨fun h ↦ ⟨h, interior_subset (hsource (hBs.subset hz)).2.1⟩, And.left⟩
    region := Or.inl (fun z hz ↦ (hsource (hBs.subset hz)).2.1) },
    fun z hz ↦ (hsource (hBs.subset hz)).1⟩

end Geometry.OriginalPLTower
