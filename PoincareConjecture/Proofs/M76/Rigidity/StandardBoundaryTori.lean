import PoincareConjecture.Proofs.M76.Rigidity.StandardHierarchySurfaces
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PeriodCircleLoop

set_option autoImplicit false

open Set Metric Topology

namespace PoincareConjecture.M76

local notation "V1" => (Fin 1 → ℝ)
local notation "D1" => closedBall (0 : V1) 1
local notation "L1" => hamiltonLowerPeriodLattice (Fin 2)
local notation "H1" => LatticeHandle (Fin 1) (Fin 2) L1
local notation "C1" => AddCircle (4 * (128 : ℝ))

noncomputable def hamiltonOneTorusSlice (x : D1) : C(C1 × C1, H1) :=
  ⟨fun z => hamiltonOneHierarchyCoordinates.symm ((x, z.1), z.2),
    hamiltonOneHierarchyCoordinates.symm.continuous.comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)⟩

noncomputable def hamiltonOneTorusProjection : C(H1, C1 × C1) :=
  ⟨fun y => ((hamiltonOneHierarchyCoordinates y).1.2,
      (hamiltonOneHierarchyCoordinates y).2),
    (continuous_fst.snd.prodMk continuous_snd).comp
      hamiltonOneHierarchyCoordinates.continuous⟩

theorem hamiltonOneTorusProjection_leftInverse (x : D1) :
    Function.LeftInverse hamiltonOneTorusProjection (hamiltonOneTorusSlice x) := by
  intro z
  change ((hamiltonOneHierarchyCoordinates
      (hamiltonOneHierarchyCoordinates.symm ((x, z.1), z.2))).1.2,
    (hamiltonOneHierarchyCoordinates
      (hamiltonOneHierarchyCoordinates.symm ((x, z.1), z.2))).2) = z
  rw [hamiltonOneHierarchyCoordinates.apply_symm_apply]

theorem range_hamiltonOneTorusSlice (x : D1) :
    range (hamiltonOneTorusSlice x) = {y | y.1 = x} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rfl
  · intro hy
    refine ⟨((hamiltonOneHierarchyCoordinates y).1.2,
      (hamiltonOneHierarchyCoordinates y).2), ?_⟩
    apply hamiltonOneHierarchyCoordinates.injective
    change hamiltonOneHierarchyCoordinates (hamiltonOneHierarchyCoordinates.symm
      ((x, (hamiltonOneHierarchyCoordinates y).1.2),
        (hamiltonOneHierarchyCoordinates y).2)) = hamiltonOneHierarchyCoordinates y
    rw [hamiltonOneHierarchyCoordinates.apply_symm_apply]
    apply Prod.ext
    · apply Prod.ext
      · exact hy.symm
      · rfl
    · rfl

theorem isEmbedding_hamiltonOneTorusSlice (x : D1) :
    IsEmbedding (hamiltonOneTorusSlice x) :=
  (hamiltonOneTorusProjection_leftInverse x).isEmbedding
    hamiltonOneTorusProjection.continuous (hamiltonOneTorusSlice x).continuous

theorem isCompact_range_hamiltonOneTorusSlice (x : D1) :
    IsCompact (range (hamiltonOneTorusSlice x)) := by
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  rw [← image_univ]
  exact isCompact_univ.image (hamiltonOneTorusSlice x).continuous

theorem isConnected_range_hamiltonOneTorusSlice (x : D1) :
    IsConnected (range (hamiltonOneTorusSlice x)) := by
  rw [← image_univ]
  exact isConnected_univ.image _ (hamiltonOneTorusSlice x).continuous.continuousOn

theorem hamiltonOneTorusSlice_pi1_injective (x : D1) (z : C1 × C1) :
    Function.Injective (FundamentalGroup.map (hamiltonOneTorusSlice x) z) :=
  FundamentalGroup.map_injective_of_leftInverse _ _
    (hamiltonOneTorusProjection_leftInverse x) z

theorem nontrivial_pi1_hamiltonOneBoundaryTorus :
    Nontrivial (FundamentalGroup (C1 × C1) (0, 0)) := by
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let : Nontrivial (FundamentalGroup C1 0) :=
    AddCircle.nontrivial_fundamentalGroup_zero (4 * (128 : ℝ))
  exact (FundamentalGroup.map_prodMk_left_injective (0 : C1) (0 : C1)).nontrivial

def hamiltonOneBoundaryMinus : D1 :=
  ⟨fun _ => -1, by simp⟩

def hamiltonOneBoundaryPlus : D1 :=
  ⟨fun _ => 1, by simp⟩

theorem hamiltonOneBoundaryMinus_ne_plus :
    hamiltonOneBoundaryMinus ≠ hamiltonOneBoundaryPlus := by
  intro h
  have he : (-1 : ℝ) = 1 := congrArg (fun x : D1 => (x : V1) 0) h
  norm_num at he

theorem hamiltonOne_norm_eq_one_iff (x : D1) :
    ‖(x : V1)‖ = 1 ↔
      x = hamiltonOneBoundaryMinus ∨ x = hamiltonOneBoundaryPlus := by
  have hconst : (x : V1) = fun _ : Fin 1 => (x : V1) 0 := by
    funext i
    fin_cases i
    rfl
  have hnorm : ‖(x : V1)‖ = |(x : V1) 0| := by
    rw [hconst, pi_norm_const, Real.norm_eq_abs]
  constructor
  · intro hx
    rw [hnorm] at hx
    rcases le_total 0 ((x : V1) 0) with hpos | hneg
    · right
      rw [abs_of_nonneg hpos] at hx
      apply Subtype.ext
      change (x : V1) = fun _ => 1
      rw [hconst, hx]
    · left
      rw [abs_of_nonpos hneg] at hx
      have he : (x : V1) 0 = -1 := by linarith
      apply Subtype.ext
      change (x : V1) = fun _ => -1
      rw [hconst, he]
  · rintro (rfl | rfl)
    · simp [hamiltonOneBoundaryMinus]
    · simp [hamiltonOneBoundaryPlus]

theorem hamiltonOneBoundary_eq_torusSlices :
    latticeHandleBoundary (Fin 1) (Fin 2) L1 =
      range (hamiltonOneTorusSlice hamiltonOneBoundaryMinus) ∪
        range (hamiltonOneTorusSlice hamiltonOneBoundaryPlus) := by
  rw [range_hamiltonOneTorusSlice, range_hamiltonOneTorusSlice]
  ext y
  change (‖(y.1 : V1)‖ = 1 ∧ True) ↔
    y.1 = hamiltonOneBoundaryMinus ∨ y.1 = hamiltonOneBoundaryPlus
  rw [and_true, hamiltonOne_norm_eq_one_iff]

theorem disjoint_hamiltonOneBoundaryTori :
    Disjoint (range (hamiltonOneTorusSlice hamiltonOneBoundaryMinus))
      (range (hamiltonOneTorusSlice hamiltonOneBoundaryPlus)) := by
  rw [range_hamiltonOneTorusSlice, range_hamiltonOneTorusSlice]
  exact disjoint_left.mpr fun _ hm hp =>
    hamiltonOneBoundaryMinus_ne_plus (hm.symm.trans hp)

end PoincareConjecture.M76
