import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.StandardAnnulus
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ShiftedCircleClosedArc










set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V1" => (Fin 1 → ℝ)
local notation "D1" => closedBall (0 : V1) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩


noncomputable def standardAmbientCoordinates : X ≃ₜ ((V1 × C) × C) := by
  let q := hamiltonLowerLatticePiEquiv (Fin 2)
  refine {
    toFun := fun z => ((z.1, q z.2 0), q z.2 1)
    invFun := fun z => (z.1.1, q.symm ![z.1.2, z.2])
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro z
    apply Prod.ext
    · rfl
    · apply q.injective
      change q (q.symm ![q z.2 0, q z.2 1]) = q z.2
      rw [q.apply_symm_apply]
      funext i
      fin_cases i <;> rfl
  · intro z
    change ((z.1.1, q (q.symm ![z.1.2, z.2]) 0),
      q (q.symm ![z.1.2, z.2]) 1) = z
    rw [q.apply_symm_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (continuous_fst.prodMk
      ((continuous_apply 0).comp (q.continuous.comp continuous_snd))).prodMk
        ((continuous_apply 1).comp (q.continuous.comp continuous_snd))
  · apply continuous_fst.fst.prodMk
    apply q.symm.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst.snd
    · exact continuous_snd

theorem standard_domain_eq_coordinate_preimage :
    R = standardAmbientCoordinates ⁻¹' ((D1 ×ˢ (univ : Set C)) ×ˢ (univ : Set C)) := by
  ext x
  change (x.1 ∈ D1 ∧ x.2 ∈ (univ : Set _)) ↔ (x.1 ∈ D1 ∧ True) ∧ True
  simp

theorem standard_sourceSlab_eq_coordinate_preimage (a b : ℝ) :
    sourceSlab (ContinuousMap.id H) a b = standardAmbientCoordinates ⁻¹'
      ((D1 ×ˢ (univ : Set C)) ×ˢ AddCircle.closedIntervalArc p a b) := by
  ext x
  constructor
  · intro hx
    let xR : R := ⟨x, sourceSlab_subset (ContinuousMap.id H) a b hx⟩
    have hq := (mem_sourceSlab_iff (ContinuousMap.id H) a b xR).mp hx
    exact ⟨⟨xR.property.1, mem_univ _⟩, hq⟩
  · intro hx
    let xR : R := ⟨x, hx.1.1, mem_univ _⟩
    exact (mem_sourceSlab_iff (ContinuousMap.id H) a b xR).mpr hx.2

theorem standard_sourceSurface_eq_coordinate_preimage (theta : C) :
    sourceSurface (ContinuousMap.id H) theta = standardAmbientCoordinates ⁻¹'
      ((D1 ×ˢ (univ : Set C)) ×ˢ {theta}) := by
  ext x
  constructor
  · intro hx
    let xR : R := ⟨x, sourceSurface_subset (ContinuousMap.id H) theta hx⟩
    have hq := (mem_sourceSurface_iff (ContinuousMap.id H) theta xR).mp hx
    exact ⟨⟨xR.property.1, mem_univ _⟩, hq⟩
  · intro hx
    let xR : R := ⟨x, hx.1.1, mem_univ _⟩
    exact (mem_sourceSurface_iff (ContinuousMap.id H) theta xR).mpr hx.2



theorem frontier_standard_sourceSlab {c a b : ℝ}
    (ha : c < a) (hab : a ≤ b) (hb : b < c + p) :
    frontier (sourceSlab (ContinuousMap.id H) a b) =
      (sourceSlab (ContinuousMap.id H) a b ∩ frontier R) ∪
        (sourceSurface (ContinuousMap.id H) (a : C) ∪
          sourceSurface (ContinuousMap.id H) (b : C)) := by
  let D : Set (V1 × C) := D1 ×ˢ univ
  let arc := AddCircle.closedIntervalArc p a b
  have hD : IsClosed D := isClosed_closedBall.prod isClosed_univ
  have harc : IsClosed arc := (AddCircle.isCompact_closedIntervalArc p a b).isClosed
  rw [standard_sourceSlab_eq_coordinate_preimage, ← standardAmbientCoordinates.preimage_frontier,
    frontier_prod_eq, hD.closure_eq, harc.closure_eq,
    AddCircle.frontier_closedIntervalArc_shifted p ha hab hb,
    standard_domain_eq_coordinate_preimage, ← standardAmbientCoordinates.preimage_frontier,
    frontier_prod_univ_eq, standard_sourceSurface_eq_coordinate_preimage,
    standard_sourceSurface_eq_coordinate_preimage]
  ext x
  have hsub : (standardAmbientCoordinates x).1.1 ∈ frontier D1 →
      (standardAmbientCoordinates x).1.1 ∈ D1 := fun hx => isClosed_closedBall.frontier_subset hx
  simp only [D, arc, frontier_prod_univ_eq, mem_preimage, mem_union, mem_prod, mem_inter_iff, mem_insert_iff,
    mem_singleton_iff, mem_univ, and_true]
  tauto

end PoincareConjecture.M76.HamiltonIntervalTorus
