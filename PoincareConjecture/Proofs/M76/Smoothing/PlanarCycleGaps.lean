import PoincareConjecture.Proofs.M76.Mathlib.PlanarNoBacktracking
import PoincareConjecture.Proofs.M76.Mathlib.RadialEmbeddingIncidence
import PoincareConjecture.Proofs.M76.Smoothing.PlanarCircleComplex

set_option autoImplicit false

open Set NormedSpace

namespace PoincareConjecture.M76.Smoothing

variable {n : ℕ}

noncomputable def unitCycleVertex (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : Circle :=
  ⟨v.val.val i, mem_sphere_zero_iff_norm.mpr (v.property i)⟩

noncomputable def cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : ℝ :=
  Circle.shortIncrement (unitCycleVertex v i) (unitCycleVertex v (i + 1))

theorem linearIndependent_unitCycleEdge (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : LinearIndependent ℝ
      ((↑) : ↥({(unitCycleVertex v i : ℂ), (unitCycleVertex v (i + 1) : ℂ)} : Set ℂ) → ℂ) := by
  have hs : ({i, i + 1} : Finset (Fin (n + 3))) ∈ (cyclicEdgeComplex n).faces :=
    ⟨by simp, i, Finset.Subset.refl _⟩
  have h := v.val.property.linearIndependent_face_image hs
  rw [show (({i, i + 1} : Finset (Fin (n + 3))) : Set (Fin (n + 3))) =
    {i, i + 1} from Finset.coe_pair, image_pair] at h
  exact h

theorem cycleIncrement_mem_Ioo (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) : cycleIncrement v i ∈ Ioo (-Real.pi) Real.pi :=
  ⟨Circle.neg_pi_lt_shortIncrement _ _,
    Circle.shortIncrement_lt_pi (linearIndependent_unitCycleEdge v i)⟩

theorem unitCycleVertex_mem_normalize_edge_iff
    (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) (i k : Fin (n + 3)) :
    (unitCycleVertex v k : ℂ) ∈ NormedSpace.normalize ''
      segment ℝ (unitCycleVertex v i : ℂ) (unitCycleVertex v (i + 1)) ↔ k = i ∨ k = i + 1 := by
  have hs : ({i, i + 1} : Finset (Fin (n + 3))) ∈ (cyclicEdgeComplex n).faces :=
    ⟨by simp, i, Finset.Subset.refl _⟩
  have h := v.val.property.vertex_mem_normalize_face_iff hs k
  simpa only [Finset.coe_pair, image_pair, convexHull_pair, Finset.mem_insert,
    Finset.mem_singleton, normalize_eq_self_of_norm_eq_one (v.property k), unitCycleVertex] using h

private theorem cycle_add_one_ne (i : Fin (n + 3)) : i + 1 ≠ i := by
  intro h
  have hzero : (1 : Fin (n + 3)) = 0 := add_left_cancel (h.trans (add_zero i).symm)
  have hv := congrArg Fin.val hzero
  simp only [Fin.val_one, Fin.val_zero] at hv
  omega

private theorem cycle_add_two_ne (i : Fin (n + 3)) : i + 1 + 1 ≠ i := by
  intro h
  have hzero : (1 : Fin (n + 3)) + 1 = 0 := by
    apply add_left_cancel (a := i)
    simpa only [add_assoc, add_zero] using h
  have hv := congrArg Fin.val hzero
  simp only [Fin.val_add, Fin.val_one, Fin.val_zero] at hv
  rw [Nat.mod_eq_of_lt (by omega : 1 + 1 < n + 3)] at hv
  omega

theorem cycleIncrement_pos_next (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (i : Fin (n + 3)) (hi : 0 < cycleIncrement v i) : 0 < cycleIncrement v (i + 1) := by
  let a := Complex.arg (unitCycleVertex v i)
  let b := a + cycleIncrement v i
  let c := b + cycleIncrement v (i + 1)
  have hea : Circle.exp a = unitCycleVertex v i := Circle.exp_arg _
  have heb : Circle.exp b = unitCycleVertex v (i + 1) := by
    dsimp only [b]
    rw [Circle.exp_add, hea]
    exact Circle.mul_exp_shortIncrement _ _
  have hec : Circle.exp c = unitCycleVertex v (i + 1 + 1) := by
    dsimp only [c]
    rw [Circle.exp_add, heb]
    exact Circle.mul_exp_shortIncrement _ _
  have hc : (Circle.exp c : ℂ) ∉ NormedSpace.normalize ''
      segment ℝ (Circle.exp a : ℂ) (Circle.exp b) := by
    rw [hea, heb, hec, unitCycleVertex_mem_normalize_edge_iff]
    exact fun h => h.elim (cycle_add_two_ne i) (cycle_add_one_ne (i + 1))
  have ha : (Circle.exp a : ℂ) ∉ NormedSpace.normalize ''
      segment ℝ (Circle.exp b : ℂ) (Circle.exp c) := by
    rw [hea, heb, hec, unitCycleVertex_mem_normalize_edge_iff]
    exact fun h => h.elim (Ne.symm (cycle_add_one_ne i)) (Ne.symm (cycle_add_two_ne i))
  have hbc := Complex.lt_of_no_radial_backtracking
    (a := a) (b := b) (c := c) (by dsimp [b]; linarith)
    (by dsimp [b]; linarith [(cycleIncrement_mem_Ioo v i).2])
    (by dsimp [c]; linarith [(cycleIncrement_mem_Ioo v (i + 1)).1]) hc ha
  dsimp only [c] at hbc
  linarith

theorem cycleIncrement_zero (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    cycleIncrement v 0 = theta := by
  change Complex.arg ((unitCycleVertex v (0 + 1) / unitCycleVertex v 0 : Circle) : ℂ) = theta
  rw [zero_add, hzero, hone, div_one]
  exact Circle.arg_exp (by linarith [Real.pi_pos, htheta.1]) htheta.2.le

theorem cycleIncrement_pos (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    {theta : ℝ} (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta)
    (i : Fin (n + 3)) : 0 < cycleIncrement v i := by
  induction i using Fin.induction with
  | zero => rw [cycleIncrement_zero v htheta hzero hone]; exact htheta.1
  | succ i ih =>
      have h := cycleIncrement_pos_next v i.castSucc ih
      simpa only [Fin.coeSucc_eq_succ] using h

end PoincareConjecture.M76.Smoothing
