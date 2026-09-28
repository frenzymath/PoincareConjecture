import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphComplex
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CocyclePathIntegral
import Mathlib.Algebra.CharP.Two

set_option autoImplicit false
open Set StdSimplexCore

namespace PoincareConjecture.M76.CutGraph

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def edgeWeight (w : I → ZMod 2) : Coordinate V I → Coordinate V I → ZMod 2
  | .inr (i, a), .inr (j, b) => if i = j ∧ a ≠ b then w i else 0
  | _, _ => 0

omit [Fintype V] [Fintype I] [DecidableEq V] in
theorem edgeWeight_diagonal (w : I → ZMod 2) (j : Coordinate V I) :
    edgeWeight w j j = 0 := by
  cases j with
  | inl _ => rfl
  | inr j => simp [edgeWeight]

omit [Fintype V] [Fintype I] [DecidableEq V] in
theorem edgeWeight_symm (w : I → ZMod 2) (j k : Coordinate V I) :
    edgeWeight w j k = edgeWeight w k j := by
  cases j with
  | inl _ => cases k <;> rfl
  | inr j =>
    cases k with
    | inl _ => rfl
    | inr k =>
      by_cases h : j.1 = k.1
      · simp [edgeWeight, h, ne_comm]
      · simp [edgeWeight, h, Ne.symm h]

def weightedCocycle (ends : I → Bool → V) (w : I → ZMod 2) :
    (abstractComplex ends).toPreAbstractSimplicialComplex.ModTwoEdgeCocycle where
  value := edgeWeight w
  diagonal := edgeWeight_diagonal w
  compose := by
    intro s hs i hi j hj k hk
    by_cases hij : i = j
    · subst j
      simp [edgeWeight_diagonal]
    by_cases hjk : j = k
    · subst k
      simp [edgeWeight_diagonal]
    by_cases hik : i = k
    · subst k
      rw [edgeWeight_symm w j i, edgeWeight_diagonal]
      exact CharTwo.add_self_eq_zero _
    exact False.elim ((not_lt.mpr (abstractComplex_face_card_le ends hs))
      (Finset.two_lt_card_iff.mpr ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩))

omit [Fintype V] [Fintype I] in
theorem weightedCocycle_arm (ends : I → Bool → V) (w : I → ZMod 2) (i : I) (b : Bool) :
    (weightedCocycle ends w).value (.inl (ends i b)) (.inr (i, b)) = 0 := rfl

omit [Fintype V] [Fintype I] in
theorem weightedCocycle_bridge (ends : I → Bool → V) (w : I → ZMod 2) (i : I) :
    (weightedCocycle ends w).value (.inr (i, false)) (.inr (i, true)) = w i := by
  simp [weightedCocycle, edgeWeight]

end PoincareConjecture.M76.CutGraph

namespace PreAbstractSimplicialComplex.ModTwoEdgeCocycle

variable {J : Type*} [Fintype J] [DecidableEq J] {A : PreAbstractSimplicialComplex J}

theorem indexAt_of_vertex (c : A.ModTwoEdgeCocycle) (x : A.barycentricSpace)
    {j : J} (hx : (x : J → ℝ) = Pi.single j 1) : c.bundle.indexAt x = j := by
  have hpos : 0 < (x : J → ℝ) (c.bundle.indexAt x) := c.bundle.mem_baseSet_at x
  rw [hx] at hpos
  by_contra h
  simp [Pi.single_eq_of_ne h] at hpos

theorem pathValue_closedFace_vertices (c : A.ModTwoEdgeCocycle)
    {s : Finset J} (hs : s ∈ A.faces) {i j : J} (hi : i ∈ s) (hj : j ∈ s)
    {x y : A.barycentricSpace} (p : Path x y)
    (hx : (x : J → ℝ) = Pi.single i 1) (hy : (y : J → ℝ) = Pi.single j 1)
    (hp : ∀ t, (p t : J → ℝ) ∈ barycentricFace s) : c.pathValue p = c.value i j := by
  obtain ⟨L, hL⟩ := c.exists_closedFace_lift hs hi hj 0 p hp
  have h := c.pathValue_of_lift p L hL
  have hstart : c.sheetCoordinate ((c.bundle.localTriv i).toOpenPartialHomeomorph.symm (x, 0)) = 0 := by
    change 0 + c.value i (c.bundle.indexAt x) = 0
    rw [c.indexAt_of_vertex x hx, c.diagonal, add_zero]
  have hend : c.sheetCoordinate
      ((c.bundle.localTriv j).toOpenPartialHomeomorph.symm (y, 0 + c.value i j)) = c.value i j := by
    change (0 + c.value i j) + c.value j (c.bundle.indexAt y) = c.value i j
    rw [c.indexAt_of_vertex y hy, c.diagonal, add_zero, zero_add]
  rw [h, hend, hstart, sub_zero]

end PreAbstractSimplicialComplex.ModTwoEdgeCocycle

namespace PoincareConjecture.M76.CutGraph

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

noncomputable def complexEdgePath (ends : I → Bool → V) (i : I) :=
  (edgePath ends i).map (realizationHomeomorph ends).continuous

theorem weightedCocycle_pathValue_segment (ends : I → Bool → V) (w : I → ZMod 2)
    {s : Finset (Coordinate V I)} (hs : s ∈ (abstractComplex ends).faces)
    {j k : Coordinate V I} (hj : j ∈ s) (hk : k ∈ s)
    (a b : carrier ends) (ha : (a : Ambient V I) = Pi.single j 1)
    (hb : (b : Ambient V I) = Pi.single k 1)
    (hseg : segment ℝ (a : Ambient V I) (b : Ambient V I) ⊆ carrier ends) :
    (weightedCocycle ends w).pathValue
      ((Path.segmentIn _ a b hseg).map (realizationHomeomorph ends).continuous) =
        (weightedCocycle ends w).value j k := by
  apply (weightedCocycle ends w).pathValue_closedFace_vertices hs hj hk _ ha hb
  intro t
  change (Path.segmentIn _ a b hseg t : Ambient V I) ∈ barycentricFace s
  exact Path.segmentIn_mem_convex (convex_barycentricFace s) a b hseg
    (ha ▸ single_mem_barycentricFace hj) (hb ▸ single_mem_barycentricFace hk) t

theorem weightedCocycle_pathValue_edge (ends : I → Bool → V) (w : I → ZMod 2) (i : I) :
    (weightedCocycle ends w).pathValue (complexEdgePath ends i) = w i := by
  simp only [complexEdgePath, edgePath, Path.map_trans,
    PreAbstractSimplicialComplex.ModTwoEdgeCocycle.pathValue_trans]
  rw [weightedCocycle_pathValue_segment ends w (arm_face_mem ends i false)
      (by simp) (by simp) _ _ rfl rfl,
    weightedCocycle_pathValue_segment ends w (bridge_face_mem ends i)
      (by simp) (by simp) _ _ rfl rfl,
    weightedCocycle_pathValue_segment ends w (arm_face_mem ends i true)
      (by simp) (by simp) _ _ rfl rfl]
  simp [weightedCocycle, edgeWeight]

end PoincareConjecture.M76.CutGraph
