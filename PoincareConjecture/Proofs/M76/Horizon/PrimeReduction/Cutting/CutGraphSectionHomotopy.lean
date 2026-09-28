import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CutGraphSectionPasting
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false
open Set StdSimplexCore

namespace PoincareConjecture.M76.CutGraph

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

private theorem triple_extend_first {X : Type*} [TopologicalSpace X] {a b c d : X}
    (p : Path a b) (q : Path b c) (r : Path c d) (t : unitInterval) :
    ((p.trans q).trans r).extend ((t : ℝ) / 4) = p t := by
  rw [Path.extend_trans_of_le_half _ _ (by linarith [t.property.2]),
    Path.extend_trans_of_le_half _ _ (by linarith [t.property.2])]
  convert Path.extend_apply p t.property using 1
  congr 1
  ring

private theorem triple_extend_middle {X : Type*} [TopologicalSpace X] {a b c d : X}
    (p : Path a b) (q : Path b c) (r : Path c d) (t : unitInterval) :
    ((p.trans q).trans r).extend (1 / 4 + (t : ℝ) / 4) = q t := by
  rw [Path.extend_trans_of_le_half _ _ (by linarith [t.property.2]),
    Path.extend_trans_of_half_le _ _ (by linarith [t.property.1])]
  convert Path.extend_apply q t.property using 1
  congr 1
  ring

private theorem triple_extend_last {X : Type*} [TopologicalSpace X] {a b c d : X}
    (p : Path a b) (q : Path b c) (r : Path c d) (t : unitInterval) :
    ((p.trans q).trans r).extend (1 - (t : ℝ) / 2) = r (unitInterval.symm t) := by
  rw [Path.extend_trans_of_half_le _ _ (by linarith [t.property.2])]
  convert Path.extend_apply r (unitInterval.symm t).property using 1
  congr 1
  change 2 * (1 - (t : ℝ) / 2) - 1 = 1 - (t : ℝ)
  ring

theorem edgePath_extend_arm (ends : I → Bool → V) (i : I) (b : Bool)
    (t : unitInterval) :
    ((edgePath ends i).extend (if b then 1 - (t : ℝ) / 2 else (t : ℝ) / 4) : Ambient V I) =
      AffineMap.lineMap (vertex (ends i b)) (privateVertex i b) (t : ℝ) := by
  cases b
  · simp only [Bool.false_eq_true, if_false, edgePath, triple_extend_first,
      Path.segmentIn_apply]
  · simp only [if_true, edgePath, triple_extend_last, Path.segmentIn_apply,
      unitInterval.coe_symm_eq]
    exact AffineMap.lineMap_apply_one_sub _ _ _

theorem edgePath_extend_bridge (ends : I → Bool → V) (i : I) (t : unitInterval) :
    ((edgePath ends i).extend (1 / 4 + (t : ℝ) / 4) : Ambient V I) =
      AffineMap.lineMap (privateVertex i false) (privateVertex i true) (t : ℝ) := by
  simp only [edgePath, triple_extend_middle, Path.segmentIn_apply]

theorem face_lineMap_coordinate {J : Type*} [Fintype J] [DecidableEq J]
    {a b : J} (hab : a ≠ b) (x : barycentricFace {a, b}) :
    AffineMap.lineMap (Pi.single a 1 : J → ℝ) (Pi.single b 1 : J → ℝ)
      (faceCoordinate {a, b} b x : ℝ) = x := by
  have hx : (x : J → ℝ) ∈ AffineMap.lineMap (Pi.single a 1 : J → ℝ)
      (Pi.single b 1) '' Icc (0 : ℝ) 1 := by
    simpa only [barycentricFace_eq_convexHull, Finset.coe_pair, image_pair,
      convexHull_pair, segment_eq_image_lineMap] using x.property
  obtain ⟨t, _, ht⟩ := hx
  have hcoord : (x : J → ℝ) b = t := by
    rw [← ht]
    simp [AffineMap.lineMap_apply, Pi.single_eq_of_ne hab.symm]
  change AffineMap.lineMap _ _ ((x : J → ℝ) b) = (x : J → ℝ)
  rw [hcoord]
  exact ht

theorem edgePath_extend_arm_coordinate (ends : I → Bool → V) (i : I) (b : Bool)
    (x : arm ends i b) :
    ((edgePath ends i).extend (if b then 1 - (faceCoordinate _ (Sum.inr (i, b)) x : ℝ) / 2
      else (faceCoordinate _ (Sum.inr (i, b)) x : ℝ) / 4) : Ambient V I) = x := by
  rw [edgePath_extend_arm]
  exact face_lineMap_coordinate (Sum.inl_ne_inr) x

theorem edgePath_extend_bridge_coordinate (ends : I → Bool → V) (i : I)
    (x : (bridge i : Set (Ambient V I))) :
    ((edgePath ends i).extend (1 / 4 +
      (faceCoordinate (J := Coordinate V I) _ (Sum.inr (i, true)) x : ℝ) / 4) : Ambient V I) = x := by
  rw [edgePath_extend_bridge]
  exact face_lineMap_coordinate (by simp) x

theorem homotopic_id_of_collapsed_segments (ends : I → Bool → V)
    (g : C(carrier ends, carrier ends))
    (hgv : ∀ v (x : carrier ends), (x : Ambient V I) = vertex v →
      (g x : Ambient V I) = vertex v)
    (hga : ∀ i b (x : carrier ends), (x : Ambient V I) ∈ arm ends i b →
      (g x : Ambient V I) = vertex (ends i b))
    (hgb : ∀ i (x : carrier ends) (hx : (x : Ambient V I) ∈ bridge i),
      g x = edgePath ends i (faceCoordinate (J := Coordinate V I)
        {Sum.inr (i, false), Sum.inr (i, true)} (Sum.inr (i, true))
        ⟨(x : Ambient V I), hx⟩)) :
    g.Homotopic (ContinuousMap.id (carrier ends)) := by
  let a (v : V) : C(unitInterval, carrier ends) :=
    ContinuousMap.const _ ⟨vertex v, vertex_mem_carrier ends v⟩
  let u (i : I) (b : Bool) : C(unitInterval, carrier ends) :=
    ⟨fun t => (edgePath ends i).extend (if b then 1 - (t : ℝ) / 2 else (t : ℝ) / 4), by
      cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop⟩
  let A (i : I) (b : Bool) : Path (a (ends i b)) (u i b) := {
    toFun := fun r => ⟨fun t => (edgePath ends i).extend
      (if b then 1 - (t : ℝ) * (r : ℝ) / 2 else (t : ℝ) * (r : ℝ) / 4), by
        cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop⟩
    continuous_toFun := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      cases b <;> dsimp [Function.uncurry] <;> fun_prop
    source' := by
      apply ContinuousMap.ext
      intro t
      apply Subtype.ext
      cases b <;> simp [a]
    target' := by
      apply ContinuousMap.ext
      intro t
      simp [u] }
  let K (i : I) : Path (u i false) (u i true) := {
    toFun := fun r => ⟨fun t => (edgePath ends i).extend
      ((1 - (t : ℝ)) * (r : ℝ) + (t : ℝ) * (1 / 4 + (r : ℝ) / 4)), by fun_prop⟩
    continuous_toFun := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      dsimp [Function.uncurry]
      fun_prop
    source' := by
      apply ContinuousMap.ext
      intro t
      change (edgePath ends i).extend _ = (edgePath ends i).extend _
      congr 1
      change (1 - (t : ℝ)) * 0 + (t : ℝ) * (1 / 4 + 0 / 4) = (t : ℝ) / 4
      ring
    target' := by
      apply ContinuousMap.ext
      intro t
      change (edgePath ends i).extend _ = (edgePath ends i).extend _
      congr 1
      change (1 - (t : ℝ)) * 1 + (t : ℝ) * (1 / 4 + 1 / 4) = 1 - (t : ℝ) / 2
      ring }
  obtain ⟨G, hGv, hGa, hGb⟩ := exists_subdivided_path_map ends a u A K
  refine ⟨{
    toFun := fun z => G z.2 z.1
    continuous_toFun := G.uncurry.continuous.comp continuous_swap
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    rcases x.property with ⟨v, hv⟩ | hx
    · change G x 0 = g x
      rw [hGv v x hv.symm]
      apply Subtype.ext
      exact (hgv v x hv.symm).symm
    · obtain ⟨i, (hx | hx) | hx⟩ := mem_iUnion.mp hx
      · change G x 0 = g x
        rw [hGa i false x hx]
        apply Subtype.ext
        simpa [A, Path.extend_zero] using (hga i false x hx).symm
      · change G x 0 = g x
        rw [hGb i x hx]
        simpa [K, Path.extend_apply] using (hgb i x hx).symm
      · change G x 0 = g x
        rw [hGa i true x hx]
        apply Subtype.ext
        simpa [A, Path.extend_one] using (hga i true x hx).symm
  · intro x
    change G x 1 = x
    rcases x.property with ⟨v, hv⟩ | hx
    · rw [hGv v x hv.symm]
      apply Subtype.ext
      exact hv
    · obtain ⟨i, (hx | hx) | hx⟩ := mem_iUnion.mp hx
      · rw [hGa i false x hx]
        apply Subtype.ext
        dsimp only [A]
        convert edgePath_extend_arm_coordinate ends i false ⟨(x : Ambient V I), hx⟩ using 1
        simp [faceCoordinate]
      · rw [hGb i x hx]
        apply Subtype.ext
        dsimp only [K]
        convert edgePath_extend_bridge_coordinate ends i ⟨(x : Ambient V I), hx⟩ using 1
        simp [faceCoordinate]
      · rw [hGa i true x hx]
        apply Subtype.ext
        dsimp only [A]
        convert edgePath_extend_arm_coordinate ends i true ⟨(x : Ambient V I), hx⟩ using 1
        simp [faceCoordinate]

end PoincareConjecture.M76.CutGraph
