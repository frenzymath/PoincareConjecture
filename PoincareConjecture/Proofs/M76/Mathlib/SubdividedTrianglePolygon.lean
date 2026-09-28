import PoincareConjecture.Proofs.M76.Mathlib.PolygonSplitEdges

set_option autoImplicit false

open Set

namespace Polygon

def subdividedTriangle (n : ℕ) : Polygon (ℝ × ℝ) (n + 3) :=
  ⟨Fin.snoc (fun i : Fin (n + 2) => ((i : ℝ), 0)) (0, 1)⟩

theorem subdividedTriangle_castSucc (n : ℕ) (i : Fin (n + 2)) :
    subdividedTriangle n i.castSucc = ((i : ℝ), 0) := by
  simp [subdividedTriangle]

theorem subdividedTriangle_last (n : ℕ) :
    subdividedTriangle n (Fin.last (n + 2)) = (0, 1) := by
  simp [subdividedTriangle]

theorem injective_subdividedTriangle (n : ℕ) :
    Function.Injective (subdividedTriangle n) := by
  change Function.Injective (Fin.snoc (fun i : Fin (n + 2) => ((i : ℝ), (0 : ℝ))) (0, 1))
  apply Fin.snoc_injective_iff.mpr
  constructor
  · intro i j hij
    apply Fin.ext
    have h : (i.val : ℝ) = j.val := congrArg Prod.fst hij
    exact_mod_cast h
  · rintro ⟨i, hi⟩
    have := congrArg Prod.snd hi
    norm_num at this

theorem subdividedTriangle_edge_base (n : ℕ) (i : Fin (n + 1)) :
    (subdividedTriangle n).edgeSet ℝ i.castSucc.castSucc =
      segment ℝ ((i : ℝ), 0) ((i : ℝ) + 1, 0) := by
  have hr : finRotate (n + 3) i.castSucc.castSucc = i.castSucc.succ :=
    finRotate_of_lt (by omega)
  have hi : i.castSucc.succ = i.succ.castSucc := rfl
  simp only [edgeSet, hr, hi, subdividedTriangle_castSucc,
    Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one, affineSegment_eq_segment]

theorem subdividedTriangle_edge_slope (n : ℕ) :
    (subdividedTriangle n).edgeSet ℝ (Fin.last (n + 1)).castSucc =
      segment ℝ ((n : ℝ) + 1, 0) (0, 1) := by
  have hr : finRotate (n + 3) (Fin.last (n + 1)).castSucc = Fin.last (n + 2) := by simp
  simp only [edgeSet, hr, subdividedTriangle_castSucc, subdividedTriangle_last,
    Fin.val_last, Nat.cast_add, Nat.cast_one, affineSegment_eq_segment]

theorem subdividedTriangle_edge_last (n : ℕ) :
    (subdividedTriangle n).edgeSet ℝ (Fin.last (n + 2)) =
      segment ℝ (0, 1) (0, 0) := by
  simpa [subdividedTriangle] using
    edgeSet_snoc_last (fun i : Fin (n + 2) => ((i : ℝ), 0)) ((0, 1) : ℝ × ℝ)

private theorem horizontal_coords {a b : ℝ} (hab : a ≤ b) {x : ℝ × ℝ}
    (hx : x ∈ segment ℝ (a, 0) (b, 0)) : x.2 = 0 ∧ a ≤ x.1 ∧ x.1 ≤ b := by
  obtain ⟨hx1, hx2⟩ := Prod.segment_subset (𝕜 := ℝ) (a, 0) (b, 0) hx
  rw [segment_same] at hx2
  rw [segment_eq_Icc hab] at hx1
  exact ⟨hx2, hx1⟩

private theorem slope_coords {r : ℝ} (hr : 0 ≤ r) {x : ℝ × ℝ}
    (hx : x ∈ segment ℝ (r, 0) (0, 1)) :
    0 ≤ x.1 ∧ 0 ≤ x.2 ∧ x.1 + r * x.2 = r := by
  rcases hx with ⟨a, b, ha, hb, hab, rfl⟩
  change 0 ≤ a * r + b * 0 ∧ 0 ≤ a * 0 + b * 1 ∧
    a * r + b * 0 + r * (a * 0 + b * 1) = r
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

private theorem vertical_coords {x : ℝ × ℝ}
    (hx : x ∈ segment ℝ (0, 1) (0, 0)) : x.1 = 0 := by
  have h := (Prod.segment_subset (𝕜 := ℝ) (0, 1) (0, 0) hx).1
  simpa only [segment_same, mem_singleton_iff] using h

private theorem base_base_inter (i j : ℕ) :
    segment ℝ ((i : ℝ), (0 : ℝ)) ((i : ℝ) + 1, 0) ∩
        segment ℝ ((j : ℝ), 0) ((j : ℝ) + 1, 0) ⊆
      convexHull ℝ (({((i : ℝ), 0), ((i : ℝ) + 1, 0)} : Set (ℝ × ℝ)) ∩
        {((j : ℝ), 0), ((j : ℝ) + 1, 0)}) := by
  wlog hij : i ≤ j generalizing i j
  · simpa only [inter_comm] using this j i (le_of_not_ge hij)
  by_cases heq : i = j
  · subst j
    simp only [inter_self, convexHull_pair]
    exact Subset.rfl
  intro x hx
  obtain ⟨hy, hi, hi'⟩ := horizontal_coords (le_add_of_nonneg_right zero_le_one) hx.1
  obtain ⟨_, hj, _⟩ := horizontal_coords (le_add_of_nonneg_right zero_le_one) hx.2
  have hn : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
  have hxi : x = ((i : ℝ) + 1, 0) := Prod.ext (by linarith) hy
  have hxj : x = ((j : ℝ), 0) := Prod.ext (by linarith) hy
  exact subset_convexHull ℝ _ ⟨by simp [hxi], by simp [hxj]⟩

private theorem base_slope_inter {n : ℕ} (i : Fin (n + 1)) :
    segment ℝ ((i : ℝ), (0 : ℝ)) ((i : ℝ) + 1, 0) ∩
        segment ℝ ((n : ℝ) + 1, 0) (0, 1) ⊆
      convexHull ℝ (({((i : ℝ), 0), ((i : ℝ) + 1, 0)} : Set (ℝ × ℝ)) ∩
        {((n : ℝ) + 1, 0), (0, 1)}) := by
  intro x hx
  obtain ⟨hy, _, hi⟩ := horizontal_coords (le_add_of_nonneg_right zero_le_one) hx.1
  obtain ⟨_, _, he⟩ := slope_coords (r := (n : ℝ) + 1) (by positivity) hx.2
  have hn : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast (show i.val + 1 ≤ n + 1 by omega)
  have hxi : x = ((i : ℝ) + 1, 0) := Prod.ext (by rw [hy] at he; nlinarith) hy
  have hxn : x = ((n : ℝ) + 1, 0) := Prod.ext (by rw [hy] at he; nlinarith) hy
  exact subset_convexHull ℝ _ ⟨by simp [hxi], by simp [hxn]⟩

private theorem base_vertical_inter (i : ℕ) :
    segment ℝ ((i : ℝ), (0 : ℝ)) ((i : ℝ) + 1, 0) ∩ segment ℝ (0, 1) (0, 0) ⊆
      convexHull ℝ (({((i : ℝ), 0), ((i : ℝ) + 1, 0)} : Set (ℝ × ℝ)) ∩ {(0, 1), (0, 0)}) := by
  intro x hx
  obtain ⟨hy, hi, _⟩ := horizontal_coords (le_add_of_nonneg_right zero_le_one) hx.1
  have hx0 := vertical_coords hx.2
  have hxi : x = ((i : ℝ), 0) := Prod.ext (by have := Nat.cast_nonneg (α := ℝ) i; linarith) hy
  have hxz : x = (0, 0) := Prod.ext hx0 hy
  exact subset_convexHull ℝ _ ⟨by simp [hxi], by simp [hxz]⟩

private theorem slope_vertical_inter {r : ℝ} (hr : 0 < r) :
    segment ℝ (r, (0 : ℝ)) (0, 1) ∩ segment ℝ (0, 1) (0, 0) ⊆
      convexHull ℝ (({(r, 0), (0, 1)} : Set (ℝ × ℝ)) ∩ {(0, 1), (0, 0)}) := by
  intro x hx
  obtain ⟨_, _, he⟩ := slope_coords hr.le hx.1
  have hx0 := vertical_coords hx.2
  have hxc : x = (0, 1) := Prod.ext hx0 (by rw [hx0] at he; nlinarith)
  exact subset_convexHull ℝ _ ⟨by simp [hxc], by simp [hxc]⟩

theorem hasSimplicialEdges_subdividedTriangle (n : ℕ) :
    (subdividedTriangle n).HasSimplicialEdges := by
  intro i j
  have hbase (i : Fin (n + 1)) :
      ((subdividedTriangle n).edgeVertices i.castSucc.castSucc : Set (ℝ × ℝ)) =
        {((i : ℝ), 0), ((i : ℝ) + 1, 0)} := by
    have hr : finRotate (n + 3) i.castSucc.castSucc = i.succ.castSucc :=
      finRotate_of_lt (by omega)
    simp only [edgeVertices, Finset.coe_pair, hr, subdividedTriangle_castSucc,
      Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  have hslope :
      ((subdividedTriangle n).edgeVertices (Fin.last (n + 1)).castSucc : Set (ℝ × ℝ)) =
        {((n : ℝ) + 1, 0), (0, 1)} := by
    have hr : finRotate (n + 3) (Fin.last (n + 1)).castSucc = Fin.last (n + 2) := by simp
    simp [edgeVertices, hr, subdividedTriangle_castSucc, subdividedTriangle_last]
  have hlast :
      ((subdividedTriangle n).edgeVertices (Fin.last (n + 2)) : Set (ℝ × ℝ)) =
        {(0, 1), (0, 0)} := by
    simpa [subdividedTriangle] using
      edgeVertices_snoc_last (fun i : Fin (n + 2) => ((i : ℝ), 0)) ((0, 1) : ℝ × ℝ)
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp only [inter_self, edgeSet_eq_convexHull, subset_refl]
    | cast j =>
      induction j using Fin.lastCases with
      | last =>
        simpa only [subdividedTriangle_edge_last, subdividedTriangle_edge_slope,
          hlast, hslope, inter_comm] using slope_vertical_inter (show 0 < (n : ℝ) + 1 by positivity)
      | cast j =>
        simpa only [subdividedTriangle_edge_last, subdividedTriangle_edge_base,
          hlast, hbase, inter_comm] using base_vertical_inter j.val
  | cast i =>
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simpa only [subdividedTriangle_edge_last, subdividedTriangle_edge_slope,
          hlast, hslope] using slope_vertical_inter (show 0 < (n : ℝ) + 1 by positivity)
      | cast j =>
        induction j using Fin.lastCases with
        | last => simp only [inter_self, edgeSet_eq_convexHull, subset_refl]
        | cast j =>
          simpa only [subdividedTriangle_edge_slope, subdividedTriangle_edge_base,
            hslope, hbase, inter_comm] using base_slope_inter j
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simpa only [subdividedTriangle_edge_last, subdividedTriangle_edge_base,
          hlast, hbase] using base_vertical_inter i.val
      | cast j =>
        induction j using Fin.lastCases with
        | last =>
          simpa only [subdividedTriangle_edge_slope, subdividedTriangle_edge_base,
            hslope, hbase] using base_slope_inter i
        | cast j =>
          simpa only [subdividedTriangle_edge_base, hbase] using base_base_inter i.val j.val

end Polygon
