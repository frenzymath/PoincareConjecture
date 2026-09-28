import PoincareConjecture.Proofs.M76.Mathlib.MaximalFaceAffineGerm
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialStar
import PoincareConjecture.Proofs.M76.Mathlib.ConeSimplex












set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]





theorem zero_mem_and_mem_intrinsicInterior_of_radial_closedStar
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ t ∈ K.faces, s ⊆ t → t = s)
    {a p : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hp : p ∈ (K.closedStar 0).space) (hplink : p ∉ (K.link 0).space)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (har : a = r • p) :
    (0 : E) ∈ s ∧ p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  obtain ⟨t, ht, hpt⟩ := mem_space_iff.mp hp
  have hat : a ∈ convexHull ℝ ((insert (0 : E) t : Finset E) : Set E) := by
    rw [har, Finset.coe_insert]
    exact smul_mem_convexHull_insert_zero hpt hr
  have hts : insert (0 : E) t = s :=
    hmax _ ht.2 (K.subset_of_mem_intrinsicInterior_face hs ht.2 ha hat)
  have hzero : (0 : E) ∈ s := hts ▸ Finset.mem_insert_self (0 : E) t
  have hps : p ∈ convexHull ℝ (s : Set E) := by
    rw [← hts]
    exact convexHull_mono (show (t : Set E) ⊆ (insert (0 : E) t : Finset E) from
      fun _ hx => Finset.mem_insert_of_mem hx) hpt
  refine ⟨hzero, ?_⟩
  by_contra hnot
  have hpfront : p ∈ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hps, hnot⟩
  obtain ⟨u, hu, hproper, hpu⟩ := K.exists_properFace_of_mem_intrinsicFrontier hs hpfront
  obtain ⟨hus, hune⟩ := Finset.ssubset_iff_subset_ne.mp hproper
  have hius : insert (0 : E) u ⊆ s := Finset.insert_subset_iff.mpr ⟨hzero, hus⟩
  have hiu : insert (0 : E) u ∈ K.faces :=
    K.down_closed hs hius (Finset.insert_nonempty (0 : E) u)
  have hau : a ∈ convexHull ℝ ((insert (0 : E) u : Finset E) : Set E) := by
    rw [har, Finset.coe_insert]
    exact smul_mem_convexHull_insert_zero hpu hr
  have hiueq : insert (0 : E) u = s :=
    hmax _ hiu (K.subset_of_mem_intrinsicInterior_face hs hiu ha hau)
  have hzerou : (0 : E) ∉ u := by
    intro h0u
    exact hune ((Finset.insert_eq_of_mem h0u).symm.trans hiueq)
  exact hplink (mem_space_iff.mpr ⟨u, ⟨hu, hzerou, hiu⟩, hpu⟩)






theorem zero_mem_and_mem_triangle_interior_of_radial_frontier
    (K : SimplicialComplex ℝ E)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {a p : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {C : Set E} (hC : IsClosed C) (hlink : Disjoint C (K.link 0).space)
    (hpC : p ∈ frontier C) (hpstar : p ∈ (K.closedStar 0).space)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (hpa : p = ρ • a) :
    (0 : E) ∈ s ∧ p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  have hρpos : 0 < ρ := zero_lt_one.trans_le hρ
  have hmax : ∀ t ∈ K.faces, s ⊆ t → t = s := by
    intro t ht hst
    exact (Finset.eq_of_subset_of_card_le hst
      (by simpa only [hcard] using hbound t ht)).symm
  have har : a = ρ⁻¹ • p := by rw [hpa, inv_smul_smul₀ hρpos.ne']
  exact K.zero_mem_and_mem_intrinsicInterior_of_radial_closedStar hs hmax ha hpstar
    (fun hpL => disjoint_left.mp hlink (hC.frontier_subset hpC) hpL)
    (show ρ⁻¹ ∈ Icc (0 : ℝ) 1 from
      ⟨inv_nonneg.mpr hρpos.le, (inv_le_one₀ hρpos).mpr hρ⟩) har




theorem exists_open_eq_triangle_plane_at_radial_frontier
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {a p : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    {C : Set E} (hC : IsClosed C) (hlink : Disjoint C (K.link 0).space)
    (hpC : p ∈ frontier C) (hpstar : p ∈ (K.closedStar 0).space)
    {ρ : ℝ} (hρ : 1 ≤ ρ) (hpa : p = ρ • a) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      K.space ∩ U = (affineSpan ℝ (s : Set E) : Set E) ∩ U := by
  have hp := K.zero_mem_and_mem_triangle_interior_of_radial_frontier
    hbound hs hcard ha hC hlink hpC hpstar hρ hpa
  exact K.exists_open_eq_affineSpan_of_triangle_interior hK hbound hs hcard hp.2

end Geometry.SimplicialComplex
