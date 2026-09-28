import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood
import Mathlib.Topology.Separation.Hausdorff












set_option autoImplicit false

open Set Geometry

namespace Set





theorem frontier_inter_eq_of_inter_eq_open
    {X : Type*} [TopologicalSpace X] {s t U : Set X}
    (hU : IsOpen U) (heq : s ∩ U = t ∩ U) :
    frontier s ∩ U = frontier t ∩ U := by
  have hclosure : closure s ∩ U = closure t ∩ U := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxU⟩
      have h := hU.closure_inter ⟨hx, hxU⟩
      rw [heq] at h
      exact ⟨closure_mono inter_subset_left h, hxU⟩
    · rintro x ⟨hx, hxU⟩
      have h := hU.closure_inter ⟨hx, hxU⟩
      rw [← heq] at h
      exact ⟨closure_mono inter_subset_left h, hxU⟩
  have hinterior : interior s ∩ U = interior t ∩ U := by
    calc
      interior s ∩ U = interior (s ∩ U) := by rw [interior_inter, hU.interior_eq]
      _ = interior (t ∩ U) := congrArg interior heq
      _ = interior t ∩ U := by rw [interior_inter, hU.interior_eq]
  apply Subset.antisymm
  · rintro x ⟨⟨hx, hxi⟩, hxU⟩
    exact ⟨⟨(hclosure.subset ⟨hx, hxU⟩).1,
      fun hi => hxi ((hinterior.symm.subset ⟨hi, hxU⟩).1)⟩, hxU⟩
  · rintro x ⟨⟨hx, hxi⟩, hxU⟩
    exact ⟨⟨(hclosure.symm.subset ⟨hx, hxU⟩).1,
      fun hi => hxi ((hinterior.subset ⟨hi, hxU⟩).1)⟩, hxU⟩

end Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem isOpen_strict_linear_halfspaces (H : Finset (E →ₗ[ℝ] ℝ)) :
    IsOpen {x : E | ∀ A ∈ H, A x < 1} := by
  simp only [ofPred_forall]
  exact isOpen_biInter_finset fun A _ =>
    isOpen_lt A.continuous_of_finiteDimensional continuous_const

private theorem mem_frontier_linear_halfspaces_of_active
    (H : Finset (E →ₗ[ℝ] ℝ)) {p : E}
    (hp : ∀ A ∈ H, A p ≤ 1) (hactive : ∃ A ∈ H, A p = 1) :
    p ∈ frontier {x : E | ∀ A ∈ H, A x ≤ 1} := by
  have hclosed : IsClosed {x : E | ∀ A ∈ H, A x ≤ 1} := by
    simp only [ofPred_forall]
    exact isClosed_biInter fun A _ =>
      isClosed_le A.continuous_of_finiteDimensional continuous_const
  refine ⟨hclosed.closure_eq.symm ▸ hp, ?_⟩
  intro hint
  obtain ⟨A, hAH, hAp⟩ := hactive
  have hAne : A ≠ 0 := by
    intro h
    rw [h, LinearMap.zero_apply] at hAp
    exact zero_ne_one hAp
  let B : E →ᵃ[ℝ] ℝ := A.toAffineMap - AffineMap.const ℝ E 1
  have hB : B.linear ≠ 0 := by simpa [B] using hAne
  have hsub : {x : E | ∀ L ∈ H, L x ≤ 1} ⊆ {x | B x ≤ 0} := by
    intro x hx
    change A x - 1 ≤ 0
    exact sub_nonpos.mpr (hx A hAH)
  have hi := interior_mono hsub hint
  rw [B.interior_nonpos hB] at hi
  change A p - 1 < 0 at hi
  rw [hAp] at hi
  linarith

open scoped Classical in
private theorem exists_open_active_halfspace_germ
    (H G : Finset (E →ₗ[ℝ] ℝ)) {p : E} {B D : Set E}
    (hpB : p ∈ interior B) (hpH : ∀ A ∈ H, A p ≤ 1)
    (hpG : ∀ A ∈ G, A p < 1)
    (hD : D = B ∩ {x | ∀ A ∈ H.filter (fun A => A p = 1) ∪ G, A x ≤ 1}) :
    ∃ U : Set E, IsOpen U ∧ p ∈ U ∧
      D ∩ U = {x | ∀ A ∈ H, A x ≤ 1} ∩ U := by
  classical
  let I := H.filter fun A => A p ≠ 1
  let U := (interior B ∩ {x | ∀ A ∈ I, A x < 1}) ∩ {x | ∀ A ∈ G, A x < 1}
  have hU : IsOpen U :=
    (isOpen_interior.inter (isOpen_strict_linear_halfspaces I)).inter
      (isOpen_strict_linear_halfspaces G)
  have hpU : p ∈ U := by
    refine ⟨⟨hpB, ?_⟩, hpG⟩
    intro A hA
    have h := Finset.mem_filter.mp hA
    exact lt_of_le_of_ne (hpH A h.1) h.2
  refine ⟨U, hU, hpU, ?_⟩
  rw [hD]
  apply Subset.antisymm
  · rintro x ⟨⟨_, hx⟩, hxU⟩
    refine ⟨?_, hxU⟩
    intro A hAH
    by_cases hAp : A p = 1
    · exact hx A (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hAH, hAp⟩))
    · exact (hxU.1.2 A (Finset.mem_filter.mpr ⟨hAH, hAp⟩)).le
  · rintro x ⟨hxH, hxU⟩
    refine ⟨⟨interior_subset hxU.1.1, ?_⟩, hxU⟩
    intro A hA
    rcases Finset.mem_union.mp hA with hAH | hAG
    · exact hxH A (Finset.mem_filter.mp hAH).1
    · exact (hxU.2 A hAG).le






theorem exists_convex_body_separated_halfspace_germs
    (H J : Finset (E →ₗ[ℝ] ℝ)) (a b : E)
    (ha : ∀ A ∈ H, A a ≤ 1) (hb : ∀ A ∈ J, A b ≤ 1)
    (hactiveA : ∃ A ∈ H, A a = 1) (hactiveB : ∃ A ∈ J, A b = 1)
    (hcrossA : ∀ A ∈ H, A a = 1 → A b < 1)
    (hcrossB : ∀ A ∈ J, A b = 1 → A a < 1) :
    ∃ (K : SimplicialComplex ℝ E) (U V : Set E),
      K.faces.Finite ∧ IsCompact K.space ∧ Convex ℝ K.space ∧
      (0 : E) ∈ interior K.space ∧ IsOpen U ∧ a ∈ U ∧
      IsOpen V ∧ b ∈ V ∧ Disjoint U V ∧
      K.space ∩ U = {x | ∀ A ∈ H, A x ≤ 1} ∩ U ∧
      K.space ∩ V = {x | ∀ A ∈ J, A x ≤ 1} ∩ V ∧
      frontier K.space ∩ U = frontier {x | ∀ A ∈ H, A x ≤ 1} ∩ U ∧
      frontier K.space ∩ V = frontier {x | ∀ A ∈ J, A x ≤ 1} ∩ V ∧
      a ∈ frontier K.space ∧ b ∈ frontier K.space := by
  classical
  let HA := H.filter fun A => A a = 1
  let JB := J.filter fun A => A b = 1
  let G := HA ∪ JB
  obtain ⟨B, hB, hBcv, hpoints⟩ :=
    ((Set.toFinite ({0, a, b} : Set E)).isCompact).exists_finite_convex_neighborhood
  let F : Finset (E →ᵃ[ℝ] ℝ) :=
    G.image fun A => A.toAffineMap - AffineMap.const ℝ E 1
  obtain ⟨K, hK, hKD⟩ := B.exists_finite_triangulation_inter_halfspaces hB F
  have hforms : {x | ∀ A ∈ F, A x ≤ 0} = {x : E | ∀ A ∈ G, A x ≤ 1} := by
    ext x
    simp only [F, mem_setOf_eq, Finset.forall_mem_image]
    change (∀ A ∈ G, A x - 1 ≤ 0) ↔ ∀ A ∈ G, A x ≤ 1
    simp only [sub_nonpos]
  rw [hforms] at hKD
  have hKcv : Convex ℝ K.space := by
    rw [hKD]
    apply hBcv.inter
    simp only [ofPred_forall]
    exact convex_iInter fun A => convex_iInter fun _ =>
      (convex_Iic (1 : ℝ)).linear_preimage A
  have h0K : (0 : E) ∈ interior K.space := by
    have hsub : interior B.space ∩ {x : E | ∀ A ∈ G, A x < 1} ⊆ K.space := by
      rw [hKD]
      exact fun x hx => ⟨interior_subset hx.1, fun A hA => (hx.2 A hA).le⟩
    apply interior_maximal hsub
      (isOpen_interior.inter (isOpen_strict_linear_halfspaces G))
    exact ⟨hpoints (by simp), fun A _ => by rw [map_zero]; exact zero_lt_one⟩
  have hJa : ∀ A ∈ JB, A a < 1 := by
    intro A hA
    exact hcrossB A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2
  have hHb : ∀ A ∈ HA, A b < 1 := by
    intro A hA
    exact hcrossA A (Finset.mem_filter.mp hA).1 (Finset.mem_filter.mp hA).2
  obtain ⟨U₀, hU₀, haU₀, heqU₀⟩ := exists_open_active_halfspace_germ H JB
    (hpoints (by simp)) ha hJa hKD
  have hKD' : K.space = B.space ∩
      {x | ∀ A ∈ J.filter (fun A => A b = 1) ∪ HA, A x ≤ 1} := by
    simpa only [G, JB, Finset.union_comm] using hKD
  obtain ⟨V₀, hV₀, hbV₀, heqV₀⟩ := exists_open_active_halfspace_germ J HA
    (hpoints (by simp)) hb hHb hKD'
  have hane : a ≠ b := by
    intro heq
    obtain ⟨A, hAH, hAa⟩ := hactiveA
    have h := hcrossA A hAH hAa
    rw [← heq, hAa] at h
    exact lt_irrefl _ h
  obtain ⟨U₁, V₁, hU₁, hV₁, haU₁, hbV₁, hdis⟩ := t2_separation hane
  let U := U₀ ∩ U₁
  let V := V₀ ∩ V₁
  have hU : IsOpen U := hU₀.inter hU₁
  have hV : IsOpen V := hV₀.inter hV₁
  have haU : a ∈ U := ⟨haU₀, haU₁⟩
  have hbV : b ∈ V := ⟨hbV₀, hbV₁⟩
  have heqU : K.space ∩ U = {x | ∀ A ∈ H, A x ≤ 1} ∩ U := by
    change K.space ∩ (U₀ ∩ U₁) = _
    rw [← inter_assoc, heqU₀, inter_assoc]
  have heqV : K.space ∩ V = {x | ∀ A ∈ J, A x ≤ 1} ∩ V := by
    change K.space ∩ (V₀ ∩ V₁) = _
    rw [← inter_assoc, heqV₀, inter_assoc]
  have hfrontU := frontier_inter_eq_of_inter_eq_open hU heqU
  have hfrontV := frontier_inter_eq_of_inter_eq_open hV heqV
  refine ⟨K, U, V, hK, K.isCompact_space_of_finite hK, hKcv, h0K,
    hU, haU, hV, hbV, hdis.mono inter_subset_right inter_subset_right,
    heqU, heqV, hfrontU, hfrontV, ?_, ?_⟩
  · exact (hfrontU.symm.subset ⟨mem_frontier_linear_halfspaces_of_active H ha hactiveA,
      haU⟩).1
  · exact (hfrontV.symm.subset ⟨mem_frontier_linear_halfspaces_of_active J hb hactiveB,
      hbV⟩).1





theorem exists_convex_body_negatively_collinear_halfspace_germs
    (H J : Finset (E →ₗ[ℝ] ℝ)) (a b : E) {r : ℝ}
    (hr : 0 < r) (hab : b = -(r • a))
    (ha : ∀ A ∈ H, A a ≤ 1) (hb : ∀ A ∈ J, A b ≤ 1)
    (hactiveA : ∃ A ∈ H, A a = 1) (hactiveB : ∃ A ∈ J, A b = 1) :
    ∃ (K : SimplicialComplex ℝ E) (U V : Set E),
      K.faces.Finite ∧ IsCompact K.space ∧ Convex ℝ K.space ∧
      (0 : E) ∈ interior K.space ∧ IsOpen U ∧ a ∈ U ∧
      IsOpen V ∧ b ∈ V ∧ Disjoint U V ∧
      K.space ∩ U = {x | ∀ A ∈ H, A x ≤ 1} ∩ U ∧
      K.space ∩ V = {x | ∀ A ∈ J, A x ≤ 1} ∩ V ∧
      frontier K.space ∩ U = frontier {x | ∀ A ∈ H, A x ≤ 1} ∩ U ∧
      frontier K.space ∩ V = frontier {x | ∀ A ∈ J, A x ≤ 1} ∩ V ∧
      a ∈ frontier K.space ∧ b ∈ frontier K.space := by
  apply exists_convex_body_separated_halfspace_germs H J a b ha hb hactiveA hactiveB
  · intro A _ hAa
    rw [hab, map_neg, map_smul, smul_eq_mul, hAa, mul_one]
    linarith
  · intro A _ hAb
    rw [hab, map_neg, map_smul, smul_eq_mul] at hAb
    by_contra h
    have hnonneg : 0 ≤ A a := zero_le_one.trans (not_lt.mp h)
    have hmul := mul_nonneg hr.le hnonneg
    linarith






theorem exists_convex_body_opposite_halfspace_germs
    (H J : Finset (E →ₗ[ℝ] ℝ)) (a : E)
    (ha : ∀ A ∈ H, A a ≤ 1) (hb : ∀ A ∈ J, A (-a) ≤ 1)
    (hactiveA : ∃ A ∈ H, A a = 1) (hactiveB : ∃ A ∈ J, A (-a) = 1) :
    ∃ (K : SimplicialComplex ℝ E) (U V : Set E),
      K.faces.Finite ∧ IsCompact K.space ∧ Convex ℝ K.space ∧
      (0 : E) ∈ interior K.space ∧ IsOpen U ∧ a ∈ U ∧
      IsOpen V ∧ -a ∈ V ∧ Disjoint U V ∧
      K.space ∩ U = {x | ∀ A ∈ H, A x ≤ 1} ∩ U ∧
      K.space ∩ V = {x | ∀ A ∈ J, A x ≤ 1} ∩ V ∧
      frontier K.space ∩ U = frontier {x | ∀ A ∈ H, A x ≤ 1} ∩ U ∧
      frontier K.space ∩ V = frontier {x | ∀ A ∈ J, A x ≤ 1} ∩ V ∧
      a ∈ frontier K.space ∧ -a ∈ frontier K.space := by
  exact exists_convex_body_negatively_collinear_halfspace_germs H J a (-a)
    zero_lt_one (by rw [one_smul]) ha hb hactiveA hactiveB

end Geometry.SimplicialComplex
