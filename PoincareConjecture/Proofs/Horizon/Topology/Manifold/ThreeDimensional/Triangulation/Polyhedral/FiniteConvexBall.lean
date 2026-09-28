import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Triangulation.Polyhedral.FiniteConvexSeparation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Normed.Module.RCLike.Real










set_option autoImplicit false

open Set Metric
open scoped BigOperators InnerProductSpace

universe u v

namespace Poincare.Topology

theorem exists_small_convex_nearest_support
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    (s : Finset E) (hs : s.Nonempty) (q : E)
    (hq : q ∉ convexHull Real (s : Set E)) :
    ∃ t : Finset E, t ⊆ s ∧ t.Nonempty ∧ t.card ≤ Module.finrank Real E ∧
      ∃ y ∈ convexHull Real (t : Set E),
        ∀ z ∈ convexHull Real (s : Set E), ⟪q - y, z - y⟫_Real ≤ 0 := by
  classical
  let C := convexHull Real (s : Set E)
  have hC : IsCompact C := s.finite_toSet.isCompact_convexHull Real
  have hCne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, subset_convexHull Real _ hx⟩
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    hCne hC.isComplete (convex_convexHull Real _) q
  have hn : q - y ≠ 0 := by
    intro h
    exact hq ((sub_eq_zero.mp h).symm ▸ hy)
  have hproj : ∀ z ∈ C, ⟪q - y, z - y⟫_Real ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull Real _) hy).mp hmin
  obtain ⟨I, hI, z, w, hz, hind, hwpos, hwsum, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hy
  let := hI
  let l : E →ₗ[Real] Real := (innerSL Real (q - y)).toLinearMap
  have hlne : l ≠ 0 := by
    intro h
    have h' := LinearMap.congr_fun h (q - y)
    change ⟪q - y, q - y⟫_Real = 0 at h'
    rw [real_inner_self_eq_norm_sq] at h'
    exact (pow_ne_zero _ (norm_ne_zero_iff.mpr hn)) h'
  have hupp (i : I) : l (z i) ≤ l y := by
    have h := hproj (z i) (subset_convexHull Real _ (hz (mem_range_self i)))
    rw [inner_sub_right] at h
    exact sub_nonpos.mp h
  have hweighted : ∑ i, w i * l (z i) = l y := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg l hwz
  have hdeficit : ∑ i, w i * (l y - l (z i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hweighted, hwsum,
      one_mul, sub_self]
  have hlevel (i : I) : l (z i) = l y := by
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
        mul_nonneg (hwpos j).le (sub_nonneg.mpr (hupp j)))).mp hdeficit i
        (Finset.mem_univ i)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (hwpos i).ne')).symm
  have hspan : vectorSpan Real (Set.range z) ≤ LinearMap.ker l := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨p, ⟨i, rfl⟩, q, ⟨j, rfl⟩, rfl⟩
    change l (z i - z j) = 0
    rw [map_sub, hlevel, hlevel, sub_self]
  have hcard : Fintype.card I ≤ Module.finrank Real E := by
    have hc := hind.card_le_finrank_succ
    have hm := Submodule.finrank_mono hspan
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hlne
    omega
  let t : Finset E := Finset.univ.image z
  have hts : t ⊆ s := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hz (mem_range_self i)
  have hyt : y ∈ convexHull Real (t : Set E) :=
    mem_convexHull_of_exists_fintype w z (fun i => (hwpos i).le) hwsum
      (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hwz
  have htne : t.Nonempty := by
    by_contra h
    have ht : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [ht, Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hyt
  refine ⟨t, hts, htne, ?_, y, hyt, hproj⟩
  calc
    t.card ≤ Fintype.card I := Finset.card_image_le
    _ ≤ Module.finrank Real E := hcard

theorem closedBall_subset_convexHull_of_small_faces_gap
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    (s : Finset E) (a : Real) (ha : 0 < a)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real E →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖x‖)
    (hzero : (0 : E) ∈ convexHull Real (s : Set E)) :
    closedBall (0 : E) a ⊆ convexHull Real (s : Set E) := by
  classical
  have hs : s.Nonempty := by
    by_contra h
    have hs : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [hs, Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hzero
  have hball : ball (0 : E) a ⊆ convexHull Real (s : Set E) := by
    intro q hq
    by_contra hqout
    obtain ⟨t, hts, _, htcard, y, hyt, hproj⟩ :=
      exists_small_convex_nearest_support s hs q hqout
    have hinner : ‖y‖ ^ 2 ≤ ⟪q, y⟫_Real := by
      have h := hproj 0 hzero
      simp only [zero_sub, inner_neg_right, inner_sub_left,
        real_inner_self_eq_norm_sq] at h
      linarith
    have hnorm : ‖y‖ ≤ ‖q‖ := by
      by_cases hy0 : ‖y‖ = 0
      · rw [hy0]
        exact norm_nonneg q
      · have hypos : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
        have h := hinner.trans (real_inner_le_norm q y)
        exact (mul_le_mul_iff_left₀ hypos).mp (by simpa only [pow_two, mul_comm] using h)
    exact (not_lt_of_ge (hgap t hts htcard y hyt))
      (hnorm.trans_lt (mem_ball_zero_iff.mp hq))
  have hclosed := s.finite_toSet.isCompact_convexHull Real |>.isClosed
  rw [← closure_ball (0 : E) ha.ne']
  exact closure_minimal hball hclosed

theorem closedBall_subset_affine_convexHull_of_small_faces_gap
    {E : Type u} [AddCommGroup E] [Module Real E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    (A : E →ᵃ[Real] F) (s : Finset E) (a : Real) (ha : 0 < a)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real F →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (hzero : ∃ x ∈ convexHull Real (s : Set E), A x = 0) :
    closedBall (0 : F) a ⊆ A '' convexHull Real (s : Set E) := by
  classical
  rw [A.image_convexHull, ← Finset.coe_image]
  apply closedBall_subset_convexHull_of_small_faces_gap (s.image A) a ha
  · intro t hts htcard y hyt
    have hpre (q : t) : ∃ p ∈ s, A p = (q : F) :=
      Finset.mem_image.mp (hts q.property)
    choose p hps hpA using hpre
    let r : Finset E := Finset.univ.image p
    have hrs : r ⊆ s := by
      intro z hz
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hz
      exact hps q
    have hrcard : r.card ≤ Module.finrank Real F := by
      calc
        r.card ≤ Fintype.card t := Finset.card_image_le
        _ = t.card := Fintype.card_coe _
        _ ≤ Module.finrank Real F := htcard
    have hArt : A '' (r : Set E) = (t : Set F) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hw
        rw [hpA q]
        exact q.property
      · intro hz
        exact ⟨p ⟨z, hz⟩, Finset.mem_image.mpr ⟨⟨z, hz⟩, Finset.mem_univ _, rfl⟩,
          hpA ⟨z, hz⟩⟩
    have hyimage : y ∈ A '' convexHull Real (r : Set E) := by
      rw [A.image_convexHull, hArt]
      exact hyt
    obtain ⟨z, hz, hzy⟩ := hyimage
    rw [← hzy]
    exact hgap r hrs hrcard z hz
  · rw [Finset.coe_image, ← A.image_convexHull]
    exact hzero

end Poincare.Topology
