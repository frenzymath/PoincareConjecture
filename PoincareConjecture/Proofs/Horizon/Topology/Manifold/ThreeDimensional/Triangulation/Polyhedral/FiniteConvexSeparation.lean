import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith










set_option autoImplicit false

open Set
open scoped BigOperators InnerProductSpace

universe u v

namespace Poincare.Topology

theorem exists_small_convex_subset_of_zero_not_mem
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
    [FiniteDimensional Real E]
    (s : Finset E) {x : E} (hx : x ∈ convexHull Real (s : Set E))
    (hzero : (0 : E) ∉ convexHull Real (s : Set E)) :
    ∃ t : Finset E, t ⊆ s ∧ t.Nonempty ∧ t.card ≤ Module.finrank Real E ∧
      ∃ y ∈ convexHull Real (t : Set E), ‖y‖ ≤ ‖x‖ := by
  classical
  let C := convexHull Real (s : Set E)
  have hC : IsCompact C := s.finite_toSet.isCompact_convexHull Real
  obtain ⟨y, hy, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (show C.Nonempty from ⟨x, hx⟩) hC.isComplete (convex_convexHull Real _) (0 : E)
  have hyne : y ≠ 0 := by
    intro h
    exact hzero (h ▸ hy)
  have hyx : ‖y‖ ≤ ‖x‖ := by
    have hbound : BddBelow (Set.range (fun z : C => ‖(0 : E) - z‖)) :=
      ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
    have h := hmin.trans_le (ciInf_le hbound (⟨x, hx⟩ : C))
    simpa only [zero_sub, norm_neg] using h
  have hsupport (z : E) (hz : z ∈ C) : ‖y‖ ^ 2 ≤ ⟪y, z⟫_Real := by
    have h := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull Real _) hy).mp
      hmin z hz
    simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at h
    linarith
  obtain ⟨I, hI, z, w, hz, hind, hwpos, hwsum, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hy
  let := hI
  let l : E →ₗ[Real] Real := (innerSL Real y).toLinearMap
  have hly : l y = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  have hlow (i : I) : l y ≤ l (z i) := by
    rw [hly]
    exact hsupport (z i) (subset_convexHull Real _ (hz (mem_range_self i)))
  have hweighted : ∑ i, w i * l (z i) = l y := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg l hwz
  have hdeficit : ∑ i, w i * (l (z i) - l y) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hweighted, hwsum,
      one_mul, sub_self]
  have hlevel (i : I) : l (z i) = l y := by
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset I)) =>
        mul_nonneg (hwpos j).le (sub_nonneg.mpr (hlow j)))).mp hdeficit i
        (Finset.mem_univ i)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (hwpos i).ne')
  have hlyne : l y ≠ 0 := by
    rw [hly]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hyne)
  have hlinear : LinearIndependent Real z := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    have hsum : (∑ j, a j) * l y = 0 := by
      have h := congrArg l ha
      simpa only [map_sum, map_smul, smul_eq_mul, hlevel, ← Finset.sum_mul,
        map_zero] using h
    have ha0 : ∑ j, a j = 0 := (mul_eq_zero.mp hsum).resolve_right hlyne
    exact hind.eq_zero_of_sum_eq_zero ha0 ha i (Finset.mem_univ i)
  let t : Finset E := Finset.univ.image z
  have hts : t ⊆ s := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hz (mem_range_self i)
  have hyt : y ∈ convexHull Real (t : Set E) :=
    mem_convexHull_of_exists_fintype w z (fun i => (hwpos i).le) hwsum
      (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) hwz
  have htne : t.Nonempty := by
    by_contra h
    have ht : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [ht, Finset.coe_empty, convexHull_empty, mem_empty_iff_false] at hyt
  refine ⟨t, hts, htne, ?_, y, hyt, hyx⟩
  calc
    t.card = Fintype.card I := by
      rw [Finset.card_image_of_injective _ hind.injective, Finset.card_univ]
    _ ≤ Module.finrank Real E := hlinear.fintype_card_le_finrank

theorem exists_zero_of_small_affine_faces_gap
    {E : Type u} [AddCommGroup E] [Module Real E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [FiniteDimensional Real F]
    (A : E →ᵃ[Real] F) (s : Finset E) (a : Real)
    (hgap : ∀ t : Finset E, t ⊆ s → t.card ≤ Module.finrank Real F →
      ∀ x ∈ convexHull Real (t : Set E), a ≤ ‖A x‖)
    (hnear : ∃ x ∈ convexHull Real (s : Set E), ‖A x‖ < a) :
    ∃ x ∈ convexHull Real (s : Set E), A x = 0 := by
  classical
  have hzero : (0 : F) ∈ convexHull Real (↑(s.image A) : Set F) := by
    by_contra hzero
    obtain ⟨x, hx, hxa⟩ := hnear
    have hxA : A x ∈ convexHull Real (↑(s.image A) : Set F) := by
      rw [Finset.coe_image, ← A.image_convexHull]
      exact mem_image_of_mem A hx
    obtain ⟨t, hts, _htne, htcard, y, hyt, hyx⟩ :=
      exists_small_convex_subset_of_zero_not_mem (s.image A) hxA hzero
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
    have hgapz := hgap r hrs hrcard z hz
    rw [hzy] at hgapz
    exact (not_lt_of_ge hgapz) (hyx.trans_lt hxa)
  rw [Finset.coe_image, ← A.image_convexHull] at hzero
  exact hzero

end Poincare.Topology
