import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem triangle_eq_simplex_image (a b c : E) :
    convexHull ℝ {a, b, c} =
      (fun w : Fin 3 → ℝ => w 0 • a + w 1 • b + w 2 • c) ''
        stdSimplex ℝ (Fin 3) := by
  let L : (Fin 3 → ℝ) →ₗ[ℝ] E :=
    (LinearMap.proj 0).smulRight a + (LinearMap.proj 1).smulRight b +
      (LinearMap.proj 2).smulRight c
  apply subset_antisymm
  · apply convexHull_min
    · rintro x (rfl | rfl | rfl)
      · exact ⟨Pi.single 0 1, single_mem_stdSimplex ℝ 0, by simp⟩
      · exact ⟨Pi.single 1 1, single_mem_stdSimplex ℝ 1, by simp⟩
      · exact ⟨Pi.single 2 1, single_mem_stdSimplex ℝ 2, by simp⟩
    · exact (convex_stdSimplex ℝ (Fin 3)).linear_image L
  · rintro x ⟨w, hw, rfl⟩
    refine mem_convexHull_of_exists_fintype w ![a, b, c] hw.1 hw.2 ?_ ?_
    · intro i
      fin_cases i <;> simp
    · simp [Fin.sum_univ_three]

variable {Z : Type*} [TopologicalSpace Z] {z0 : Z}

theorem eventually_disjoint_triangle_segment {a b c d e : Z → E}
    (ha : ContinuousAt a z0) (hb : ContinuousAt b z0) (hc : ContinuousAt c z0)
    (hd : ContinuousAt d z0) (he : ContinuousAt e z0)
    (hdis : Disjoint (convexHull ℝ {a z0, b z0, c z0}) (segment ℝ (d z0) (e z0))) :
    ∀ᶠ z in 𝓝 z0, Disjoint (convexHull ℝ {a z, b z, c z}) (segment ℝ (d z) (e z)) := by
  let K := stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1
  let D : Z → ((Fin 3 → ℝ) × ℝ) → E := fun z q =>
    q.1 0 • a z + q.1 1 • b z + q.1 2 • c z - AffineMap.lineMap (d z) (e z) q.2
  have hK : IsCompact K := (isCompact_stdSimplex ℝ (Fin 3)).prod isCompact_Icc
  have hne : ∀ᶠ z in 𝓝 z0, ∀ q ∈ K, D z q ≠ 0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro q hq
    have hcont : ContinuousAt (fun v : Z × ((Fin 3 → ℝ) × ℝ) => D v.1 v.2) (z0, q) := by
      have hw (i : Fin 3) :
          ContinuousAt (fun v : Z × ((Fin 3 → ℝ) × ℝ) => v.2.1 i) (z0, q) :=
        (continuous_apply i).continuousAt.comp (continuousAt_fst.comp continuousAt_snd)
      exact (((hw 0).smul (ha.comp continuousAt_fst)).add
        ((hw 1).smul (hb.comp continuousAt_fst))).add
          ((hw 2).smul (hc.comp continuousAt_fst)) |>.sub
            ((hd.comp continuousAt_fst).lineMap (he.comp continuousAt_fst)
              (continuousAt_snd.comp continuousAt_snd))
    apply hcont.eventually_ne
    intro hzero
    have hT : q.1 0 • a z0 + q.1 1 • b z0 + q.1 2 • c z0 ∈
        convexHull ℝ {a z0, b z0, c z0} := by
      rw [triangle_eq_simplex_image]
      exact ⟨q.1, hq.1, rfl⟩
    have heq : q.1 0 • a z0 + q.1 1 • b z0 + q.1 2 • c z0 =
        AffineMap.lineMap (d z0) (e z0) q.2 := sub_eq_zero.mp hzero
    exact Set.disjoint_left.mp hdis hT (heq.symm ▸ lineMap_mem_segment ℝ _ _ hq.2)
  filter_upwards [hne] with z hz
  apply Set.disjoint_left.mpr
  intro x hxT hxS
  rw [triangle_eq_simplex_image] at hxT
  obtain ⟨w, hw, hwx⟩ := hxT
  dsimp only at hwx
  rw [segment_eq_image_lineMap] at hxS
  obtain ⟨t, ht, htx⟩ := hxS
  apply hz (w, t) ⟨hw, ht⟩
  change w 0 • a z + w 1 • b z + w 2 • c z - AffineMap.lineMap (d z) (e z) t = 0
  rw [hwx, htx, sub_self]

private theorem pointed_triangle_relation_ne_zero (a b c d : E)
    (ha : a ∉ segment ℝ b c) (had : a ≠ d)
    (hinter : convexHull ℝ {a, b, c} ∩ segment ℝ a d ⊆ {a})
    (w : Fin 3 → ℝ) (hw : w ∈ stdSimplex ℝ (Fin 3)) :
    w 0 • (b - a) + w 1 • (c - a) - w 2 • (d - a) ≠ 0 := by
  intro hzero
  have hsum : w 0 + w 1 + w 2 = 1 := by simpa only [Fin.sum_univ_three] using hw.2
  let x := a + w 0 • (b - a) + w 1 • (c - a)
  have hx : x = w 2 • a + w 0 • b + w 1 • c := by
    rw [show w 2 = 1 - w 0 - w 1 by linarith]
    dsimp [x]
    module
  have hx' : x = a + w 2 • (d - a) := by
    calc
      x = a + (w 0 • (b - a) + w 1 • (c - a)) := by dsimp [x]; abel
      _ = a + w 2 • (d - a) := by rw [sub_eq_zero.mp hzero]
  have hxT : x ∈ convexHull ℝ {a, b, c} := by
    rw [triangle_eq_simplex_image]
    refine ⟨![w 2, w 0, w 1], ⟨?_, ?_⟩, ?_⟩
    · intro i
      fin_cases i
      · exact hw.1 2
      · exact hw.1 0
      · exact hw.1 1
    · simp only [Fin.sum_univ_three]
      change w 2 + w 0 + w 1 = 1
      linarith
    · exact hx.symm
  have hxS : x ∈ segment ℝ a d := by
    refine ⟨1 - w 2, w 2, sub_nonneg.mpr (mem_Icc_of_mem_stdSimplex hw 2).2,
      hw.1 2, by ring, ?_⟩
    rw [hx']
    module
  have hxa : x = a := hinter ⟨hxT, hxS⟩
  have hz : w 2 • (d - a) = 0 := by
    have hh := hx'.symm.trans hxa
    exact add_eq_left.mp hh
  have hw2 : w 2 = 0 := (smul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr had.symm)
  apply ha
  refine ⟨w 0, w 1, hw.1 0, hw.1 1, by linarith, ?_⟩
  simpa only [hw2, zero_smul, zero_add, hxa] using hx.symm

theorem eventually_triangle_inter_attached_segment_subset {a b c d : Z → E}
    (ha : ContinuousAt a z0) (hb : ContinuousAt b z0)
    (hc : ContinuousAt c z0) (hd : ContinuousAt d z0)
    (hpoint : a z0 ∉ segment ℝ (b z0) (c z0)) (had : a z0 ≠ d z0)
    (hinter : convexHull ℝ {a z0, b z0, c z0} ∩ segment ℝ (a z0) (d z0) ⊆ {a z0}) :
    ∀ᶠ z in 𝓝 z0, convexHull ℝ {a z, b z, c z} ∩ segment ℝ (a z) (d z) ⊆ {a z} := by
  let R : Z → (Fin 3 → ℝ) → E := fun z w =>
    w 0 • (b z - a z) + w 1 • (c z - a z) - w 2 • (d z - a z)
  have hne : ∀ᶠ z in 𝓝 z0, ∀ w ∈ stdSimplex ℝ (Fin 3), R z w ≠ 0 := by
    apply (isCompact_stdSimplex ℝ (Fin 3)).eventually_forall_of_forall_eventually
    intro w hw
    have hcont : ContinuousAt (fun v : Z × (Fin 3 → ℝ) => R v.1 v.2) (z0, w) := by
      have hwc (i : Fin 3) : ContinuousAt (fun v : Z × (Fin 3 → ℝ) => v.2 i) (z0, w) :=
        (continuous_apply i).continuousAt.comp continuousAt_snd
      have hac := ha.comp (continuousAt_fst (p := (z0, w)))
      exact (((hwc 0).smul ((hb.comp continuousAt_fst).sub hac)).add
        ((hwc 1).smul ((hc.comp continuousAt_fst).sub hac))).sub
          ((hwc 2).smul ((hd.comp continuousAt_fst).sub hac))
    exact hcont.eventually_ne
      (pointed_triangle_relation_ne_zero _ _ _ _ hpoint had hinter w hw)
  filter_upwards [hne] with z hz
  intro x hx
  by_contra hxa
  have hxa' : x ≠ a z := hxa
  have hxT := hx.1
  rw [triangle_eq_simplex_image] at hxT
  obtain ⟨v, hv, hvx⟩ := hxT
  dsimp only at hvx
  have hxS := hx.2
  rw [segment_eq_image_lineMap] at hxS
  obtain ⟨t, ht, htx⟩ := hxS
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    apply hxa'
    rw [← htx, ← heq]
    simp)
  let s := v 1 + v 2 + t
  have hs : 0 < s := add_pos_of_nonneg_of_pos (add_nonneg (hv.1 1) (hv.1 2)) htpos
  let w : Fin 3 → ℝ := ![v 1 / s, v 2 / s, t / s]
  have hw : w ∈ stdSimplex ℝ (Fin 3) := by
    constructor
    · intro i
      fin_cases i
      · exact div_nonneg (hv.1 1) hs.le
      · exact div_nonneg (hv.1 2) hs.le
      · exact div_nonneg ht.1 hs.le
    · simp only [Fin.sum_univ_three]
      change v 1 / s + v 2 / s + t / s = 1
      rw [← add_div, ← add_div]
      exact div_self hs.ne'
  have hsum : v 0 + v 1 + v 2 = 1 := by simpa only [Fin.sum_univ_three] using hv.2
  have hrel : v 1 • (b z - a z) + v 2 • (c z - a z) - t • (d z - a z) = 0 := by
    have heq := hvx.trans htx.symm
    rw [AffineMap.lineMap_apply_module] at heq
    rw [show v 0 = 1 - v 1 - v 2 by linarith] at heq
    calc
      _ = ((1 - v 1 - v 2) • a z + v 1 • b z + v 2 • c z) -
          ((1 - t) • a z + t • d z) := by module
      _ = 0 := sub_eq_zero.mpr heq
  apply hz w hw
  change (v 1 / s) • (b z - a z) + (v 2 / s) • (c z - a z) -
    (t / s) • (d z - a z) = 0
  rw [div_eq_inv_mul, div_eq_inv_mul, div_eq_inv_mul, mul_smul, mul_smul, mul_smul,
    ← smul_add, ← smul_sub, hrel, smul_zero]

end PoincareConjecture.M25.Topology3D
