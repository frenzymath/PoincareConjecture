import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.SecantTransversality
import Mathlib.Analysis.Convex.Star

/-!
# Secants of a star and its tangent saturation

A star containing a relative neighborhood of its central face has
the same secant directions after adding the face's tangent subspace.
Consequently its geometric transverse-plane condition is unchanged.
See Cairns 1940, pp. 799--800, and M76 derivation 34.
-/

set_option autoImplicit false

open Set
open scoped Pointwise Topology

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A neighborhood of zero relative to a subspace contains a
positive multiple of every vector in that subspace.
See Cairns pp. 799--800 and M76 derivation 34. -/
theorem exists_pos_smul_mem_of_submodule_nhds (L : Submodule ℝ E) {C : Set E}
    (hC : L.subtype ⁻¹' C ∈ 𝓝 (0 : L)) {v : E} (hv : v ∈ L) :
    ∃ r : ℝ, 0 < r ∧ r • v ∈ C := by
  have hcont : Continuous (fun r : ℝ => r • (⟨v, hv⟩ : L)) :=
    continuous_id.smul continuous_const
  have hpre : {r : ℝ | r • (⟨v, hv⟩ : L) ∈ L.subtype ⁻¹' C} ∈ 𝓝 (0 : ℝ) :=
    hcont.continuousAt.preimage_mem_nhds (by simpa only [zero_smul] using hC)
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨r / 2, half_pos hr, hb ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    using half_lt_self hr

/-- Every tangent-saturated secant has a positive rescaling that is
an actual secant of the bounded star.
See Cairns Section 3(B), p. 799, Section 4(C), p. 800, and M76 derivation 34. -/
theorem exists_pos_secant_of_mem_add_submodule (L : Submodule ℝ E) {C S : Set E}
    (hzero : (0 : E) ∈ C) (hstar : ∀ p ∈ C, StarConvex ℝ p S)
    (habsorb : ∀ l ∈ L, ∃ r : ℝ, 0 < r ∧ r • l ∈ C)
    {x y : E} (hx : x ∈ S + (L : Set E)) (hy : y ∈ S + (L : Set E)) :
    ∃ r : ℝ, 0 < r ∧ ∃ u ∈ S, ∃ v ∈ S, u - v = r • (x - y) := by
  obtain ⟨x, hx, l, hl, rfl⟩ := hx
  obtain ⟨y, hy, m, hm, rfl⟩ := hy
  obtain ⟨t, ht, htc⟩ := habsorb (l - m) (L.sub_mem hl hm)
  have hden : 0 < 1 + t := by linarith
  let a : ℝ := 1 / (1 + t)
  let r : ℝ := t / (1 + t)
  have ha : 0 < a := div_pos one_pos hden
  have hr : 0 < r := div_pos ht hden
  have hsum : a + r = 1 := by
    dsimp only [a, r]
    rw [← add_div, div_self hden.ne']
  have har : a * t = r := by dsimp only [a, r]; ring
  refine ⟨r, hr, a • (t • (l - m)) + r • x,
    hstar _ htc hx ha.le hr.le hsum, a • (0 : E) + r • y,
    hstar _ hzero hy ha.le hr.le hsum, ?_⟩
  rw [smul_smul, har, smul_zero, zero_add]
  simp only [smul_add, smul_sub]
  abel

/-- Linear injectivity on the star is equivalent to injectivity on
its entire tangent saturation.
See Cairns pp. 799--800 and M76 derivation 34. -/
theorem injOn_add_submodule_iff (L : Submodule ℝ E) {C S : Set E}
    (hzero : (0 : E) ∈ C) (hstar : ∀ p ∈ C, StarConvex ℝ p S)
    (habsorb : ∀ l ∈ L, ∃ r : ℝ, 0 < r ∧ r • l ∈ C) (Q : E →L[ℝ] F) :
    InjOn Q (S + (L : Set E)) ↔ InjOn Q S := by
  constructor
  · intro h
    apply h.mono
    intro x hx
    exact ⟨x, hx, 0, L.zero_mem, add_zero x⟩
  · intro h x hx y hy he
    obtain ⟨r, hr, u, hu, v, hv, huv⟩ :=
      exists_pos_secant_of_mem_add_submodule L hzero hstar habsorb hx hy
    have hQ : Q (u - v) = 0 := by rw [huv, map_smul, map_sub, he, sub_self, smul_zero]
    have hsame : u = v := h hu hv (sub_eq_zero.mp (by simpa only [map_sub] using hQ))
    have hscaled : r • (x - y) = 0 := by rw [← huv, hsame, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hscaled).resolve_left hr.ne')

end Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The geometric secant-angle condition is unchanged by tangent
saturation of a star. The same positive constant works on both sets.
See Cairns pp. 799--800 and M76 derivation 34. -/
theorem isSecantTransverse_add_submodule_iff (K L : Submodule ℝ E) {C S : Set E}
    (hzero : (0 : E) ∈ C) (hstar : ∀ p ∈ C, StarConvex ℝ p S)
    (habsorb : ∀ l ∈ L, ∃ r : ℝ, 0 < r ∧ r • l ∈ C) :
    K.IsSecantTransverse (S + (L : Set E)) ↔ K.IsSecantTransverse S := by
  constructor
  · intro h
    exact h.mono (fun x hx => ⟨x, hx, 0, L.zero_mem, add_zero x⟩)
  · rintro ⟨c, hc, hb⟩
    refine ⟨c, hc, fun x hx y hy => ?_⟩
    obtain ⟨r, hr, u, hu, v, hv, huv⟩ :=
      Set.exists_pos_secant_of_mem_add_submodule L hzero hstar habsorb hx hy
    have h := hb u hu v hv
    rw [huv, map_smul, ← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg hr.le] at h
    have hscaled : r * (c * ‖x - y‖) ≤ r * ‖(x - y) - K.starProjection (x - y)‖ := by
      nlinarith only [h]
    exact (mul_le_mul_iff_right₀ hr).mp (by nlinarith only [hscaled])

end Submodule
