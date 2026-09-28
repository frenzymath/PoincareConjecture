import PoincareConjecture.Proofs.M76.Mathlib.FaceStarSaturation
import Mathlib.Analysis.Convex.Intrinsic

set_option autoImplicit false

open Set
open scoped Pointwise Topology

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_pos_smul_add_mem_of_intrinsicInterior {C : Set E} {p l : E}
    (hp : p ∈ intrinsicInterior ℝ C) (hl : l ∈ (affineSpan ℝ C).direction) :
    ∃ r : ℝ, 0 < r ∧ r • l + p ∈ C := by
  obtain ⟨q, hq, rfl⟩ := mem_intrinsicInterior.mp hp
  let f : ℝ → affineSpan ℝ C := fun r =>
    ⟨r • l + (q : E), (affineSpan ℝ C).vadd_mem_of_mem_direction
      ((affineSpan ℝ C).direction.smul_mem r hl) q.property⟩
  have hf : Continuous f :=
    ((continuous_id.smul continuous_const).add continuous_const).subtype_mk _
  have hzero : f 0 = q := by apply Subtype.ext; simp [f]
  have hpre : f ⁻¹' ((↑) ⁻¹' C : Set (affineSpan ℝ C)) ∈ 𝓝 (0 : ℝ) :=
    hf.continuousAt.preimage_mem_nhds (hzero ▸ mem_interior_iff_mem_nhds.mp hq)
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨r / 2, half_pos hr, hb ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hr)]
    using half_lt_self hr

theorem exists_pos_secant_of_mem_add_direction {C S : Set E} {p : E}
    (hp : p ∈ intrinsicInterior ℝ C) (hstar : ∀ q ∈ C, StarConvex ℝ q S)
    {x y : E} (hx : x ∈ S + ((affineSpan ℝ C).direction : Set E))
    (hy : y ∈ S + ((affineSpan ℝ C).direction : Set E)) :
    ∃ r : ℝ, 0 < r ∧ ∃ u ∈ S, ∃ v ∈ S, u - v = r • (x - y) := by
  obtain ⟨x, hx, l, hl, rfl⟩ := hx
  obtain ⟨y, hy, m, hm, rfl⟩ := hy
  obtain ⟨t, ht, htc⟩ := exists_pos_smul_add_mem_of_intrinsicInterior hp
    ((affineSpan ℝ C).direction.sub_mem hl hm)
  have hden : 0 < 1 + t := by linarith
  let a : ℝ := 1 / (1 + t)
  let r : ℝ := t / (1 + t)
  have ha : 0 < a := div_pos one_pos hden
  have hr : 0 < r := div_pos ht hden
  have hsum : a + r = 1 := by
    dsimp only [a, r]
    rw [← add_div, div_self hden.ne']
  have har : a * t = r := by dsimp only [a, r]; ring
  refine ⟨r, hr, a • (t • (l - m) + p) + r • x,
    hstar _ htc hx ha.le hr.le hsum, a • p + r • y,
    hstar _ (intrinsicInterior_subset hp) hy ha.le hr.le hsum, ?_⟩
  rw [smul_add, smul_smul, har]
  simp only [smul_add, smul_sub]
  abel

end Set

namespace Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsSecantTransverse.of_secant_rescaling {K : Submodule ℝ E} {S T : Set E}
    (hK : K.IsSecantTransverse S)
    (hscale : ∀ x ∈ T, ∀ y ∈ T,
      ∃ r : ℝ, 0 < r ∧ ∃ u ∈ S, ∃ v ∈ S, u - v = r • (x - y)) :
    K.IsSecantTransverse T := by
  obtain ⟨c, hc, hb⟩ := hK
  refine ⟨c, hc, fun x hx y hy => ?_⟩
  obtain ⟨r, hr, u, hu, v, hv, huv⟩ := hscale x hx y hy
  have h := hb u hu v hv
  rw [huv, map_smul, ← smul_sub, norm_smul, norm_smul, Real.norm_of_nonneg hr.le] at h
  exact (mul_le_mul_iff_right₀ hr).mp (by nlinarith only [h])

theorem isSecantTransverse_add_direction_iff (K : Submodule ℝ E) {C S : Set E} {p : E}
    (hp : p ∈ intrinsicInterior ℝ C) (hstar : ∀ q ∈ C, StarConvex ℝ q S) :
    K.IsSecantTransverse (S + ((affineSpan ℝ C).direction : Set E)) ↔
      K.IsSecantTransverse S := by
  constructor
  · intro h
    exact h.mono (fun x hx => ⟨x, hx, 0, (affineSpan ℝ C).direction.zero_mem, add_zero x⟩)
  · intro h
    exact h.of_secant_rescaling (fun _ hx _ hy =>
      Set.exists_pos_secant_of_mem_add_direction hp hstar hx hy)

theorem isSecantTransverse_closedFaceStar_tangent_iff [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (P : Submodule ℝ E) :
    P.IsSecantTransverse ((K.closedFaceStar s).space +
      ((affineSpan ℝ (s : Set E)).direction : Set E)) ↔
      P.IsSecantTransverse (K.closedFaceStar s).space := by
  have hne : (convexHull ℝ (s : Set E)).Nonempty :=
    (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces hs)).convexHull
  obtain ⟨p, hp⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _) hne
  simpa only [affineSpan_convexHull] using P.isSecantTransverse_add_direction_iff hp
    (fun _ hq => K.starConvex_closedFaceStar s hq)

end Submodule
