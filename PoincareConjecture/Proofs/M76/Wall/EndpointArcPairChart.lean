import PoincareConjecture.Proofs.M76.Wall.EndpointArcStraightening
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcEndpointLocalization
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_endpoint_arc_pair_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X}
    (hL : PLDomain e L) {f : ℝ → X}
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hi : InjOn f (Icc (0 : ℝ) 1)) (hfront : f 0 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ L)
    {W : Set X} (hW : IsOpen W) (hxW : f 0 ∈ W) :
    ∃ (G : OpenPartialHomeomorph X V3) (A : V3 →L[ℝ] ℝ) (v : V3),
      f 0 ∈ G.source ∧ G.source ⊆ W ∧ G (f 0) = 0 ∧ A v = 1 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ A (G y)) ∧
      (∀ y ∈ G.source, y ∈ frontier L ↔ A (G y) = 0) ∧
      ∀ y ∈ G.source,
        y ∈ f '' Icc (0 : ℝ) 1 ↔ ∃ r : ℝ, r ≤ 0 ∧ G y = r • v := by
  obtain ⟨B, A, v, hxB, hzero, hv, hcompat, hhalf, hboundary,
    m, hm, δ, hδ, hmap, hformula⟩ :=
    hL.exists_straightened_endpoint_segment hf hi hfront hproper
  have hd : m • v ≠ 0 := by
    intro h
    have hval := congrArg A h
    rw [map_smul, hv, smul_eq_mul, mul_one, map_zero] at hval
    exact hm.ne hval
  have hray (t : ℝ) (ht : t ∈ Icc 0 δ) : B (f t) = t • (m • v) := by
    rw [smul_smul]
    exact hformula t ht
  obtain ⟨U, hU, hxU, hUB, harc⟩ := B.exists_endpoint_arc_neighborhood
    hf.continuousOn hi hxB hzero hδ.1 hδ.2.le hd hmap hray hW hxW
  let G := B.restrOpen U hU
  refine ⟨G, A, v, ⟨hxB, hxU⟩, fun _ hy => (hUB hy.2).2,
    hzero, hv, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right B (hcompat i) hU
  · intro y hy
    exact hhalf y hy.1
  · intro y hy
    exact hboundary y hy.1
  · intro y hy
    change y ∈ f '' Icc (0 : ℝ) 1 ↔ ∃ r : ℝ, r ≤ 0 ∧ B y = r • v
    rw [harc y hy.2]
    constructor
    · rintro ⟨t, ht, hyt⟩
      exact ⟨t * m, mul_nonpos_of_nonneg_of_nonpos ht hm.le,
        hyt.trans (smul_smul t m v)⟩
    · rintro ⟨r, hr, hyr⟩
      refine ⟨r / m, div_nonneg_of_nonpos hr hm.le, ?_⟩
      rw [smul_smul, div_mul_cancel₀ _ hm.ne]
      exact hyr

end PoincareConjecture.M76
