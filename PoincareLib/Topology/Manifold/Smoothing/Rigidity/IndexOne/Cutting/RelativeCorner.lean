import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineCornerStraightening

/-!
# Relative phase corners with both complete face labels

A normalized phase direction tangent to the old boundary constructs
the two dual affine directions required by corner straightening. The
resulting original-compatible chart retains both complete marked faces
and fixes their common rim in chart coordinates. This is the local
relative cut geometry of Waldhausen 1968, Section 1.3, pp. 59--60.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76.HamiltonIntervalTorus

/-- Straighten a phase corner in an original compatible chart. The
old normal need not already be tangent to the phase plane. -/
theorem exists_relative_phase_corner
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : ι → OpenPartialHomeomorph X E)
    (T : OpenPartialHomeomorph X E)
    (hT : ∀ i, (e i).symm.trans T ∈ piecewiseAffineGroupoid E)
    (psi ell : E →ᴬ[ℝ] ℝ) (u v : E)
    (hpu : psi.contLinear u = 1) (hlv : ell.contLinear v = 1)
    (hpv : psi.contLinear v = 0) :
    ∃ G : OpenPartialHomeomorph X E,
      G.source = T.source ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid E) ∧
      (∀ x, psi (T x) = 0 → ell (T x) = 0 → G x = T x) ∧
      (∀ x, (0 ≤ psi (T x) ∧ 0 ≤ ell (T x)) ↔ 0 ≤ psi (G x)) ∧
      (∀ x, (psi (T x) = 0 ∧ 0 ≤ ell (T x)) ↔
        psi (G x) = 0 ∧ 0 ≤ ell (G x)) ∧
      ∀ x, (ell (T x) = 0 ∧ 0 ≤ psi (T x)) ↔
        psi (G x) = 0 ∧ ell (G x) ≤ 0 := by
  let u' := u - ell.contLinear u • v
  have hpu' : psi.contLinear u' = 1 := by
    simp only [u', map_sub, map_smul, hpv, smul_zero, sub_zero, hpu]
  have hlu' : ell.contLinear u' = 0 := by
    simp only [u', map_sub, map_smul, hlv, smul_eq_mul, mul_one, sub_self]
  obtain ⟨H, hH, _, _, hfix, hquad, hold, hnew⟩ :=
    psi.exists_corner_straightening ell u' v hpu' hlu' hpv hlv
  let G := T.trans H.toOpenPartialHomeomorph
  have hGs : G.source = T.source := by
    change T.source ∩ T ⁻¹' univ = T.source
    rw [preimage_univ, inter_univ]
  refine ⟨G, hGs, ?_, fun x hx hy => hfix (T x) hx hy,
    fun x => hquad (T x), fun x => hold (T x), fun x => hnew (T x)⟩
  intro i
  simpa only [G, OpenPartialHomeomorph.trans_assoc] using
    (piecewiseAffineGroupoid E).trans (hT i) hH

end PoincareMT.M76.HamiltonIntervalTorus
