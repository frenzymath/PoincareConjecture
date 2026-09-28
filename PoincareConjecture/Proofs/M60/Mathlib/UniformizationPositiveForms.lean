import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M60

theorem eventually_positive_bilinear
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {B : X → E →L[ℝ] E →L[ℝ] ℝ} {x : X}
    (hB : ContinuousAt B x) (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v) :
    ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < B y v v := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨c, hc, hbound⟩ := exists_uniform_bilinear_family_lower_bound
    (B := B) (isCompact_singleton (x := x))
    (continuousOn_singleton B x) (by simpa only [mem_singleton_iff, forall_eq] using hpos)
  have hsmall : ∀ᶠ y in 𝓝 x, ‖B y - B x‖ < c := by
    exact (hB.sub continuousAt_const).norm.eventually_lt continuousAt_const (by simpa)
  filter_upwards [hsmall] with y hy
  intro v hv
  have hnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have herr := (B y - B x).le_opNorm₂ v v
  have hneg := neg_le_abs (B y v v - B x v v)
  simp only [sub_apply, Real.norm_eq_abs] at herr
  have hstrict : ‖B y - B x‖ * ‖v‖ ^ 2 < c * ‖v‖ ^ 2 :=
    mul_lt_mul_of_pos_right hy hnorm
  have hbase := hbound x (mem_singleton x) v
  nlinarith

theorem tendsto_bilinear_of_quadratic_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A R : E →L[ℝ] E →L[ℝ] ℝ) (Q : ℕ → E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ v w, A v w = A w v) (hQ : ∀ k v w, Q k v w = Q k w v)
    {delta : ℕ → ℝ} (hdelta : Tendsto delta atTop (𝓝 0))
    (hbound : ∀ k v, A v v ≤ Q k v v ∧ Q k v v ≤ A v v + delta k * R v v)
    (v w : E) : Tendsto (fun k => Q k v w) atTop (𝓝 (A v w)) := by
  have hdiag (u : E) : Tendsto (fun k => Q k u u) atTop (𝓝 (A u u)) := by
    have hup : Tendsto (fun k => A u u + delta k * R u u) atTop (𝓝 (A u u)) := by
      simpa only [zero_mul, add_zero] using
        (show Tendsto (fun _ : ℕ => A u u) atTop (𝓝 (A u u)) from tendsto_const_nhds).add
          (hdelta.mul_const (R u u))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun k => (hbound k u).1) (fun k => (hbound k u).2)
  have hpolar (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u t, B u t = B t u) :
      (B (v + w) (v + w) - B v v - B w w) / 2 = B v w := by
    simp only [map_add, add_apply, hB w v]
    ring
  simpa only [hpolar A hA, hpolar (Q _) (hQ _)] using
    (((hdiag (v + w)).sub (hdiag v)).sub (hdiag w)).div_const 2

end PoincareConjecture.M60
