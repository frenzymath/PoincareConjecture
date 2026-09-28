import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.Supports
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff.Radial








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData



theorem liYau_bound_of_distance_upper_supports
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [PreconnectedSpace M] {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) (hcomplete : MetricComplete g) {k m l : ℝ}
    (hk : 0 ≤ k) (hm : 0 ≤ m) (hl : 0 ≤ l)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    (hsupport : ∀ p x, p ≠ x →
      ∃ (U : Set M) (ρ : M → ℝ), IsOpen U ∧ x ∈ U ∧
        ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ ρ U ∧ ρ x = (g.edist p x).toReal ∧
        (∀ y ∈ U, (g.edist p y).toReal ≤ ρ y) ∧
        g.inner x (D.gradient ρ x) (D.gradient ρ x) = 1 ∧
        D.laplacian ρ x ≤ 2 * m / (g.edist p x).toReal + m * l)
    {u : ℝ × M → ℝ}
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ univ))
    (hpos : ∀ t, 0 < t → ∀ x, 0 < u (t, x))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => u (s, x))
      (D.laplacian (fun y => u (t, y)) x) t) {t : ℝ} (ht : 0 < t) (x : M) :
    g.inner x (D.gradient (fun y => Real.log (u (t, y))) x)
        (D.gradient (fun y => Real.log (u (t, y))) x) -
      2 * deriv (fun s => Real.log (u (s, x))) t ≤ 4 * (n : ℝ) / t + 4 * n * k := by
  obtain ⟨χ, A, B, C, hA, hB, hC, hχ, hanti, hχ01, hone, hzero, hdA, hdB, hdC⟩ :=
    Poincare.Analysis.exists_radial_cutoff_profile
  have hself (p : M) : g.edist p p = 0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
  let q := g.inner x (D.gradient (fun y => Real.log (u (t, y))) x)
      (D.gradient (fun y => Real.log (u (t, y))) x) -
    2 * deriv (fun s => Real.log (u (s, x))) t
  have hbound (R : ℝ) (hR : 0 < R) :
      t * q ≤ 4 * (n : ℝ) *
        (1 + (B / R ^ 2 + C * (2 * m / R + m * l) / R +
          ((n : ℝ) + 2) * (A / R ^ 2) + k) * t) := by
    have hs := g.radial_cutoff_lower_supports_of_distance_supports D x hχ hanti hone
      hA.le hB.le hC.le hm hl hR hdA hdB hdC (fun y hy => hsupport x y (by
        intro he; subst y; rw [hself, ENNReal.toReal_zero] at hy; linarith))
    have hb := D.liYau_cutoff_bound_of_lower_supports hn hk (by positivity)
      (by positivity) hRic hu hpos hheat
      (hχ.continuous.comp ((g.continuous_toReal_edist x).div_const R))
      (g.hasCompactSupport_radial_cutoff hcomplete x hR hzero)
      (fun y => hχ01 _) (fun y _ => hs y) t ht x
    simpa only [Function.comp_apply, hself, ENNReal.toReal_zero, zero_div,
      hone 0 (by norm_num), mul_one]
      using hb
  have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have he : Tendsto (fun R : ℝ => 4 * (n : ℝ) *
      (1 + (B / R ^ 2 + C * (2 * m / R + m * l) / R +
        ((n : ℝ) + 2) * (A / R ^ 2) + k) * t)) atTop
      (𝓝 (4 * (n : ℝ) * (1 + k * t))) := by
    simpa only [div_eq_mul_inv, inv_pow, mul_zero, zero_add, add_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.add
        (((tendsto_const_nhds.mul (hi.pow 2)).add
          ((tendsto_const_nhds.mul ((tendsto_const_nhds.mul hi).add
            tendsto_const_nhds)).mul hi)).add
          (tendsto_const_nhds.mul (tendsto_const_nhds.mul (hi.pow 2))) |>.add
          tendsto_const_nhds |>.mul tendsto_const_nhds)))
  have hlim : t * q ≤ 4 * (n : ℝ) * (1 + k * t) :=
    ge_of_tendsto he (eventually_atTop.2 ⟨1, fun R hR => hbound R (by linarith)⟩)
  change q ≤ _
  calc
    q ≤ (4 * (n : ℝ) * (1 + k * t)) / t :=
      (le_div_iff₀ ht).mpr (by simpa only [mul_comm q t] using hlim)
    _ = 4 * (n : ℝ) / t + 4 * n * k := by field_simp

end PoincareConjecture.LeviCivitaData
