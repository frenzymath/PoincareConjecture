import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LiYau.DomainSupports
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff.Radial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Distance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

theorem exists_liYau_radius_error_on_domains
    {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
    {g : RiemannianMetric (m + 1) M} (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g) {κ : ℝ} (hκ : 0 ≤ κ)
    (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -(m : ℝ) * κ * g.inner x v v ≤ D.ricci x v v) :
    ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ (O : M) (R : ℝ), 0 < R → ∀ Ω : Set M, IsOpen Ω →
        {z | (g.edist O z).toReal ≤ 2 * R} ⊆ Ω → ∀ u : ℝ × M → ℝ,
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 (m + 1))) 𝓘(ℝ, ℝ) ∞ u (Ioi 0 ×ˢ Ω) →
        (∀ t, 0 < t → ∀ x ∈ Ω, 0 < u (t, x)) →
        (∀ t, 0 < t → ∀ x ∈ Ω, HasDerivAt (fun s => u (s, x))
          (D.laplacian (fun y => u (t, y)) x) t) →
        ∀ t, 0 < t → ∀ x, (g.edist O x).toReal ≤ R →
          g.inner x (D.gradient (fun y => Real.log (u (t, y))) x)
            (D.gradient (fun y => Real.log (u (t, y))) x) -
            2 * deriv (fun s => Real.log (u (s, x))) t ≤
              4 * ((m + 1 : ℕ) : ℝ) / t +
                4 * ((m + 1 : ℕ) : ℝ) * (e R + (m : ℝ) * κ) := by
  obtain ⟨χ, A, B, C, hA, hB, hC, hχ, hanti, hχ01, hone, hzero, hdA, hdB, hdC⟩ :=
    Poincare.Analysis.exists_radial_cutoff_profile
  let e := fun R : ℝ => B / R ^ 2 +
    C * (2 * (m : ℝ) / R + (m : ℝ) * Real.sqrt κ) / R +
      (((m + 1 : ℕ) : ℝ) + 2) * (A / R ^ 2)
  have hi : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have he : Tendsto e atTop (𝓝 0) := by
    simpa only [e, div_eq_mul_inv, inv_pow, mul_zero, zero_add, add_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] using
      ((tendsto_const_nhds.mul (hi.pow 2)).add
        ((tendsto_const_nhds.mul ((tendsto_const_nhds.mul hi).add
          tendsto_const_nhds)).mul hi)).add
        (tendsto_const_nhds.mul (tendsto_const_nhds.mul (hi.pow 2)))
  refine ⟨e, he, ?_⟩
  intro O R hR Ω hΩ hcontains u hu hpos hheat t ht x hx
  let : ConnectedSpace M := ⟨⟨O⟩⟩
  have hsupport := g.exists_distance_laplacian_upper_support D hm hcomplete
    (Real.sqrt_nonneg κ) (by simpa only [Real.sq_sqrt hκ] using hRic)
  have hself : g.edist O O = 0 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
  have hs := g.radial_cutoff_lower_supports_of_distance_supports D O hχ hanti hone
    hA.le hB.le hC.le (Nat.cast_nonneg m) (Real.sqrt_nonneg κ) hR hdA hdB hdC
    (fun y hy => hsupport O y (by
      intro heq; subst y; rw [hself, ENNReal.toReal_zero] at hy; linarith))
  have hηsupport : tsupport (fun y => χ ((g.edist O y).toReal / R)) ⊆
      {z | (g.edist O z).toReal ≤ 2 * R} := by
    apply closure_minimal ?_ (isClosed_le (g.continuous_toReal_edist O) continuous_const)
    intro y hy
    change χ ((g.edist O y).toReal / R) ≠ 0 at hy
    by_contra h
    apply hy
    apply hzero
    exact (le_div_iff₀ hR).mpr (le_of_lt (lt_of_not_ge h))
  have hxΩ : x ∈ Ω := hcontains (show (g.edist O x).toReal ≤ 2 * R by linarith)
  have h := D.liYau_cutoff_bound_of_lower_supports_on (by omega)
    (mul_nonneg (Nat.cast_nonneg m) hκ) (by positivity) (by positivity)
    (by simpa only [neg_mul] using hRic) hΩ hu hpos hheat
    (hχ.continuous.comp ((g.continuous_toReal_edist O).div_const R))
    (g.hasCompactSupport_radial_cutoff hcomplete O hR hzero)
    (hηsupport.trans hcontains) (fun y => hχ01 _) (fun y _ => hs y) t ht x hxΩ
  simp only [Function.comp_apply, hone _ ((div_le_one hR).mpr hx), mul_one] at h
  apply (mul_le_mul_iff_right₀ ht).mp
  have heq : t * (4 * ((m + 1 : ℕ) : ℝ) / t +
      4 * ((m + 1 : ℕ) : ℝ) * (e R + (m : ℝ) * κ)) =
      4 * ((m + 1 : ℕ) : ℝ) * (1 + (e R + (m : ℝ) * κ) * t) := by
    field_simp
  rw [heq]
  exact h

end PoincareConjecture.LeviCivitaData
