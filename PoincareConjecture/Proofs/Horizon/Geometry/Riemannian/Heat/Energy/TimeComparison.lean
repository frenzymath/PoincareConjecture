import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.TimeIntegral










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}


theorem integrated_weighted_subsolution_cutoff_estimate (D : LeviCivitaData g)
    {u ξ : ℝ × M → ℝ} {a b : ℝ} (hab : a ≤ b)
    {U : Set ℝ} (hU : IsOpen U) (hUab : Ioo a b ⊆ U)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (U ×ˢ univ))
    (hξ : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ ξ (U ×ˢ univ))
    (huc : ContinuousOn u (Icc a b ×ˢ univ))
    (hξc : ContinuousOn ξ (Icc a b ×ˢ univ))
    (hu0 : ∀ t ∈ Ioo a b, ∀ x, 0 ≤ u (t, x))
    (hsub : ∀ t ∈ Ioo a b, ∀ x,
      deriv (fun s ↦ u (s, x)) t ≤ D.laplacian (fun y ↦ u (t, y)) x)
    (hweight : ∀ t ∈ Ioo a b, ∀ x, deriv (fun s ↦ ξ (s, x)) t +
      g.inner x (D.gradient (fun y ↦ ξ (t, y)) x)
        (D.gradient (fun y ↦ ξ (t, y)) x) ≤ 0)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) :
    (∫ x, η x ^ 2 * Real.exp (ξ (b, x)) * u (b, x) ^ 2 ∂g.volumeMeasure) ≤
      (∫ x, η x ^ 2 * Real.exp (ξ (a, x)) * u (a, x) ^ 2 ∂g.volumeMeasure) +
      4 * ∫ t in a..b, ∫ x, Real.exp (ξ (t, x)) * u (t, x) ^ 2 *
        g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure := by
  let E : ℝ → ℝ := fun t ↦ ∫ x, η x ^ 2 * Real.exp (ξ (t, x)) * u (t, x) ^ 2
    ∂g.volumeMeasure
  let W : ℝ → ℝ := fun t ↦ ∫ x, Real.exp (ξ (t, x)) * u (t, x) ^ 2 *
    g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure
  let E' : ℝ → ℝ := fun t ↦ ∫ x, η x ^ 2 * Real.exp (ξ (t, x)) *
    (2 * u (t, x) * deriv (fun s ↦ u (s, x)) t +
      u (t, x) ^ 2 * deriv (fun s ↦ ξ (s, x)) t) ∂g.volumeMeasure
  have hug (t : ℝ) (ht : t ∈ U) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ u (t, x) :=
    hu.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hξg (t : ℝ) (ht : t ∈ U) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ ξ (t, x) :=
    hξ.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hEc : ContinuousOn E (Icc a b) := by
    apply continuousOn_integral_of_compact_support hηc.isCompact
    · exact (((hη.continuous.comp continuous_snd).pow 2).continuousOn.mul
        (Real.continuous_exp.comp_continuousOn hξc)).mul (huc.pow 2)
    · intro t x _ hx
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hWc : ContinuousOn W (Icc a b) := by
    apply continuousOn_integral_of_compact_support hηc.isCompact
    · exact ((Real.continuous_exp.comp_continuousOn hξc).mul (huc.pow 2)).mul
        ((D.continuous_inner_gradient hη hη).comp continuous_snd).continuousOn
    · intro t x _ hx
      simp [D.gradient_eq_zero_of_notMem_tsupport hx]
  have hdc : ContinuousOn (fun p : ℝ × M ↦ η p.2 ^ 2 * Real.exp (ξ p) *
      (2 * u p * deriv (fun s ↦ u (s, p.2)) p.1 +
        u p ^ 2 * deriv (fun s ↦ ξ (s, p.2)) p.1)) (U ×ˢ univ) := by
    intro p hp
    exact (((((hη.continuous.continuousAt.comp continuousAt_snd).pow 2).mul
      (Real.continuous_exp.continuousAt.comp (hξg p.1 hp.1 p.2).continuousAt))).mul
        ((((hug p.1 hp.1 p.2).continuousAt.const_mul 2).mul
          (Poincare.Manifold.contMDiffAt_deriv_time (hug p.1 hp.1 p.2)).continuousAt).add
        (((hug p.1 hp.1 p.2).continuousAt.pow 2).mul
          (Poincare.Manifold.contMDiffAt_deriv_time (hξg p.1 hp.1 p.2)).continuousAt))).continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ U) : HasDerivAt E (E' t) t := by
    apply Poincare.Parabolic.hasDerivAt_integral_compact_support hU
      (F := fun t x ↦ η x ^ 2 * Real.exp (ξ (t, x)) * u (t, x) ^ 2)
      (G := fun t x ↦ η x ^ 2 * Real.exp (ξ (t, x)) *
        (2 * u (t, x) * deriv (fun s ↦ u (s, x)) t +
          u (t, x) ^ 2 * deriv (fun s ↦ ξ (s, x)) t))
      ?_ hdc hηc.isCompact ?_ ?_ ?_ ht
    · exact (((hη.continuous.comp continuous_snd).pow 2).continuousOn.mul
        (Real.continuous_exp.comp_continuousOn hξ.continuousOn)).mul (hu.continuousOn.pow 2)
    · intro t ht x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
    · intro t ht x hx
      simp [image_eq_zero_of_notMem_tsupport hx]
    · intro t ht x
      have hu' := ((hug t ht x).comp t (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt.differentiableAt (by simp)
      have hξ' := ((hξg t ht x).comp t (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt.differentiableAt (by simp)
      convert! ((hξ'.hasDerivAt.exp.const_mul (η x ^ 2)).mul (hu'.hasDerivAt.pow 2)) using 1
      simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 by rfl, pow_one,
        Function.comp_def, id_eq, Pi.pow_apply]
      ring
  have hi := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hEc
    (fun t ht ↦ (hd t (hUab ht)).hasDerivWithinAt)
    ((hWc.const_mul 4).integrableOn_Icc) (fun t ht ↦ ?_)
  · rw [intervalIntegral.integral_const_mul] at hi
    change E b ≤ E a + 4 * ∫ t in a..b, W t
    linarith
  · exact D.weighted_subsolution_spatial_cutoff_estimate hη hηc
      (fun x ↦ (hug t (hUab ht) x).comp x (contMDiffAt_const.prodMk contMDiffAt_id))
      (fun x ↦ (hξg t (hUab ht) x).comp x (contMDiffAt_const.prodMk contMDiffAt_id))
      (continuous_iff_continuousAt.mpr (fun x ↦
        (Poincare.Manifold.contMDiffAt_deriv_time (hug t (hUab ht) x)).continuousAt.comp
          (continuousAt_const.prodMk continuousAt_id)))
      (continuous_iff_continuousAt.mpr (fun x ↦
        (Poincare.Manifold.contMDiffAt_deriv_time (hξg t (hUab ht) x)).continuousAt.comp
          (continuousAt_const.prodMk continuousAt_id)))
      (hu0 t ht) (hsub t ht) (hweight t ht)

end PoincareConjecture.LeviCivitaData
