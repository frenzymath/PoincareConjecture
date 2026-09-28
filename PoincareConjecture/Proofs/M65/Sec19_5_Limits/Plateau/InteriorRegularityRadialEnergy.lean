import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityRadialIntegral
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityOscillation











set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M65LocalWeakMap

open M65Interior

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}




theorem energy_radial (F : M65LocalWeakMap e U) (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (x : LoopPlane) {R : ℝ} (hR : 0 < R) (hRU : closedBall x R ⊆ U) :
    AbsolutelyContinuousOnInterval
      (fun s => ∫ z in closedBall x s,
        m65EmbeddedEnergyDensity g e F.value F.derivative z) 0 R ∧
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      IntegrableOn (fun θ =>
        m65EmbeddedEnergyDensity g e F.value F.derivative (polarPlane x (r, θ)))
        (Icc (-Real.pi) Real.pi) ∧
      HasDerivAt (fun s => ∫ z in closedBall x s,
          m65EmbeddedEnergyDensity g e F.value F.derivative z)
        (r * ∫ θ in Icc (-Real.pi) Real.pi,
          m65EmbeddedEnergyDensity g e F.value F.derivative (polarPlane x (r, θ))) r := by
  obtain ⟨hac, hderiv⟩ := local_disk_radial hR
    (F.energy_integrable g he hinj hemb compact (closedBall x R)
      (isCompact_closedBall x R) hRU)
  refine ⟨hac, ?_⟩
  have hμ : volume.restrict (Ioo (-Real.pi) Real.pi) =
      volume.restrict (Icc (-Real.pi) Real.pi) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc
  filter_upwards [hderiv] with r hr
  simpa only [IntegrableOn, hμ] using hr





theorem energy_circle_oscillation (F : M65LocalWeakMap e U) (hU : IsOpen U)
    (g : RiemannianMetric 3 M) (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : LoopPlane) (ε R : ℝ), 0 < ε → ε < R →
      closedBall x R ⊆ U →
      ∀ᵐ r ∂volume.restrict (Ioo ε R),
        ∃ v : ℝ → EuclideanSpace ℝ (Fin N),
          ContinuousOn v (Icc (-Real.pi) Real.pi) ∧ v (-Real.pi) = v Real.pi ∧
          (v =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)]
            fun t => e (F.value (polarPlane x (r, t)))) ∧
          MapsTo v (Icc (-Real.pi) Real.pi) (range e) ∧
          (∀ j, AbsolutelyContinuousOnInterval (fun t => v t j) (-Real.pi) Real.pi) ∧
          (∀ s ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
            ‖v t - v s‖ ^ 2 ≤ (4 * Real.pi * r / c) *
              deriv (fun s => ∫ z in closedBall x s,
                m65EmbeddedEnergyDensity g e F.value F.derivative z) r) ∧
          ∀ s ∈ Icc (-Real.pi) Real.pi, ∀ t ∈ Icc (-Real.pi) Real.pi,
            v t - v s = ∫ θ in s..t,
              (-r * Real.sin θ) • F.derivative 0 (polarPlane x (r, θ)) +
                (r * Real.cos θ) • F.derivative 1 (polarPlane x (r, θ)) := by
  obtain ⟨c, C, hc, _, hb⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  have hclosed : IsClosed (range e) := by
    simpa only [image_univ] using (compact.image he.continuous).isClosed
  refine ⟨c, hc, fun x ε R hε hεR hRU => ?_⟩
  have hR := hε.trans hεR
  have hcircle := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self
    (F.polar_continuous_circle hU hclosed x hε hR.le hRU)
  have henergy := ae_restrict_of_ae_restrict_of_subset
    (show Ioo ε R ⊆ Ioo (0 : ℝ) R from fun _ hr => ⟨hε.trans hr.1, hr.2⟩)
    (F.energy_radial g he hinj hemb compact x hR hRU).2
  filter_upwards [hcircle, henergy] with r hcircle henergy
  obtain ⟨hm, v, hv, hp, hAE, htarget, hac, hinc⟩ := hcircle
  obtain ⟨hei, hderiv⟩ := henergy
  let d (θ : ℝ) := (-r * Real.sin θ) • F.derivative 0 (polarPlane x (r, θ)) +
    (r * Real.cos θ) • F.derivative 1 (polarPlane x (r, θ))
  let en (θ : ℝ) := m65EmbeddedEnergyDensity g e F.value F.derivative
    (polarPlane x (r, θ))
  have hbound (θ : ℝ) : (c / 2) * ‖d θ‖ ^ 2 ≤ r ^ 2 * en θ := by
    have ha := angular_field_norm_sq_le
      (F.derivative 0 (polarPlane x (r, θ))) (F.derivative 1 (polarPlane x (r, θ))) r θ
    have he' := (m65EmbeddedEnergyDensity_bounds g e hb F.value F.derivative
      (polarPlane x (r, θ))).1
    simp only [Fin.sum_univ_two] at he'
    have h1 := mul_le_mul_of_nonneg_left ha (show 0 ≤ c / 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left he' (sq_nonneg r)
    dsimp only [d, en]
    nlinarith only [h1, h2]
  have hi : (c / 2) * (∫ θ in Icc (-Real.pi) Real.pi, ‖d θ‖ ^ 2) ≤
      r ^ 2 * ∫ θ in Icc (-Real.pi) Real.pi, en θ := by
    have h := integral_mono_ae
      (hm.norm.integrable_sq.const_mul (c / 2)) (hei.const_mul (r ^ 2))
      (ae_of_all _ hbound)
    simpa only [integral_const_mul] using h
  have hj : (∫ θ in Icc (-Real.pi) Real.pi, ‖d θ‖ ^ 2) ≤
      (r ^ 2 * ∫ θ in Icc (-Real.pi) Real.pi, en θ) / (c / 2) := by
    apply (le_div_iff₀ (show 0 < c / 2 by positivity)).mpr
    simpa only [mul_comm] using hi
  refine ⟨v, hv, hp, hAE, htarget, hac, ?_, hinc⟩
  intro s hs t ht
  have hosc := interval_increment_norm_sq_le
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos]) hm hinc s hs t ht
  have hπ : Real.pi - -Real.pi = 2 * Real.pi := by ring
  rw [hπ] at hosc
  rw [hderiv.deriv]
  calc
    _ ≤ 2 * Real.pi * ∫ θ in Icc (-Real.pi) Real.pi, ‖d θ‖ ^ 2 := hosc
    _ ≤ 2 * Real.pi * ((r ^ 2 * ∫ θ in Icc (-Real.pi) Real.pi, en θ) / (c / 2)) :=
      mul_le_mul_of_nonneg_left hj (by positivity)
    _ = _ := by dsimp only [en]; field_simp; ring

end PoincareConjecture.M65LocalWeakMap
