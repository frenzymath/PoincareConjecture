import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularitySmallCircle
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityLocalGreen
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityRadialEnergy

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareConjecture.M65Interior

theorem embeddedEnergyDensity_nonneg {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ} {α : Type*}
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (q : α → M) (d : Fin 2 → α → EuclideanSpace ℝ (Fin N)) (z : α) :
    0 ≤ m65EmbeddedEnergyDensity g e q d z := by
  unfold m65EmbeddedEnergyDensity
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
    m65EmbeddingMetric_nonneg g e (q z) (d i z))

theorem localMinimum_radial_energy_inequality
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (E0 : ℝ) (hE0 : 0 ≤ E0) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ (U : Set LoopPlane) (F : M65LocalWeakMap e U), IsOpen U →
        M65LocallyMinimizesEnergy g F → ∀ (x : LoopPlane) (ε R : ℝ),
          0 < ε → ε < R → closedBall x R ⊆ U →
          (∫ z in closedBall x R, m65EmbeddedEnergyDensity g e F.value F.derivative z) ≤ E0 →
          ∀ᵐ r ∂volume.restrict (Ioo ε R),
            (∫ z in closedBall x r, m65EmbeddedEnergyDensity g e F.value F.derivative z) ≤
              K * r * deriv (fun s => ∫ z in closedBall x s,
                m65EmbeddedEnergyDensity g e F.value F.derivative z) r := by
  obtain ⟨δ, A, hδ, hA, hreplace⟩ :=
    m65Embedding_uniform_small_circle_replacement g e he hinj hemb compact
  obtain ⟨c, C, hc, _, hb⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  let a := 2 * A / c
  let b := 4 * Real.pi * E0 / (c * δ ^ 2)
  let K := 1 + a + b
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hK : 1 ≤ K := by dsimp only [K]; linarith
  have haK : a ≤ K := by dsimp only [K]; linarith
  have hbK : b ≤ K := by dsimp only [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro U F hU hmin x ε R hε hεR hRU htotal
  have hR : 0 < R := hε.trans hεR
  have hclosed : IsClosed (range e) := by
    simpa only [image_univ] using (compact.image he.continuous).isClosed
  have hcircle := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self
    (F.polar_continuous_circle hU hclosed x hε hR.le hRU)
  have hgreen := ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self
    (F.disk_green hU x hε hR.le hRU)
  have henergy := ae_restrict_of_ae_restrict_of_subset
    (show Ioo ε R ⊆ Ioo (0 : ℝ) R from fun _ hr => ⟨hε.trans hr.1, hr.2⟩)
    (F.energy_radial g he hinj hemb compact x hR hRU).2
  filter_upwards [hcircle, hgreen, henergy, ae_restrict_mem measurableSet_Ioo]
    with r hcircle hgreen henergy hrange
  have hr : 0 < r := hε.trans hrange.1
  have hDU : closedBall x r ⊆ U :=
    (closedBall_subset_closedBall hrange.2.le).trans hRU
  obtain ⟨hW, V, _, hper, htrace, htarget, hac, hinc⟩ := hcircle
  obtain ⟨hei, hderiv⟩ := henergy
  let W (θ : ℝ) := (-r * Real.sin θ) • F.derivative 0 (polarPlane x (r, θ)) +
    (r * Real.cos θ) • F.derivative 1 (polarPlane x (r, θ))
  let en := m65EmbeddedEnergyDensity g e F.value F.derivative
  let E (s : ℝ) := ∫ z in closedBall x s, en z
  have hen (z : LoopPlane) : 0 ≤ en z := embeddedEnergyDensity_nonneg g e F.value F.derivative z
  have hderiv0 : 0 ≤ deriv E r := by
    rw [hderiv.deriv]
    exact mul_nonneg hr.le (integral_nonneg (fun θ => hen (polarPlane x (r, θ))))
  have hX : 0 ≤ r * deriv E r := mul_nonneg hr.le hderiv0
  have hpoint (θ : ℝ) : (c / 2) * ‖W θ‖ ^ 2 ≤ r ^ 2 * en (polarPlane x (r, θ)) := by
    have h1 := mul_le_mul_of_nonneg_left
      (angular_field_norm_sq_le (F.derivative 0 (polarPlane x (r, θ)))
        (F.derivative 1 (polarPlane x (r, θ))) r θ)
      (show 0 ≤ c / 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left
      (m65EmbeddedEnergyDensity_bounds g e hb F.value F.derivative
        (polarPlane x (r, θ))).1 (sq_nonneg r)
    simp only [Fin.sum_univ_two] at h2
    dsimp only [W, en]
    nlinarith only [h1, h2]
  have hi : (c / 2) * (∫ θ in Icc (-Real.pi) Real.pi, ‖W θ‖ ^ 2) ≤
      r ^ 2 * ∫ θ in Icc (-Real.pi) Real.pi, en (polarPlane x (r, θ)) := by
    simpa only [integral_const_mul] using integral_mono_ae
      (hW.norm.integrable_sq.const_mul (c / 2)) (hei.const_mul (r ^ 2))
      (ae_of_all _ hpoint)
  have hangular : (∫ θ in Icc (-Real.pi) Real.pi, ‖W θ‖ ^ 2) ≤
      (2 / c) * (r * deriv E r) := by
    calc
      _ ≤ (r ^ 2 * ∫ θ in Icc (-Real.pi) Real.pi, en (polarPlane x (r, θ))) / (c / 2) := by
        apply (le_div_iff₀ (show 0 < c / 2 by positivity)).mpr
        simpa only [mul_comm] using hi
      _ = _ := by rw [hderiv.deriv]; dsimp only [en]; field_simp
  have hEr : E r ≤ E0 := by
    apply le_trans _ htotal
    exact setIntegral_mono_set
      (F.energy_integrable g he hinj hemb compact (closedBall x R)
        (isCompact_closedBall x R) hRU)
      (ae_of_all _ hen)
      (ae_of_all _ (fun _ hz => closedBall_subset_closedBall hrange.2.le hz))
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  by_cases hsmall : ∀ θ ∈ Icc (-Real.pi) Real.pi, ‖V θ - V (-Real.pi)‖ < δ
  · obtain ⟨G, hGout, hGE⟩ := hreplace U F x r hr hDU V W
      (coordinatewise_ac hac) hper htarget htrace hW hinc hsmall hgreen
    have hAE : G.value =ᵐ[volume.restrict (U \ closedBall x r)] F.value := by
      filter_upwards [ae_restrict_mem (hU.measurableSet.diff isClosed_closedBall.measurableSet)]
        with z hz
      exact (hGout z hz.2).1
    calc
      _ ≤ ∫ z in closedBall x r, m65EmbeddedEnergyDensity g e G.value G.derivative z :=
        hmin x r hr hDU G hAE
      _ ≤ A * ∫ θ in Icc (-Real.pi) Real.pi, ‖W θ‖ ^ 2 := hGE
      _ ≤ A * ((2 / c) * (r * deriv E r)) := mul_le_mul_of_nonneg_left hangular hA.le
      _ = a * (r * deriv E r) := by dsimp only [a]; ring
      _ ≤ K * r * deriv E r := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right haK hX
  · push Not at hsmall
    obtain ⟨θ, hθ, hθδ⟩ := hsmall
    have hosc := interval_increment_norm_sq_le hπ hW hinc
      (-Real.pi) ⟨le_rfl, hπ⟩ θ hθ
    have hdelta : δ ^ 2 ≤ (4 * Real.pi / c) * (r * deriv E r) := by
      calc
        _ ≤ ‖V θ - V (-Real.pi)‖ ^ 2 := pow_le_pow_left₀ hδ.le hθδ 2
        _ ≤ (Real.pi - -Real.pi) * ∫ θ in Icc (-Real.pi) Real.pi, ‖W θ‖ ^ 2 := hosc
        _ ≤ (Real.pi - -Real.pi) * ((2 / c) * (r * deriv E r)) :=
          mul_le_mul_of_nonneg_left hangular (by linarith [Real.pi_pos])
        _ = _ := by ring
    have hlarge : E0 ≤ b * (r * deriv E r) := by
      have h := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ E0 / δ ^ 2 by positivity)
      calc
        E0 = (E0 / δ ^ 2) * δ ^ 2 := by field_simp
        _ ≤ (E0 / δ ^ 2) * ((4 * Real.pi / c) * (r * deriv E r)) := h
        _ = _ := by dsimp only [b]; ring
    exact hEr.trans (hlarge.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hbK hX))

end PoincareConjecture.M65Interior
