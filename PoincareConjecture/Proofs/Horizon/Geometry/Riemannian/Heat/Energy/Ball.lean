import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.SpaceTime









set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

omit [PreconnectedSpace M] in
private lemma integral_le_of_support_bound {f : M → ℝ} {S : Set M}
    (hS : g.volumeMeasure S < ⊤) {B : ℝ}
    (hB : ∀ x ∈ S, ‖f x‖ ≤ B) (hout : ∀ x ∉ S, f x = 0) :
    (∫ x, f x ∂g.volumeMeasure) ≤ B * (g.volumeMeasure S).toReal := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  exact (le_abs_self _).trans (norm_setIntegral_le_of_norm_le_const hS hB)



theorem integrated_heat_energy_cutoff_bound (D : LeviCivitaData g)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hFc : ContinuousOn F (Ici 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    (hηc : HasCompactSupport η) (hηrange : ∀ x, η x ∈ Icc 0 1)
    {S : Set M} (hS : g.volumeMeasure S < ⊤) (hηS : tsupport η ⊆ S)
    {L B b : ℝ} (hB : 0 ≤ B) (hb : 0 < b)
    (hgrad : ∀ x, g.inner x (D.gradient η x) (D.gradient η x) ≤ L)
    (hbound : ∀ t ∈ Icc 0 b, ∀ x ∈ S, |F (t, x)| ≤ B) :
    (∫ t in 0..b, ∫ x, η x ^ 2 * g.inner x
      (D.gradient (fun y ↦ F (t, y)) x) (D.gradient (fun y ↦ F (t, y)) x)
      ∂g.volumeMeasure) ≤ B ^ 2 * (1 + 4 * b * L) * (g.volumeMeasure S).toReal := by
  let W : ℝ → ℝ := fun t ↦ ∫ x, F (t, x) ^ 2 *
    g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure
  have hinner0 (x : M) : 0 ≤ g.inner x (D.gradient η x) (D.gradient η x) := by
    by_cases h : D.gradient η x = 0
    · simp [h]
    · exact (g.pos x _ h).le
  have hsq (t : ℝ) (ht : t ∈ Icc 0 b) (x : M) (hx : x ∈ S) :
      F (t, x) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hbound t ht x hx)
  have hE : (∫ x, η x ^ 2 * F (0, x) ^ 2 ∂g.volumeMeasure) ≤
      B ^ 2 * (g.volumeMeasure S).toReal := by
    apply integral_le_of_support_bound hS
    · intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hηsq : η x ^ 2 ≤ 1 := by nlinarith [(hηrange x).1, (hηrange x).2]
      exact (mul_le_mul_of_nonneg_right hηsq (sq_nonneg _)).trans
        (by simpa using hsq 0 ⟨le_rfl, hb.le⟩ x hx)
    · intro x hx
      have hxs : x ∉ tsupport η := fun h ↦ hx (hηS h)
      simp [image_eq_zero_of_notMem_tsupport hxs]
  have hW (t : ℝ) (ht : t ∈ Icc 0 b) :
      W t ≤ (B ^ 2 * L) * (g.volumeMeasure S).toReal := by
    apply integral_le_of_support_bound hS
    · intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hinner0 x))]
      exact mul_le_mul (hsq t ht x hx) (hgrad x) (hinner0 x) (sq_nonneg _)
    · intro x hx
      have hxs : x ∉ tsupport η := fun h ↦ hx (hηS h)
      simp [D.gradient_eq_zero_of_notMem_tsupport hxs]
  have hWc : ContinuousOn W (Icc 0 b) := by
    apply (continuousOn_integral_of_compact_support hηc.isCompact ?_ ?_).mono
      (fun _ ht ↦ ht.1 : Icc (0 : ℝ) b ⊆ Ici 0)
    · exact (hFc.pow 2).mul
        ((D.continuous_inner_gradient hη hη).comp continuous_snd).continuousOn
    · intro t x _ hx
      simp [D.gradient_eq_zero_of_notMem_tsupport hx]
  have hWi : IntervalIntegrable W volume 0 b := hWc.intervalIntegrable_of_Icc hb.le
  have hi := intervalIntegral.integral_mono_on hb.le hWi intervalIntegrable_const hW
  rw [intervalIntegral.integral_const] at hi
  simp only [sub_zero, smul_eq_mul] at hi
  have he := (D.integrated_heat_energy_cutoff_estimate_from_zero hF hFc hheat hη hηc hb).2
  change _ ≤ _ + 4 * ∫ t in 0..b, W t at he
  calc
    _ ≤ (∫ x, η x ^ 2 * F (0, x) ^ 2 ∂g.volumeMeasure) + 4 * ∫ t in 0..b, W t := he
    _ ≤ B ^ 2 * (g.volumeMeasure S).toReal +
        4 * (b * ((B ^ 2 * L) * (g.volumeMeasure S).toReal)) := by linarith
    _ = _ := by ring



theorem exists_cutoff_with_heat_energy_bound (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hFc : ContinuousOn F (Ici 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {A b R : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (hR : 1 ≤ R)
    (hbound : ∀ t ∈ Icc 0 b, ∀ x, |F (t, x)| ≤ (g.edist O x).toReal + A) :
    ∃ η : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Icc 0 1) ∧
      (∀ x, (g.edist O x).toReal ≤ R → η x = 1) ∧
      (∫ t in 0..b, ∫ x, η x ^ 2 * g.inner x
        (D.gradient (fun y ↦ F (t, y)) x) (D.gradient (fun y ↦ F (t, y)) x)
        ∂g.volumeMeasure) ≤ (5 * R + A) ^ 2 *
          (1 + 4 * b * (heatCutoffConstant / R) ^ 2) *
          (g.volumeMeasure {x | (g.edist O x).toReal ≤ 5 * R}).toReal := by
  obtain ⟨η, hη, hc, hr, hone, hs, hg⟩ := D.exists_intrinsic_ball_cutoff hcomplete O hR
  refine ⟨η, hη, hc, hr, hone, ?_⟩
  have hball : {x | (g.edist O x).toReal ≤ 5 * R} =
      {x | g.edist O x ≤ ENNReal.ofReal (5 * R)} := by
    ext x
    constructor
    · intro hx
      change g.edist O x ≤ ENNReal.ofReal (5 * R)
      rw [← ENNReal.ofReal_toReal (g.edist_ne_top O x)]
      exact ENNReal.ofReal_le_ofReal hx
    · exact ENNReal.toReal_le_of_le_ofReal (by linarith : 0 ≤ 5 * R)
  apply D.integrated_heat_energy_cutoff_bound hF hFc hheat hη hc hr
    (by rw [hball]; exact (g.isCompact_closedBall_of_metricComplete hcomplete O (5 * R)).measure_lt_top)
    hs (by linarith) hb hg
  intro t ht x hx
  have := hbound t ht x
  change (g.edist O x).toReal ≤ 5 * R at hx
  linarith



theorem integrable_heat_energy_on_ball (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hFc : ContinuousOn F (Ici 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {b R : ℝ} (hb : 0 < b) (hR : 1 ≤ R) :
    IntegrableOn (fun p : ℝ × M ↦ g.inner p.2
      (D.gradient (fun y ↦ F (p.1, y)) p.2)
      (D.gradient (fun y ↦ F (p.1, y)) p.2))
      {p | (g.edist O p.2).toReal < R}
      ((volume.restrict (Ioc 0 b)).prod g.volumeMeasure) := by
  obtain ⟨η, hη, hc, _, hone, _, _⟩ := D.exists_intrinsic_ball_cutoff hcomplete O hR
  have hs : MeasurableSet {p : ℝ × M | (g.edist O p.2).toReal < R} :=
    measurableSet_lt ((g.continuous_toReal_edist O).comp continuous_snd).measurable
      measurable_const
  apply (D.integrable_heat_energy_cutoff_from_zero hF hFc hheat hη hc hb).restrict.congr
  filter_upwards [ae_restrict_mem hs] with p hp
  simp [hone p.2 (le_of_lt hp)]



theorem integral_heat_energy_on_ball_le (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (O : M)
    {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    (hFc : ContinuousOn F (Ici 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s ↦ F (s, x))
      (D.laplacian (fun y ↦ F (t, y)) x) t)
    {A b R : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (hR : 1 ≤ R)
    (hbound : ∀ t ∈ Icc 0 b, ∀ x, |F (t, x)| ≤ (g.edist O x).toReal + A) :
    (∫ p : ℝ × M in {p | (g.edist O p.2).toReal < R}, g.inner p.2
      (D.gradient (fun y ↦ F (p.1, y)) p.2)
      (D.gradient (fun y ↦ F (p.1, y)) p.2)
      ∂((volume.restrict (Ioc 0 b)).prod g.volumeMeasure)) ≤
      (5 * R + A) ^ 2 * (1 + 4 * b * (heatCutoffConstant / R) ^ 2) *
        (g.volumeMeasure {x | (g.edist O x).toReal ≤ 5 * R}).toReal := by
  obtain ⟨η, hη, hc, _, hone, henergy⟩ :=
    D.exists_cutoff_with_heat_energy_bound hcomplete O hF hFc hheat hA hb hR hbound
  let q : ℝ × M → ℝ := fun p ↦ g.inner p.2
    (D.gradient (fun y ↦ F (p.1, y)) p.2)
    (D.gradient (fun y ↦ F (p.1, y)) p.2)
  have hs : MeasurableSet {p : ℝ × M | (g.edist O p.2).toReal < R} :=
    measurableSet_lt ((g.continuous_toReal_edist O).comp continuous_snd).measurable
      measurable_const
  have heq : (fun p : ℝ × M ↦ q p) =ᵐ[
      (((volume.restrict (Ioc 0 b)).prod g.volumeMeasure).restrict
        {p | (g.edist O p.2).toReal < R})] (fun p ↦ η p.2 ^ 2 * q p) := by
    filter_upwards [ae_restrict_mem hs] with p hp
    simp [hone p.2 (le_of_lt hp)]
  have hnonneg : ∀ p : ℝ × M, 0 ≤ η p.2 ^ 2 * q p := by
    intro p
    apply mul_nonneg (sq_nonneg _)
    by_cases hv : D.gradient (fun y ↦ F (p.1, y)) p.2 = 0
    · simp [q, hv]
    · exact (g.pos p.2 _ hv).le
  calc
    _ = ∫ p : ℝ × M in {p | (g.edist O p.2).toReal < R}, η p.2 ^ 2 * q p
        ∂((volume.restrict (Ioc 0 b)).prod g.volumeMeasure) := integral_congr_ae heq
    _ ≤ ∫ p : ℝ × M, η p.2 ^ 2 * q p
        ∂((volume.restrict (Ioc 0 b)).prod g.volumeMeasure) :=
      setIntegral_le_integral
        (D.integrable_heat_energy_cutoff_from_zero hF hFc hheat hη hc hb)
        (Filter.Eventually.of_forall hnonneg)
    _ = ∫ t in 0..b, ∫ x, η x ^ 2 * g.inner x
        (D.gradient (fun y ↦ F (t, y)) x) (D.gradient (fun y ↦ F (t, y)) x)
        ∂g.volumeMeasure :=
      D.integral_heat_energy_cutoff_eq_intervalIntegral hF hFc hheat hη hc hb
    _ ≤ _ := henergy

end PoincareConjecture.LeviCivitaData
