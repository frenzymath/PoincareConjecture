import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalFrontierScale
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceLower

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

theorem edist_le_of_mem_closure_positive_quarter_pair_m28
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (hε : N.epsilon ≤ 1 / 1000)
    {x y : M} (hx : x ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹))
    (hy : y ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) :
    g.edist x y ≤ ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  exact closure_minimal (fun z hz => N.edist_le_of_mem_closure_positive_quarter_m28 hε hz hy)
    (isClosed_le (continuous_id.edist continuous_const) continuous_const) hx

theorem exists_closure_positive_quarter_subset_of_central_sphere_contact_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon = N.epsilon →
        (closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ∩ N'.central_sphere).Nonempty →
          closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ⊆ N'.carrier := by
  obtain ⟨ε₁, hε₁, _, hscale⟩ := exists_scale_comparison_at_common_closure_m28.{u}
  refine ⟨min ε₁ (1 / 1000), lt_min hε₁ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hε heq ⟨x, hx, hx'⟩ y hy
  have hsmall : N.epsilon ≤ 1 / 1000 := hε.trans (min_le_right _ _)
  have hN : N.epsilon ≤ ε₁ := hε.trans (min_le_left _ _)
  have hs := (hscale N N' hN (heq ▸ hN)
    ⟨x, closure_mono (N.region_subset_carrier _ _) hx,
      subset_closure (N'.central_sphere_subset hx')⟩).1
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hupper : g.edist N'.center y ≤
      ENNReal.ofReal ((2 * Real.pi) * N'.scale) +
        ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) := by
    have hcomm : g.edist x y = g.edist y x := Manifold.riemannianEDist_comm
    calc
      _ ≤ g.edist N'.center x + g.edist x y := Manifold.riemannianEDist_triangle
      _ ≤ _ := add_le_add
        (N'.edist_central_sphere_le_two_pi_mul_scale N'.center_on_central_sphere hx')
        (hcomm ▸ edist_le_of_mem_closure_positive_quarter_pair_m28 N hsmall hy hx)
  by_contra hout
  have hlower := N'.balanced_edist_lower_of_not_mem_carrier (heq ▸ hsmall) hout
  rw [heq] at hlower
  have hscale_pos := N.scale_pos
  have hscale'_pos := N'.scale_pos
  have hepsilon := N.epsilon_pos
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hepsilon).mpr
    linarith
  have hnum : (2 * Real.pi) * N'.scale + (0.51 : ℝ) * N.scale * N.epsilon⁻¹ <
      (0.99 : ℝ) * N'.scale * N.epsilon⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_right hs (inv_pos.mpr hepsilon).le
    have h2 := mul_le_mul_of_nonneg_right Real.pi_le_four hscale'_pos.le
    have h3 := mul_le_mul_of_nonneg_left hinv hscale'_pos.le
    nlinarith [mul_pos hscale_pos (inv_pos.mpr hepsilon)]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at hupper
  have hlt := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hnum
  exact (not_lt_of_ge (hlower.trans hupper)) hlt

theorem exists_positive_quarter_subset_of_central_sphere_contact_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon = N.epsilon →
        (closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) ∩ N'.central_sphere).Nonempty →
          N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier := by
  obtain ⟨ε₀, hε₀, hsmall, hcontain⟩ :=
    exists_closure_positive_quarter_subset_of_central_sphere_contact_m28.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hN' hcontact
  exact subset_closure.trans (hcontain N N' hN hN' hcontact)

end PoincareConjecture.EpsilonNeck
