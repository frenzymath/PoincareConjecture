import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalAxialSign











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_transition_axis_prefix_signed_deriv_bounds_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N P : EpsilonNeck g), N.epsilon ≤ ε₀ → P.epsilon ≤ ε₀ →
        ∀ (q : UnitTwoSphere) {t₀ v δ : ℝ}, (v = 1 ∨ v = -1) → 0 < δ →
          MapsTo (fun s => P.coordinate_map (q, t₀ + v * s)) (Icc 0 δ) N.carrier →
          (N.coordinate_inverse (P.coordinate_map (q, t₀ + v * δ))).2 <
            (N.coordinate_inverse (P.coordinate_map (q, t₀))).2 →
          ∀ {L : ℝ}, 0 ≤ L →
            (∀ s ∈ Icc 0 (max δ L), t₀ + v * s ∈ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹) →
            MapsTo (fun s => P.coordinate_map (q, t₀ + v * s)) (Icc 0 L) N.carrier →
            ∀ s ∈ Icc 0 L,
              (-1.1 : ℝ) ≤ v * deriv
                (fun t => (N.coordinate_inverse (P.coordinate_map (q, t))).2) (t₀ + v * s) ∧
              v * deriv (fun t => (N.coordinate_inverse (P.coordinate_map (q, t))).2)
                (t₀ + v * s) ≤ (-0.9 : ℝ) := by
  obtain ⟨ε₀, hε₀, hsmall, hbounds⟩ := exists_transition_axis_signed_deriv_bounds_m28.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N P hN hP q t₀ v δ hv hδ hseedCarrier hseed L _ hdom hprefix
  let S := (fun s : ℝ => t₀ + v * s) '' Icc 0 (max δ L)
  let f := fun t : ℝ => (N.coordinate_inverse (P.coordinate_map (q, t))).2
  have hS : IsPreconnected S := isPreconnected_Icc.image _
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have hSdom : S ⊆ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    exact hdom s hs
  have hScarrier : ∀ t ∈ S, P.coordinate_map (q, t) ∈ N.carrier := by
    rintro _ ⟨s, hs, rfl⟩
    rcases le_total δ L with hle | hle
    · exact hprefix ⟨hs.1, hs.2.trans (max_eq_right hle).le⟩
    · exact hseedCarrier ⟨hs.1, hs.2.trans (max_eq_left hle).le⟩
  have hzero : t₀ ∈ S := by
    refine ⟨0, ⟨le_rfl, hδ.le.trans (le_max_left _ _)⟩, ?_⟩
    simp only [mul_zero, add_zero]
  have hdelta : t₀ + v * δ ∈ S :=
    ⟨δ, ⟨hδ.le, le_max_left _ _⟩, rfl⟩
  have hmem {s : ℝ} (hs : s ∈ Icc 0 L) : t₀ + v * s ∈ S :=
    ⟨s, ⟨hs.1, hs.2.trans (le_max_right _ _)⟩, rfl⟩
  have hsigned := hbounds N P hN hP q S hS hSdom hScarrier
  change f (t₀ + v * δ) < f t₀ at hseed
  rcases hv with rfl | rfl
  · have horder : t₀ < t₀ + 1 * δ := by linarith
    have hsign : 0 < (-1 : ℝ) * (f (t₀ + 1 * δ) - f t₀) := by linarith
    intro s hs
    have hb := hsigned t₀ hzero (t₀ + 1 * δ) hdelta horder (-1) (Or.inr rfl) hsign
      (t₀ + 1 * s) (hmem hs)
    change (0.9 : ℝ) ≤ -1 * deriv f (t₀ + 1 * s) ∧
      -1 * deriv f (t₀ + 1 * s) ≤ (1.1 : ℝ) at hb
    change (-1.1 : ℝ) ≤ 1 * deriv f (t₀ + 1 * s) ∧
      1 * deriv f (t₀ + 1 * s) ≤ (-0.9 : ℝ)
    constructor <;> linarith [hb.1, hb.2]
  · have horder : t₀ + (-1) * δ < t₀ := by linarith
    have hsign : 0 < (1 : ℝ) * (f t₀ - f (t₀ + (-1) * δ)) := by linarith
    intro s hs
    have hb := hsigned (t₀ + (-1) * δ) hdelta t₀ hzero horder 1 (Or.inl rfl) hsign
      (t₀ + (-1) * s) (hmem hs)
    change (0.9 : ℝ) ≤ 1 * deriv f (t₀ + (-1) * s) ∧
      1 * deriv f (t₀ + (-1) * s) ≤ (1.1 : ℝ) at hb
    change (-1.1 : ℝ) ≤ (-1) * deriv f (t₀ + (-1) * s) ∧
      (-1) * deriv f (t₀ + (-1) * s) ≤ (-0.9 : ℝ)
    constructor <;> linarith [hb.1, hb.2]

end PoincareConjecture.EpsilonNeck
