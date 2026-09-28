import PoincareConjecture.Proofs.M34.Standard.CapNeckNormalizedImage

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

theorem exists_capNeckNormalizedImage_end_boundary_tolerance {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon' : epsilon < 1 / 2) :
    ∃ tau : ℝ, 0 < tau ∧ ∃ eta : ℝ, 0 < eta ∧
      ∀ {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
        [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
        {g : RiemannianMetric 3 M} (h : RiemannianMetric 3 X) (N : EpsilonNeck g),
        N.epsilon ≤ epsilon → ∀ (D : LeviCivitaData h) (e : OpenPartialHomeomorph M X),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target → N.carrier ⊆ e.source →
        let B : RoundCylinderTwoTensor := fun z v w =>
          N.scale⁻¹ ^ 2 * roundCylinderPullback h (e ∘ N.coordinate_map) z v w
        RoundCylinderTensorSmoothOn N.epsilon B →
        (∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
          ∀ j ≤ Nat.floor epsilon⁻¹, ∀ a b : Fin 3,
            ‖iteratedFDeriv ℝ j (fun y =>
              roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
                roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ tau) →
        (∀ q₀ : UnitTwoSphere,
          let c := epsilon⁻¹ - N.epsilon⁻¹
          let R := D.scalarCurvature (e (N.coordinate_map (q₀, c)))
          |N.scale ^ 2 * R - 1| ≤ eta →
          ∃ E : EpsilonNeck h,
            E.epsilon = epsilon ∧ E.connection = D ∧
            E.center = e (N.coordinate_map (q₀, c)) ∧ E.scale = R ^ (-1 / 2 : ℝ) ∧
            E.carrier = e '' N.region (-N.epsilon⁻¹) (2 / epsilon - N.epsilon⁻¹) ∧
            E.region (-epsilon⁻¹) (-epsilon⁻¹ / 2) =
              e '' N.region (-N.epsilon⁻¹) (1 / (2 * epsilon) - N.epsilon⁻¹)) ∧
        (∀ q₀ : UnitTwoSphere,
          let R := D.scalarCurvature (e (N.coordinate_map (q₀, 0)))
          |N.scale ^ 2 * R - 1| ≤ eta →
          ∃ E : EpsilonNeck h,
            E.epsilon = epsilon ∧ E.connection = D ∧
            E.center = e (N.coordinate_map (q₀, 0)) ∧ E.scale = R ^ (-1 / 2 : ℝ) ∧
            E.carrier = e '' N.region (-epsilon⁻¹) epsilon⁻¹ ∧
            E.central_sphere = e '' N.central_sphere) := by
  obtain ⟨tau, htau, eta, heta, hconstruct⟩ :=
    exists_capNeckNormalizedImage_tolerance hepsilon hepsilon'
  refine ⟨tau, htau, eta, heta, ?_⟩
  intro M X _ _ _ _ _ _ g h N hN D e hf hi hsource
  dsimp only
  intro hB herror
  constructor
  · intro q₀ hscalar
    obtain ⟨E, he, hs, hc, hD, hcarrier, _, hregion⟩ :=
      hconstruct N.epsilon N.epsilon_pos hN h N le_rfl D e hf hi hsource q₀
        hB herror hscalar
    refine ⟨E, he, hD, hc, hs, ?_, ?_⟩
    · rw [hcarrier]
      congr 2
      all_goals
        try simp only [div_eq_mul_inv]
        ring
    · rw [hregion (-epsilon⁻¹) (-epsilon⁻¹ / 2) le_rfl
        (by linarith [inv_pos.mpr hepsilon])]
      congr 2
      all_goals
        try simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  · intro q₀ hscalar
    have hinterval : Ioo (-epsilon⁻¹) epsilon⁻¹ ⊆
        Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      intro s hs
      have hinv := inv_anti₀ N.epsilon_pos hN
      constructor <;> linarith [hs.1, hs.2]
    have hsmooth : RoundCylinderTensorSmoothOn epsilon (fun z v w =>
        N.scale⁻¹ ^ 2 * roundCylinderPullback h (e ∘ N.coordinate_map) z v w) := by
      intro q a b
      exact (hB q a b).mono (Set.prod_mono (Subset.refl _) hinterval)
    obtain ⟨E, he, hs, hc, hD, hcarrier, hsphere, _⟩ :=
      hconstruct epsilon hepsilon le_rfl h N hN D e hf hi hsource q₀ hsmooth
        (fun q s hs j hj a b => herror q s (hinterval hs) j hj a b)
        (by simpa only [sub_self] using hscalar)
    refine ⟨E, he, hD, ?_, ?_, ?_, ?_⟩
    · simpa only [sub_self] using hc
    · simpa only [sub_self] using hs
    · simpa only [sub_self, add_zero] using hcarrier
    · rw [N.central_sphere_eq]
      simpa only [sub_self] using hsphere

end PoincareConjecture.M34
