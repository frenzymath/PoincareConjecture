import PoincareConjecture.Proofs.M34.Standard.CapNeckNormalizedImagePullback










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)





theorem exists_capNeckNormalizedImage_tolerance {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon' : epsilon < 1 / 2) :
    ∃ tau : ℝ, 0 < tau ∧ ∃ eta : ℝ, 0 < eta ∧
      ∀ d : ℝ, 0 < d → d ≤ epsilon →
      ∀ {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
        [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
        {g : RiemannianMetric 3 M} (h : RiemannianMetric 3 X) (N : EpsilonNeck g),
        N.epsilon ≤ d → ∀ (D : LeviCivitaData h) (e : OpenPartialHomeomorph M X),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target → N.carrier ⊆ e.source →
        ∀ q₀ : UnitTwoSphere,
        let B : RoundCylinderTwoTensor := fun z v w =>
          N.scale⁻¹ ^ 2 * roundCylinderPullback h (e ∘ N.coordinate_map) z v w
        let c := epsilon⁻¹ - d⁻¹
        let R := D.scalarCurvature (e (N.coordinate_map (q₀, c)))
        RoundCylinderTensorSmoothOn d B →
        (∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-d⁻¹) d⁻¹ →
          ∀ j ≤ Nat.floor epsilon⁻¹, ∀ a b : Fin 3,
            ‖iteratedFDeriv ℝ j (fun y =>
              roundCylinderTensorCoefficient B (chartAt E₂ q) y a b -
                roundCylinderGram 0 (chartAt E₂ q) y a b) (0, s)‖ ≤ tau) →
        |N.scale ^ 2 * R - 1| ≤ eta →
        ∃ E : EpsilonNeck h,
          E.epsilon = epsilon ∧ E.scale = R ^ (-1 / 2 : ℝ) ∧
          E.center = e (N.coordinate_map (q₀, c)) ∧ E.connection = D ∧
          E.carrier = e '' N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ∧
          E.central_sphere = e '' (N.coordinate_map '' (univ ×ˢ ({c} : Set ℝ))) ∧
          ∀ a b : ℝ, -epsilon⁻¹ ≤ a → b ≤ epsilon⁻¹ →
            E.region a b = e '' N.region (a + c) (b + c) := by
  obtain ⟨tau, htau, eta, heta, hnormalize⟩ :=
    exists_capNeckNormalization_ordinary_tolerance hepsilon
  refine ⟨tau, htau, min eta (1 / 2), lt_min heta (by norm_num), ?_⟩
  intro d hd hde M X _ _ _ _ _ _ g h N hNd D e hf hi hsource q₀
  dsimp only
  intro hB herror hscalar
  let B : RoundCylinderTwoTensor := fun z v w =>
    N.scale⁻¹ ^ 2 * roundCylinderPullback h (e ∘ N.coordinate_map) z v w
  let c : ℝ := epsilon⁻¹ - d⁻¹
  let R : ℝ := D.scalarCurvature (e (N.coordinate_map (q₀, c)))
  have hbeta : |N.scale ^ 2 * R - 1| ≤ min eta (1 / 2) := hscalar
  have hR : 0 < R := by
    have hb := (abs_le.mp (hbeta.trans (min_le_right _ _))).1
    by_contra hnot
    have hmul := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg N.scale) (le_of_not_gt hnot)
    linarith
  have hdomain : Ioo (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆
      Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro s hs
    have hNinv := inv_anti₀ N.epsilon_pos hNd
    have hdinv := inv_anti₀ hd hde
    dsimp only [c] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hregion : N.region (-epsilon⁻¹ + c) (epsilon⁻¹ + c) ⊆ e.source :=
    fun _ hx => hsource hx.1
  have hnormalized : RoundCylinderClose epsilon 0
      (fun z v w => (N.scale ^ 2 * R) * roundCylinderShift c B z v w) :=
    hnormalize d hd hde B hB herror (N.scale ^ 2 * R)
      (hbeta.trans (min_le_left _ _))
  have hclose : RoundCylinderClose epsilon 0 (fun z v w =>
      (R ^ (-1 / 2 : ℝ))⁻¹ ^ 2 *
        roundCylinderPullback h (fun z => e (N.coordinate_map (z.1, z.2 + c))) z v w) := by
    apply hnormalized.congr_cylinder
    intro z hz v w
    exact (N.normalized_shifted_image_tensor_eq h e hf hsource hR c z
      (hdomain ⟨by linarith [hz.1], by linarith [hz.2]⟩) v w).symm
  let E := N.imageShift e hf hi hepsilon hepsilon' hdomain hregion D q₀
    (Real.rpow_pos_of_pos hR _) hR rfl hclose
  obtain ⟨he, hs, hc, hD, hcarrier, hsphere, _⟩ :=
    N.imageShift_data e hf hi hepsilon hepsilon' hdomain hregion D q₀
      (Real.rpow_pos_of_pos hR _) hR rfl hclose
  refine ⟨E, he, hs, hc, hD, hcarrier, hsphere, ?_⟩
  intro a b ha hb
  exact N.imageShift_region e hf hi hepsilon hepsilon' hdomain hregion D q₀
    (Real.rpow_pos_of_pos hR _) hR rfl hclose a b ha hb

end PoincareConjecture.M34
