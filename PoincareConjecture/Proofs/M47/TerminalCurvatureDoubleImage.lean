import PoincareConjecture.Proofs.M47.TerminalCurvatureDoubleNormalization
import PoincareConjecture.Proofs.M47.TerminalCurvatureCenteredImage
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistencePullbackSmooth









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem terminalCurvature_exists_double_image_tolerance_uniform
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 / 2 ∧
      ∀ (M : Type u) (X : Type v) [TopologicalSpace M] [TopologicalSpace X]
        [ChartedSpace E₃ M] [ChartedSpace E₃ X]
        [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
        (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 X)
        (N : EpsilonNeck g), N.epsilon = epsilon →
      ∀ (D : LeviCivitaData h) (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞),
      N.carrier ⊆ phi.source →
      (∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ →
        ∀ j ≤ Nat.floor (2 * epsilon)⁻¹, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient
                (fun z v w => N.scale⁻¹ ^ 2 *
                  roundCylinderPullback h (phi ∘ N.coordinate_map) z v w)
                (chartAt E₂ q) y a b -
              roundCylinderTensorCoefficient
                (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
                (chartAt E₂ q) y a b) (0, z)‖ ≤ rho) →
      |N.scale ^ 2 * D.scalarCurvature (phi N.center) - 1| ≤ sigma →
      ∃ E : EpsilonNeck h,
        E.epsilon = 2 * epsilon ∧ E.center = phi N.center ∧ E.connection = D ∧
        E.carrier = phi '' N.region (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ ∧
        E.coordinate_map = phi ∘ N.coordinate_map := by
  obtain ⟨rho, hrho, sigma, hsigma, hsigmaHalf, hnormalize⟩ :=
    terminalCurvature_exists_double_normalization_tolerance hepsilon
  refine ⟨rho, hrho, sigma, hsigma, hsigmaHalf, ?_⟩
  intro M X _ _ _ _ _ _ g h N hN D phi hsource hjet hbeta
  let B0 : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
    roundCylinderPullback g N.coordinate_map z v w
  have hB0 : RoundCylinderClose epsilon 0 B0 := by
    simpa only [← hN] using N.metric_comparison.1
  let B : RoundCylinderTwoTensor := fun z v w => N.scale⁻¹ ^ 2 *
    roundCylinderPullback h (phi ∘ N.coordinate_map) z v w
  have hsmooth : ContMDiffOn Ic (𝓡 3) ∞ (phi ∘ N.coordinate_map)
      (univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :=
    phi.contMDiffOn_toFun.comp N.coordinate_map_smooth
      (fun _ hz => hsource (N.coordinate_map_mem_of_axial_mem hz.2))
  have hB : RoundCylinderTensorSmoothOn (2 * epsilon) B := by
    have hs := (M34.capPersistence_roundCylinderTensorSmoothOn_pullback h hsmooth).const_mul
      (beta := N.scale⁻¹ ^ 2)
    rw [hN] at hs
    exact hs.mono_epsilon hepsilon (by linarith)
  let beta := N.scale ^ 2 * D.scalarCurvature (phi N.center)
  have hbetaPos : 0 < beta := by
    have hh := (abs_le.mp (hbeta.trans hsigmaHalf)).1
    dsimp only [beta]
    linarith
  have hR : 0 < D.scalarCurvature (phi N.center) := by
    by_contra hnot
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg N.scale) (le_of_not_gt hnot)
    exact (not_lt_of_ge hh) hbetaPos
  have hclose := hnormalize B0 hB0 B hB hjet beta hbeta
  have hnormalized : RoundCylinderClose (2 * N.epsilon) 0 (fun z v w =>
      D.scalarCurvature (phi N.center) *
        roundCylinderPullback h (phi ∘ N.coordinate_map) z v w) := by
    rw [hN]
    have heq : (fun z v w => beta * B z v w) = fun z v w =>
        D.scalarCurvature (phi N.center) *
          roundCylinderPullback h (phi ∘ N.coordinate_map) z v w := by
      funext z v w
      dsimp only [beta, B]
      field_simp [N.scale_pos.ne']
    rwa [heq] at hclose
  obtain ⟨E, hE⟩ := terminalCurvature_exists_centered_double_neck N D phi
    (by simpa only [hN] using hsmall) (fun _ hx => hsource hx.1) hR hnormalized
  exact ⟨E, by simpa only [hN] using hE⟩


theorem terminalCurvature_exists_double_image_tolerance
    {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace E₃ M] [ChartedSpace E₃ X]
    [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X]
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2) :
    ∃ rho : ℝ, 0 < rho ∧ ∃ sigma : ℝ, 0 < sigma ∧ sigma ≤ 1 / 2 ∧
      ∀ (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 X)
        (N : EpsilonNeck g), N.epsilon = epsilon →
      ∀ (D : LeviCivitaData h) (phi : PartialDiffeomorph (𝓡 3) (𝓡 3) M X ∞),
      N.carrier ⊆ phi.source →
      (∀ (q : UnitTwoSphere) (z : ℝ), z ∈ Ioo (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ →
        ∀ j ≤ Nat.floor (2 * epsilon)⁻¹, ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient
                (fun z v w => N.scale⁻¹ ^ 2 *
                  roundCylinderPullback h (phi ∘ N.coordinate_map) z v w)
                (chartAt E₂ q) y a b -
              roundCylinderTensorCoefficient
                (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
                (chartAt E₂ q) y a b) (0, z)‖ ≤ rho) →
      |N.scale ^ 2 * D.scalarCurvature (phi N.center) - 1| ≤ sigma →
      ∃ E : EpsilonNeck h,
        E.epsilon = 2 * epsilon ∧ E.center = phi N.center ∧ E.connection = D ∧
        E.carrier = phi '' N.region (-(2 * epsilon)⁻¹) (2 * epsilon)⁻¹ ∧
        E.coordinate_map = phi ∘ N.coordinate_map := by
  obtain ⟨rho, hrho, sigma, hsigma, hsigmaHalf, hbound⟩ :=
    terminalCurvature_exists_double_image_tolerance_uniform hepsilon hsmall
  exact ⟨rho, hrho, sigma, hsigma, hsigmaHalf, hbound M X⟩

end PoincareConjecture.M47
