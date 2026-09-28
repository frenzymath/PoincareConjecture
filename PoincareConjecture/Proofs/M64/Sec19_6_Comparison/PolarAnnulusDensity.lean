import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.PolarForwardMap
import PoincareConjecture.Proofs.M58.Mathlib.TwoVectorArea












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Real Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

open Proofs.M58




theorem m64PolarAnnulusMap_density_le
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {f : LoopPlane → M}
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    {r : ℝ} (hr : 0 < r) (theta : ℝ) :
    r * m60AreaDensity g (m64PolarAnnulusMap f) (r • angularPoint theta) ≤
      2 * m60AreaDensity g f (annulusPoint theta (2 * r - 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let F := m64PolarAnnulusMap f
  let p := annulusPoint theta (2 * r - 1)
  have hp0 : p 0 = theta := rfl
  have hp1 : p 1 = 2 * r - 1 := rfl
  have hrad : (1 / 2 : ℝ) * (p 1 + 1) = r := by rw [hp1]; ring
  have hforward : m64PolarForwardMap p = r • angularPoint theta := by
    simp only [m64PolarForwardMap, hrad, hp0]
  suffices h : r * m60AreaDensity g F (m64PolarForwardMap p) ≤
      2 * m60AreaDensity g f p by simpa only [F, p, hforward] using h
  by_cases hF : MDifferentiableAt (𝓡 2) (𝓡 n) F (m64PolarForwardMap p)
  · have harea (G : LoopPlane → M) (z : LoopPlane) :
        m60AreaDensity g G z =
          twoVectorArea
            (mfderiv (𝓡 2) (𝓡 n) G z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
            (mfderiv (𝓡 2) (𝓡 n) G z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) := by
      unfold m60AreaDensity twoVectorArea m60AreaGram
      rw [Matrix.det_fin_two]
      dsimp only
      rw [show g.inner (G z)
          (mfderiv (𝓡 2) (𝓡 n) G z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
          (mfderiv (𝓡 2) (𝓡 n) G z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
          g.inner (G z)
          (mfderiv (𝓡 2) (𝓡 n) G z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (mfderiv (𝓡 2) (𝓡 n) G z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) from g.symm _ _ _]
      rw [pow_two]
      rfl
    let D := mfderiv (𝓡 2) (𝓡 n) F (m64PolarForwardMap p)
    let u := D (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    let v := D (EuclideanSpace.basisFun (Fin 2) ℝ 1)
    have hrep (w : LoopPlane) : D w = w 0 • u + w 1 • v := by
      have hw : w = w 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
          w 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
        simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using
          ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr w).symm
      calc
        D w = D (w 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
            w 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1) := congrArg D hw
        _ = _ := by erw [map_add, map_smul, map_smul]
    have hframe : twoVectorArea (D (r • angularVector theta))
        (D ((1 / 2 : ℝ) • angularPoint theta)) =
        (r / 2) * m60AreaDensity g F (m64PolarForwardMap p) := by
      rw [hrep, hrep]
      change twoVectorArea ((r * -sin theta) • u + (r * cos theta) • v)
        (((1 / 2 : ℝ) * cos theta) • u + ((1 / 2 : ℝ) * sin theta) • v) = _
      rw [twoVectorArea_change]
      have hdet : r * -sin theta * ((1 / 2 : ℝ) * sin theta) -
          r * cos theta * ((1 / 2 : ℝ) * cos theta) = -(r / 2) := by
        calc
          _ = -(r / 2) * (sin theta ^ 2 + cos theta ^ 2) := by ring
          _ = -(r / 2) := by rw [sin_sq_add_cos_sq, mul_one]
      rw [hdet, abs_neg, abs_of_pos (div_pos hr (by norm_num)), harea]
    have hPhi := (m64PolarForwardMap_hasFDerivAt p).hasMFDerivAt
    have hcol0 : mfderiv (𝓡 2) (𝓡 n) (F ∘ m64PolarForwardMap) p
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) = D (r • angularVector theta) := by
      rw [mfderiv_comp_apply p hF hPhi.mdifferentiableAt]
      congr 1
      rw [hPhi.mfderiv]
      change (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0 •
          (((1 / 2 : ℝ) * (p 1 + 1)) • angularVector (p 0)) +
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) 1 •
          ((1 / 2 : ℝ) • angularPoint (p 0)) = r • angularVector theta
      rw [hrad, hp0]
      simp [EuclideanSpace.basisFun_apply]
    have hcol1 : mfderiv (𝓡 2) (𝓡 n) (F ∘ m64PolarForwardMap) p
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) = D ((1 / 2 : ℝ) • angularPoint theta) := by
      rw [mfderiv_comp_apply p hF hPhi.mdifferentiableAt]
      congr 1
      rw [hPhi.mfderiv]
      change (EuclideanSpace.basisFun (Fin 2) ℝ 1) 0 •
          (((1 / 2 : ℝ) * (p 1 + 1)) • angularVector (p 0)) +
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) 1 •
          ((1 / 2 : ℝ) • angularPoint (p 0)) = (1 / 2 : ℝ) • angularPoint theta
      simp [hp0, EuclideanSpace.basisFun_apply]
    have heq := m64PolarAnnulusMap_comp_forward_eventually hperiodic
      (p := p) (by rw [hp1]; linarith)
    have hareaEq : m60AreaDensity g (F ∘ m64PolarForwardMap) p = m60AreaDensity g f p := by
      unfold m60AreaDensity m60AreaGram
      rw [heq.mfderiv_eq, heq.self_of_nhds]
    have h := harea (F ∘ m64PolarForwardMap) p
    rw [hcol0, hcol1, hframe, hareaEq] at h
    nlinarith only [h]
  · have hzero : m60AreaDensity g F (m64PolarForwardMap p) = 0 := by
      simp only [m60AreaDensity, m60AreaGram, mfderiv_zero_of_not_mdifferentiableAt hF,
        zero_apply, map_zero, Matrix.det_fin_two,
        zero_mul, sub_zero, max_self, Real.sqrt_zero]
    rw [hzero, mul_zero]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

end PoincareConjecture
