import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.SectionalIntegral








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M}



theorem levelMeanCurvature_div_tangentNorm_le_of_hessian_le
    (D : LeviCivitaData g) {f : M → ℝ} {x : M} {l H : ℝ}
    (hl : 0 < l) (hH : 0 ≤ H)
    (hspeed : l ≤ g.tangentNorm x (g.gradient f x))
    (hhess : ∀ v : TangentSpace (𝓡 (n + 1)) x,
      D.hessian f x v v ≤ H * g.inner x v v) :
    D.levelMeanCurvature f x / g.tangentNorm x (g.gradient f x) ≤
      (n : ℝ) * H / l ^ 2 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hs : l ≤ Real.sqrt (D.levelQ f x) := hspeed
  have hspos : 0 < Real.sqrt (D.levelQ f x) := hl.trans_le hs
  have hq : 0 < D.levelQ f x := Real.sqrt_pos.mp hspos
  have hmean : D.levelMeanCurvature f x ≤ (n : ℝ) * (H / l) := by
    apply D.levelMeanCurvature_le_of_tangentialHessian hq (H / l)
    intro v _
    have hv : 0 ≤ g.inner x v v := by
      change 0 ≤ inner ℝ v v
      exact real_inner_self_nonneg
    calc
      D.hessian f x v v / Real.sqrt (D.levelQ f x) ≤
          (H * g.inner x v v) / Real.sqrt (D.levelQ f x) :=
        div_le_div_of_nonneg_right (hhess v) hspos.le
      _ ≤ (H * g.inner x v v) / l :=
        div_le_div_of_nonneg_left (mul_nonneg hH hv) hl hs
      _ = H / l * g.inner x v v := by ring
  change D.levelMeanCurvature f x / Real.sqrt (D.levelQ f x) ≤ _
  calc
    D.levelMeanCurvature f x / Real.sqrt (D.levelQ f x) ≤
        ((n : ℝ) * (H / l)) / Real.sqrt (D.levelQ f x) :=
      div_le_div_of_nonneg_right hmean hspos.le
    _ ≤ ((n : ℝ) * (H / l)) / l :=
      div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) (div_nonneg hH hl.le)) hl hs
    _ = (n : ℝ) * H / l ^ 2 := by ring

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]



theorem hasDerivAt_regularLevelArea_and_le_of_hessian_le
    (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {I : Set ℝ} (hI : IsOpen I) (hproper : IsProperMap (I.restrictPreimage f))
    {l H : ℝ} (hl : 0 < l) (hH : 0 ≤ H)
    (hspeed : ∀ x : M, f x ∈ I → l ≤ g.tangentNorm x (g.gradient f x))
    (hhess : ∀ x : M, f x ∈ I → ∀ v : TangentSpace (𝓡 (n + 1)) x,
      D.hessian f x v v ≤ H * g.inner x v v)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (g.regularLevelArea hf) (deriv (g.regularLevelArea hf) t) t ∧
      deriv (g.regularLevelArea hf) t ≤
        ((n : ℝ) * H / l ^ 2) * g.regularLevelArea hf t := by
  have hreg (x : M) (hx : f x ∈ I) : mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0 :=
    (g.tangentNorm_gradient_pos_iff f x).mp (hl.trans_le (hspeed x hx))
  have hd := (D.first_variation_regularLevelArea hf hI hproper hreg).2 t ht
  refine ⟨by rw [hd.deriv]; exact hd, ?_⟩
  rw [hd.deriv]
  let := isFiniteMeasure_regularLevelVolume_of_isProperMap (g := g) hf hI hproper hreg ht
  have hi := integrable_regularLevelVolume_of_isProperMap hf hI hproper hreg ht
    ((D.continuousOn_levelMeanCurvature_regularDomain hf).div
      (g.continuous_tangentNorm_gradient hf).continuousOn (fun _ hx => ne_of_gt hx))
  have hbound (z : openLevelSet f (g.regularDomain hf) t) :
      D.levelMeanCurvature f (openLevelIncl f (g.regularDomain hf) t z) /
        g.tangentNorm (openLevelIncl f (g.regularDomain hf) t z)
          (g.gradient f (openLevelIncl f (g.regularDomain hf) t z)) ≤ (n : ℝ) * H / l ^ 2 := by
    have hz : f (openLevelIncl f (g.regularDomain hf) t z) ∈ I := by
      rw [show f (openLevelIncl f (g.regularDomain hf) t z) = t from z.2]
      exact ht
    exact D.levelMeanCurvature_div_tangentNorm_le_of_hessian_le hl hH
      (hspeed _ hz) (hhess _ hz)
  have hint := integral_mono hi (integrable_const ((n : ℝ) * H / l ^ 2)) hbound
  simpa only [Function.comp_def, Pi.div_apply, integral_const, smul_eq_mul,
    RiemannianMetric.regularLevelArea, mul_comm _ ((n : ℝ) * H / l ^ 2)] using hint

end PoincareConjecture.LeviCivitaData
