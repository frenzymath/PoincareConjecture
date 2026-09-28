import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RadialFrameComparison
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators Bundle

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}


def coordinateMap (U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => WithLp.toLp 2 (fun i => U i x)

@[simp] theorem coordinateMap_apply (U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) : coordinateMap U x i = U i x := rfl

theorem contDiff_coordinateMap {U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) : ContDiff ℝ ∞ (coordinateMap U) :=
  (contDiff_piLp 2).mpr hU

theorem contDiffOn_coordinateMap {U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hU : ∀ i, ContDiffOn ℝ ∞ (U i) s) :
    ContDiffOn ℝ ∞ (coordinateMap U) s :=
  (contDiffOn_piLp 2).mpr hU

theorem differentiableAt_coordinateMap {U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hU : ∀ i, DifferentiableAt ℝ (U i) x) :
    DifferentiableAt ℝ (coordinateMap U) x :=
  (differentiableAt_piLp 2).mpr hU



theorem fderiv_coordinateMap_apply {U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hU : ∀ i, DifferentiableAt ℝ (U i) x)
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (fderiv ℝ (coordinateMap U) x v) i = fderiv ℝ (U i) x v := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
    (differentiableAt_coordinateMap hU).hasFDerivAt
  have hrow : fderiv ℝ (U i) x =
      (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ (coordinateMap U) x) :=
    h.fderiv
  exact (congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A v) hrow).symm


theorem norm_le_sqrt_dim_mul_of_coordinate_bound
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ (i : Fin n) (v : EuclideanSpace ℝ (Fin n)), |A v i| ≤ ε * ‖v‖) :
    ‖A‖ ≤ Real.sqrt n * ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (sq_le_sq₀ (norm_nonneg (A v)) (by positivity : 0 ≤ Real.sqrt n * ε * ‖v‖)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin n, (ε * ‖v‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hε (norm_nonneg v))).mpr (hA i v)
    _ = (Real.sqrt n * ε * ‖v‖) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      ring


theorem norm_fderiv_coordinateMap_sub_id_le
    {U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hU : ∀ i, DifferentiableAt ℝ (U i) x) {ε : ℝ} (hε : 0 ≤ ε)
    (herror : ∀ i, ‖fderiv ℝ (U i) x - EuclideanSpace.proj (𝕜 := ℝ) i‖ ≤ ε) :
    ‖fderiv ℝ (coordinateMap U) x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤
      Real.sqrt n * ε := by
  apply norm_le_sqrt_dim_mul_of_coordinate_bound _ hε
  intro i v
  have heq : ((fderiv ℝ (coordinateMap U) x -
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) v) i =
      (fderiv ℝ (U i) x - EuclideanSpace.proj (𝕜 := ℝ) i) v := by
    change (fderiv ℝ (coordinateMap U) x v) i - v i = fderiv ℝ (U i) x v - v i
    rw [fderiv_coordinateMap_apply hU]
  rw [heq]
  exact ((fderiv ℝ (U i) x - EuclideanSpace.proj (𝕜 := ℝ) i).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (herror i) (norm_nonneg v))


theorem norm_fderiv_coordinateMap_sub_id_le_max [NeZero n]
    {U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hU : ∀ i, DifferentiableAt ℝ (U i) x) :
    ‖fderiv ℝ (coordinateMap U) x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤
      Real.sqrt n * Finset.univ.sup' Finset.univ_nonempty
        (fun i => ‖fderiv ℝ (U i) x - EuclideanSpace.proj (𝕜 := ℝ) i‖) := by
  apply norm_fderiv_coordinateMap_sub_id_le hU
  · exact Finset.le_sup'_of_le _ (Finset.mem_univ (0 : Fin n)) (norm_nonneg _)
  · intro i
    exact Finset.le_sup'
      (fun j : Fin n => ‖fderiv ℝ (U j) x - EuclideanSpace.proj (𝕜 := ℝ) j‖)
      (Finset.mem_univ i)

variable {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



theorem norm_fderiv_coordinateMap_sub_id_le_of_frame (D : LeviCivitaData g)
    {U : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hU : ∀ i, DifferentiableAt ℝ (U i) x)
    {T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hT : T.IsInvertible)
    (hiso : ∀ v w, g.inner x (T v) (T w) = inner ℝ v w)
    {b δ ε : ℝ} (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (hclose : ∀ v, ‖T.inverse v - v‖ ≤ δ * ‖v‖)
    (herror : ∀ i, g.tangentNorm x ((show EuclideanSpace ℝ (Fin n) from
      D.gradient (U i) x) - T (EuclideanSpace.basisFun (Fin n) ℝ i)) ≤ ε) :
    ‖fderiv ℝ (coordinateMap U) x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤
      Real.sqrt n * (ε * Real.sqrt b + δ) := by
  apply norm_fderiv_coordinateMap_sub_id_le hU
    (add_nonneg (mul_nonneg hε (Real.sqrt_nonneg b)) hδ)
  intro i
  let z : EuclideanSpace ℝ (Fin n) :=
    (show EuclideanSpace ℝ (Fin n) from D.gradient (U i) x) -
      T (EuclideanSpace.basisFun (Fin n) ℝ i)
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (mul_nonneg hε (Real.sqrt_nonneg b)) hδ)
  intro v
  have hvnorm : g.tangentNorm x v ≤ Real.sqrt b * ‖v‖ := by
    have h := Real.sqrt_le_sqrt (hupper v)
    simpa only [RiemannianMetric.tangentNorm, Real.sqrt_mul hb,
      Real.sqrt_sq (norm_nonneg v)] using h
  have hpair : |g.inner x z v| ≤ ε * (Real.sqrt b * ‖v‖) := by
    have hcs : |g.inner x z v| ≤ g.tangentNorm x z * g.tangentNorm x v := by
      let : Bundle.RiemannianBundle
          (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact abs_real_inner_le_norm (show TangentSpace (𝓡 n) x from z)
        (show TangentSpace (𝓡 n) x from v)
    exact hcs.trans (mul_le_mul (herror i) hvnorm (Real.sqrt_nonneg _) hε)
  have hframe : g.inner x (T (EuclideanSpace.basisFun (Fin n) ℝ i)) v =
      (T.inverse v) i := by
    simpa only [hT.self_apply_inverse, EuclideanSpace.basisFun_inner] using
      hiso (EuclideanSpace.basisFun (Fin n) ℝ i) (T.inverse v)
  have hgrad : g.inner x (D.gradient (U i) x) v = fderiv ℝ (U i) x v := by
    rw [D.inner_gradient]
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  have heq : fderiv ℝ (U i) x v - v i = g.inner x z v + (T.inverse v - v) i := by
    change fderiv ℝ (U i) x v - v i =
      g.inner x (D.gradient (U i) x -
        (show TangentSpace (𝓡 n) x from T (EuclideanSpace.basisFun (Fin n) ℝ i))) v +
          ((T.inverse v) i - v i)
    rw [map_sub, sub_apply, hgrad, hframe]
    ring
  have hcoframe : |(T.inverse v - v) i| ≤ δ * ‖v‖ := by
    exact (PiLp.norm_apply_le (T.inverse v - v) i).trans (hclose v)
  rw [Real.norm_eq_abs]
  change |fderiv ℝ (U i) x v - v i| ≤ (ε * Real.sqrt b + δ) * ‖v‖
  rw [heq]
  calc
    _ ≤ |g.inner x z v| + |(T.inverse v - v) i| := abs_add_le _ _
    _ ≤ ε * (Real.sqrt b * ‖v‖) + δ * ‖v‖ := add_le_add hpair hcoframe
    _ = _ := by ring

end PoincareConjecture.HarmonicCoordinates
