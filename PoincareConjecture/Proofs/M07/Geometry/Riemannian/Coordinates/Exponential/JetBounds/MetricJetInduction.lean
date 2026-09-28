import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FrameInduction












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff Topology BigOperators Manifold

namespace PoincareConjecture.CoordinateExponential

section Calculus

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_clm_le_of_apply
    {f : P → E →L[ℝ] F} (hf : ContDiff ℝ ∞ f) (m : ℕ) {x : P} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ u, ‖iteratedFDeriv ℝ m (fun y => f y u) x‖ ≤ C * ‖u‖) :
    ‖iteratedFDeriv ℝ m f x‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (Finset.prod_nonneg (by simp)))
  intro u
  have he := iteratedFDerivWithin_clm_apply_const_apply uniqueDiffOn_univ hf.contDiffOn
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) (mem_univ x) (u := u) (m := v)
  rw [iteratedFDerivWithin_of_isOpen m isOpen_univ (mem_univ x),
    iteratedFDerivWithin_of_isOpen m isOpen_univ (mem_univ x)] at he
  rw [← he]
  exact (ContinuousMultilinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_right (h u) (Finset.prod_nonneg (by simp))).trans_eq (by ring))

theorem scalarJetProductBound_mul_right (m : ℕ) (A B : ℕ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    scalarJetProductBound m A (fun q => B q * s) = scalarJetProductBound m A B * s := by
  simp only [scalarJetProductBound, abs_mul, abs_of_nonneg hs, Finset.sum_mul, mul_assoc]

end Calculus

open Poincare.Riemannian.RadialTransport

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


theorem euclideanCoefficients_eq_coframe_gram
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    g.euclideanCoefficients x u v =
      ∑ a, radialCoframeCoeff b T a x u * radialCoframeCoeff b T a x v := by
  have h := inner_radial_field D x ((T x).inverse u) ((T x).inverse v)
  rw [← hTv, ← hTv, (hTi x).self_apply_inverse, (hTi x).self_apply_inverse, h0] at h
  change g.inner x u v = _
  rw [h, ← b.sum_inner_mul_inner ((T x).inverse u) ((T x).inverse v)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [radialCoframeCoeff, OrthonormalBasis.repr_apply_apply]
  rw [real_inner_comm ((T x).inverse u) (b a)]



theorem norm_iteratedFDeriv_metric_le_of_coframe
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (m : ℕ) (A : ℕ → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hA : ∀ q ≤ m, ∀ a u,
      ‖iteratedFDeriv ℝ q (fun y => radialCoframeCoeff b T a y u) x‖ ≤ A q * ‖u‖) :
    ‖iteratedFDeriv ℝ m g.euclideanCoefficients x‖ ≤ n * scalarJetProductBound m A A := by
  have hmetric : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hC : 0 ≤ (n : ℝ) * scalarJetProductBound m A A :=
    mul_nonneg (Nat.cast_nonneg _) (scalarJetProductBound_nonneg ..)
  apply norm_iteratedFDeriv_clm_le_of_apply hmetric m hC
  intro u
  apply norm_iteratedFDeriv_clm_le_of_apply (hmetric.clm_apply contDiff_const) m
    (mul_nonneg hC (norm_nonneg u))
  intro v
  have hm : (m : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  have hf (a) (w : EuclideanSpace ℝ (Fin n)) :
      ContDiff ℝ m (fun y => radialCoframeCoeff b T a y w) :=
    (contDiff_radialCoframeCoeff b hT hTi a w).of_le hm
  have hb (a : Fin n) :
      ‖iteratedFDeriv ℝ m (fun y => radialCoframeCoeff b T a y u *
        radialCoframeCoeff b T a y v) x‖ ≤ scalarJetProductBound m A A * ‖u‖ * ‖v‖ := by
    have hh := norm_iteratedFDeriv_mul_le_scaled_bound isOpen_univ (hf a u).contDiffOn
      (hf a v).contDiffOn (mem_univ x) A (fun q => A q * ‖v‖) (norm_nonneg u)
      (fun q hq => hA q hq a u) (fun q hq => hA q hq a v)
    rw [scalarJetProductBound_mul_right m A A (norm_nonneg v)] at hh
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
  have hh := norm_iteratedFDeriv_sum_le_const
    (fun a => ((hf a u).mul (hf a v)).contDiffAt) hb
  have he : (fun y => ∑ a, radialCoframeCoeff b T a y u * radialCoframeCoeff b T a y v) =
      fun y => g.euclideanCoefficients y u v :=
    funext fun y => (euclideanCoefficients_eq_coframe_gram D b h0 hTi hTv y u v).symm
  rw [he] at hh
  simpa only [Fintype.card_fin, mul_assoc] using hh



theorem exists_uniform_geodesic_coordinate_metric_jet_bounds
    (n : ℕ) (r : ℝ) (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
      (∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w) →
      (∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
        christoffelBilinear g.euclideanCoefficients (t • x) x x = 0) →
      (∀ l, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r, D.curvatureDerivativeNorm l x ≤ C l) →
      ∀ m, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
        ‖iteratedFDeriv ℝ m g.euclideanCoefficients x‖ ≤ B m := by
  choose A B K hA hB hK hbound using exists_uniform_radial_frame_jet_bounds n r C hC
  refine ⟨fun m => n * scalarJetProductBound m (fun _ => A m) (fun _ => A m),
    fun m => mul_nonneg (Nat.cast_nonneg _) (scalarJetProductBound_nonneg ..), ?_⟩
  intro g D h0 hgeo hcurv m x hx
  have hΓ : ContDiff ℝ ∞ (christoffelBilinear g.euclideanCoefficients) := by
    rw [contDiff_iff_contDiffAt]
    exact fun y => contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients y)
      (g.inner_isInvertible y)
  obtain ⟨T, hT, _, hTv, hTi, _⟩ := exists_radial_transport_operator hΓ
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have h := (hbound m g D b h0 hgeo T hT hTi hTv hcurv).2.1
  exact norm_iteratedFDeriv_metric_le_of_coframe D b h0 hT hTi hTv m (fun _ => A m) x
    (fun q hq a u => h q hq a u x hx)

end PoincareConjecture.CoordinateExponential
