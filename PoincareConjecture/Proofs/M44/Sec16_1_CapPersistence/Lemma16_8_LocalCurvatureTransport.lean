import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_LocalScalarTransport
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_CollarTransport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareConjecture.Proofs.M04.TensorNorm









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}



theorem curvatureTensorNorm_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    {Q : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 n) y,
      h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) =
        Q * g.inner y v w) {x : M} (hx : x ∈ U) :
    D'.curvatureTensorNorm (f x) = D.curvatureTensorNorm x / Q := by
  let DQ := m01RescaledMetric_connection g D Q hQ
  have hm (y : M) (hy : y ∈ U) (v w : TangentSpace (𝓡 n) y) :
      (m01RescaledMetric g Q hQ).inner y v w =
        h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) :=
    (m01RescaledMetric_inner g Q hQ y v w).trans (hmetric y hy v w).symm
  have hnorm := DQ.curvatureDerivativeNorm_eq_pullback D' hU hf hinv hm 0 hx
  simp only [LeviCivitaData.curvatureDerivativeNorm_zero] at hnorm
  rw [← hnorm]
  exact M13.homothety_curvatureTensorNorm_eq g (m01RescaledMetric g Q hQ)
    (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (rescaledMetric_identity_homothety hQ) D DQ x





theorem sectionalCurvature_eq_of_local_homothety
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {U : Set M}
    (hU : IsOpen U) (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    {Q : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 n) y,
      h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) =
        Q * g.inner y v w) {x : M} (hx : x ∈ U)
    (u v : TangentSpace (𝓡 n) x) :
    D'.sectionalCurvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
      (mfderiv (𝓡 n) (𝓡 n) f x v) = D.sectionalCurvature x u v / Q := by
  let DQ := m01RescaledMetric_connection g D Q hQ
  have hm (y : M) (hy : y ∈ U) (v w : TangentSpace (𝓡 n) y) :
      (m01RescaledMetric g Q hQ).inner y v w =
        h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y v) (mfderiv (𝓡 n) (𝓡 n) f y w) :=
    (m01RescaledMetric_inner g Q hQ y v w).trans (hmetric y hy v w).symm
  have hsection : DQ.sectionalCurvature x u v =
      D'.sectionalCurvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
        (mfderiv (𝓡 n) (𝓡 n) f x v) := by
    simp only [LeviCivitaData.sectionalCurvature,
      DQ.curvatureTensor_eq_of_local_isometry D' hU hf hm hx, hm x hx]
  rw [← hsection]
  simpa only [Diffeomorph.coe_refl, id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using
    M13.homothety_sectionalCurvature_eq g (m01RescaledMetric g Q hQ)
      (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (rescaledMetric_identity_homothety hQ) D DQ x u v

section Collar

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y] [T2Space X] [T2Space Y]




theorem exists_collar_plane_of_local_homothety
    {gX : RiemannianMetric 3 X} {gY : RiemannianMetric 3 Y}
    (D : LeviCivitaData gX) (D' : LeviCivitaData gY) {f : X → Y} {V : Set X}
    (hV : IsOpen V) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f V)
    (hinv : ∀ y ∈ V, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {Q : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ y ∈ V, ∀ v w : TangentSpace (𝓡 3) y,
      gY.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v) (mfderiv (𝓡 3) (𝓡 3) f y w) =
        Q * gX.inner y v w) {x : X} (hx : x ∈ V) (C : ℝ)
    (u v : TangentSpace (𝓡 3) x) (horth : LeviCivitaData.IsOrthonormalPair gX x u v)
    (hmargin : D.sectionalCurvature x u v < C⁻¹ * D.scalarCurvature x) :
    ∃ p q : TangentSpace (𝓡 3) (f x), LeviCivitaData.IsOrthonormalPair gY (f x) p q ∧
      D'.sectionalCurvature (f x) p q < C⁻¹ * D'.scalarCurvature (f x) := by
  apply exists_collar_plane_of_positiveGram D' (f x) C
    (mfderiv (𝓡 3) (𝓡 3) f x u) (mfderiv (𝓡 3) (𝓡 3) f x v)
  · rw [hmetric x hx, hmetric x hx, hmetric x hx, horth.1, horth.2.1, horth.2.2]
    simpa only [mul_one, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero] using mul_pos hQ hQ
  · rw [sectionalCurvature_eq_of_local_homothety D D' hV hf hQ hmetric hx,
      scalar_eq_of_local_homothety D D' hV hf hinv hQ hmetric hx, ← mul_div_assoc]
    exact (div_lt_div_iff_of_pos_right hQ).mpr hmargin

end Collar

end PoincareConjecture.M44
