import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanFields
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}

theorem covariantDerivativeOnFields_mpullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {x : M}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    (X Y : (y : N) → TangentSpace (𝓡 n) y)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) (f x)) :
    D.covariantDerivativeOnFields (mpullback (𝓡 n) (𝓡 n) f X)
        (mpullback (𝓡 n) (𝓡 n) f Y) x =
      mpullback (𝓡 n) (𝓡 n) f (D'.covariantDerivativeOnFields X Y) x := by
  rw [covariantDerivativeOnFields, D.connection_mpullback_of_metric_pullback D'
    hf hinv hmetric hY]
  simp only [mpullback_apply, hinv.self_of_nhds.self_apply_inverse,
    covariantDerivativeOnFields]

theorem curvatureOnFields_mpullback
    (D : LeviCivitaData g) (D' : LeviCivitaData h) {f : M → N} {x : M}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace (𝓡 n) y,
      g.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    {X Y Z : (y : N) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) (f x))
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) (f x))
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) (f x)) :
    D.curvatureOnFields (mpullback (𝓡 n) (𝓡 n) f X)
        (mpullback (𝓡 n) (𝓡 n) f Y) (mpullback (𝓡 n) (𝓡 n) f Z) x =
      mpullback (𝓡 n) (𝓡 n) f (D'.curvatureOnFields X Y Z) x := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 M)
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) N := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 N)
  let P := mpullback (𝓡 n) (𝓡 n) f
  have hP {W : (y : N) → TangentSpace (𝓡 n) y}
      (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) (f x)) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (P W)) x :=
    hW.mpullback_vectorField_preimage hf hinv.self_of_nhds (by simp)
  have heq (V W : (y : N) → TangentSpace (𝓡 n) y)
      (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) (f x)) :
      D.covariantDerivativeOnFields (P V) (P W) =ᶠ[𝓝 x]
        P (D'.covariantDerivativeOnFields V W) := by
    have hd := hf.continuousAt.eventually
      (eventually_mdifferentiableAt_of_contMDiffAt hW)
    have hf2 := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (2 : ℕ∞ω) ≠ ∞)).mp
      (hf.of_le (by norm_cast : (2 : ℕ∞ω) ≤ ∞))
    filter_upwards [hf2, hinv.eventually_nhds, hmetric.eventually_nhds, hd]
      with y hy hi hm hw
    change D.connection (P W) y (P V y) = _
    rw [D.connection_mpullback_of_metric_pullback_of_contMDiffAt_two D' hy hi hm hw]
    simp only [P, mpullback_apply, hi.self_of_nhds.self_apply_inverse,
      covariantDerivativeOnFields]
  have hiter (V W : (y : N) → TangentSpace (𝓡 n) y)
      (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) (f x))
      (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% W) (f x))
      (v : TangentSpace (𝓡 n) x) :
      D.connection (D.covariantDerivativeOnFields (P V) (P W)) x v =
        (mfderiv (𝓡 n) (𝓡 n) f x).inverse
          (D'.connection (D'.covariantDerivativeOnFields V W) (f x)
            (mfderiv (𝓡 n) (𝓡 n) f x v)) := by
    have hc := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((D.contMDiffAt_covariantDerivativeOnFields (hP hV) (hP hW)).mdifferentiableAt
        (by simp))
      ((hP (D'.contMDiffAt_covariantDerivativeOnFields hV hW)).mdifferentiableAt
        (by simp)) (by simp) (heq V W hW)
    rw [congrArg (fun L => L v) hc]
    exact D.connection_mpullback_of_metric_pullback D' hf hinv hmetric
      ((D'.contMDiffAt_covariantDerivativeOnFields hV hW).mdifferentiableAt (by simp)) v
  have hbr := mpullback_mlieBracket (hX.mdifferentiableAt (by simp))
    (hY.mdifferentiableAt (by simp)) hf
      (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  change D.connection (D.covariantDerivativeOnFields (P Y) (P Z)) x (P X x) -
      D.connection (D.covariantDerivativeOnFields (P X) (P Z)) x (P Y x) -
      D.connection (P Z) x (mlieBracket (𝓡 n) (P X) (P Y) x) = _
  rw [hiter Y Z hY hZ, hiter X Z hX hZ, ← hbr,
    D.connection_mpullback_of_metric_pullback D' hf hinv hmetric
      (hZ.mdifferentiableAt (by simp))]
  simp only [P, mpullback_apply, hinv.self_of_nhds.self_apply_inverse,
    curvatureOnFields, map_sub]
  rfl

section EuclideanSource

variable {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem curvature_eq_pullback_euclidean
    (D : LeviCivitaData gE) (D' : LeviCivitaData h)
    {f : EuclideanSpace ℝ (Fin n) → N} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin n),
      gE.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    (u v w : EuclideanSpace ℝ (Fin n)) :
    D.curvature x u v w = (mfderiv (𝓡 n) (𝓡 n) f x).inverse
      (D'.curvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
        (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)) := by
  let A := mfderiv (𝓡 n) (𝓡 n) f x
  let V := fun a : EuclideanSpace ℝ (Fin n) =>
    FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (A a)
  have hV (a : EuclideanSpace ℝ (Fin n)) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% (V a)) (f x) :=
    FiberBundle.contMDiffAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (A a)
  have hP (a : EuclideanSpace ℝ (Fin n)) :
      ContDiffAt ℝ ∞ (mpullback (𝓡 n) (𝓡 n) f (V a)) x :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mp
      ((hV a).mpullback_vectorField_preimage hf hinv.self_of_nhds (by simp))
  have ht := D.curvatureOnFields_mpullback D' hf hinv hmetric (hV u) (hV v) (hV w)
  rw [D.curvatureOnFields_eq_curvature_euclidean (hP u) (hP v) (hP w)] at ht
  simpa only [V, A, mpullback_apply, FiberBundle.extend_apply_self,
    hinv.self_of_nhds.inverse_apply_self, curvature] using ht

theorem curvatureTensor_eq_pullback_euclidean
    (D : LeviCivitaData gE) (D' : LeviCivitaData h)
    {f : EuclideanSpace ℝ (Fin n) → N} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin n),
      gE.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v))
    (u v w z : EuclideanSpace ℝ (Fin n)) :
    D.curvatureTensor x u v w z = D'.curvatureTensor (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v)
      (mfderiv (𝓡 n) (𝓡 n) f x w) (mfderiv (𝓡 n) (𝓡 n) f x z) := by
  unfold curvatureTensor
  rw [D.curvature_eq_pullback_euclidean D' hf hinv hmetric,
    hmetric.self_of_nhds, hinv.self_of_nhds.self_apply_inverse]

theorem curvatureTensorNorm_eq_pullback_euclidean
    (D : LeviCivitaData gE) (D' : LeviCivitaData h)
    {f : EuclideanSpace ℝ (Fin n) → N} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ u v : EuclideanSpace ℝ (Fin n),
      gE.inner y u v = h.inner (f y) (mfderiv (𝓡 n) (𝓡 n) f y u)
        (mfderiv (𝓡 n) (𝓡 n) f y v)) :
    D.curvatureTensorNorm x = D'.curvatureTensorNorm (f x) := by
  obtain ⟨e, he⟩ := hinv.self_of_nhds
  obtain ⟨B, hB⟩ := D.exists_multilinear_curvatureTensor x
  symm
  apply D'.curvatureTensorNorm_eq_of_linearEquiv D (f x) x e.symm.toLinearEquiv
    _ _ B hB
  · intro u v
    rw [hmetric.self_of_nhds, ← he]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply]
  · intro u v w z
    rw [D.curvatureTensor_eq_pullback_euclidean D' hf hinv hmetric, ← he]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
      ContinuousLinearEquiv.apply_symm_apply]

end EuclideanSource

end PoincareConjecture.LeviCivitaData
