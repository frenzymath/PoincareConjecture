import PoincareConjecture.Proofs.M13.ConnectionScale
import PoincareConjecture.Proofs.Ch01.Koszul
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] in

theorem diffeomorph_mfderiv_isInvertible
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (x : M) :
    (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible :=
  ⟨f.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩

omit [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] in

theorem diffeomorph_mfderiv_mpullback
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞)
    (V : (y : N) → TangentSpace (𝓡 n) y) (x : M) :
    mfderiv (𝓡 n) (𝓡 n) f x (VectorField.mpullback (𝓡 n) (𝓡 n) f V x) = V (f x) :=
  (diffeomorph_mfderiv_isInvertible f x).self_apply_inverse _

theorem mdifferentiableAt_mpullback
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞)
    (V : (y : N) → TangentSpace (𝓡 n) y) (x : M)
    (hV : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% V) (f x)) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% (VectorField.mpullback (𝓡 n) (𝓡 n) f V)) x :=
  hV.mpullback_vectorField f.contMDiffAt (diffeomorph_mfderiv_isInvertible f x) (by decide)

theorem diffeomorph_mpullback_mlieBracket
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞)
    (V W : (y : N) → TangentSpace (𝓡 n) y) (x : M)
    (hV : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% V) (f x))
    (hW : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% W) (f x)) :
    VectorField.mpullback (𝓡 n) (𝓡 n) f (VectorField.mlieBracket (𝓡 n) V W) x =
      VectorField.mlieBracket (𝓡 n) (VectorField.mpullback (𝓡 n) (𝓡 n) f V)
        (VectorField.mpullback (𝓡 n) (𝓡 n) f W) x := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 M)
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) N := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 N)
  exact VectorField.mpullback_mlieBracket hV hW f.contMDiffAt
    (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)

theorem homothety_inner_mpullback (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hf : MetricHomothety g h f Q)
    (V W : (y : N) → TangentSpace (𝓡 n) y) (x : M) :
    h.inner (f x) (V (f x)) (W (f x)) =
      Q * g.inner x (VectorField.mpullback (𝓡 n) (𝓡 n) f V x)
        (VectorField.mpullback (𝓡 n) (𝓡 n) f W x) := by
  have H := hf x (VectorField.mpullback (𝓡 n) (𝓡 n) f V x)
    (VectorField.mpullback (𝓡 n) (𝓡 n) f W x)
  simpa only [diffeomorph_mfderiv_mpullback] using H

theorem homothety_mvfderiv_inner_mpullback
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hf : MetricHomothety g h f Q)
    (X Y Z : (y : N) → TangentSpace (𝓡 n) y) (x : M)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) (f x))
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) (f x)) :
    mvfderiv (𝓡 n) (fun y ↦ h.inner y (Y y) (Z y)) (f x) (X (f x)) =
      Q * mvfderiv (𝓡 n) (fun p ↦ g.inner p
        (VectorField.mpullback (𝓡 n) (𝓡 n) f Y p)
        (VectorField.mpullback (𝓡 n) (𝓡 n) f Z p)) x
          (VectorField.mpullback (𝓡 n) (𝓡 n) f X x) := by
  have hYZ := metric_inner_mdifferentiableAt h Y Z (f x) hY hZ
  have H := mvfderiv_comp_apply x hYZ (f.mdifferentiable (by simp) x)
    (VectorField.mpullback (𝓡 n) (𝓡 n) f X x)
  rw [diffeomorph_mfderiv_mpullback] at H
  rw [← H]
  have heq : (fun y ↦ h.inner y (Y y) (Z y)) ∘ f =
      (fun p ↦ Q * g.inner p (VectorField.mpullback (𝓡 n) (𝓡 n) f Y p)
        (VectorField.mpullback (𝓡 n) (𝓡 n) f Z p)) :=
    funext (homothety_inner_mpullback g h f Q hf Y Z)
  rw [heq]
  exact mvfderiv_const_mul_metric_inner g Q _ _ x
    (mdifferentiableAt_mpullback f Y x hY) (mdifferentiableAt_mpullback f Z x hZ) _

theorem homothety_connection_pairing_mpullback
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hf : MetricHomothety g h f Q)
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (X Y Z : (y : N) → TangentSpace (𝓡 n) y) (x : M)
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% X) (f x))
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Y) (f x))
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% Z) (f x)) :
    h.inner (f x) (D'.connection Y (f x) (X (f x))) (Z (f x)) =
      Q * g.inner x
        (D.connection (VectorField.mpullback (𝓡 n) (𝓡 n) f Y) x
          (VectorField.mpullback (𝓡 n) (𝓡 n) f X x))
        (VectorField.mpullback (𝓡 n) (𝓡 n) f Z x) := by
  have hK := D.koszul (VectorField.mpullback (𝓡 n) (𝓡 n) f X)
    (VectorField.mpullback (𝓡 n) (𝓡 n) f Y)
    (VectorField.mpullback (𝓡 n) (𝓡 n) f Z)
    (mdifferentiableAt_mpullback f X x hX)
    (mdifferentiableAt_mpullback f Y x hY)
    (mdifferentiableAt_mpullback f Z x hZ)
  have hK' := D'.koszul X Y Z hX hY hZ
  rw [homothety_mvfderiv_inner_mpullback g h f Q hf X Y Z x hY hZ,
    homothety_mvfderiv_inner_mpullback g h f Q hf Y Z X x hZ hX,
    homothety_mvfderiv_inner_mpullback g h f Q hf Z X Y x hX hY,
    homothety_inner_mpullback g h f Q hf (VectorField.mlieBracket (𝓡 n) X Y) Z x,
    homothety_inner_mpullback g h f Q hf Y (VectorField.mlieBracket (𝓡 n) X Z) x,
    homothety_inner_mpullback g h f Q hf X (VectorField.mlieBracket (𝓡 n) Y Z) x,
    diffeomorph_mpullback_mlieBracket f X Y x hX hY,
    diffeomorph_mpullback_mlieBracket f X Z x hX hZ,
    diffeomorph_mpullback_mlieBracket f Y Z x hY hZ] at hK'
  linear_combination (hK' - Q * hK) / 2

theorem homothety_connection_mpullback
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hf : MetricHomothety g h f Q)
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (W : (y : N) → TangentSpace (𝓡 n) y) (x : M)
    (hW : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% W) (f x)) (u : TangentSpace (𝓡 n) x) :
    D'.connection W (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) =
      mfderiv (𝓡 n) (𝓡 n) f x
        (D.connection (VectorField.mpullback (𝓡 n) (𝓡 n) f W) x u) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro v
  change h.inner (f x) (D'.connection W (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)) v =
    h.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x
      (D.connection (VectorField.mpullback (𝓡 n) (𝓡 n) f W) x u)) v
  have hX : VectorField.mpullback (𝓡 n) (𝓡 n) f
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (mfderiv (𝓡 n) (𝓡 n) f x u)) x = u := by
    rw [VectorField.mpullback_apply, FiberBundle.extend_apply_self]
    exact (diffeomorph_mfderiv_isInvertible f x).inverse_apply_self u
  have H := homothety_connection_pairing_mpullback g h f Q hf D D'
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (mfderiv (𝓡 n) (𝓡 n) f x u)) W
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v) x
    (FiberBundle.mdifferentiableAt_extend ..) hW (FiberBundle.mdifferentiableAt_extend ..)
  simp only [FiberBundle.extend_apply_self, hX] at H
  rw [H, ← hf, diffeomorph_mfderiv_mpullback, FiberBundle.extend_apply_self]

theorem homothety_connection_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hf : MetricHomothety g h f Q)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (U : Set M) (hU : IsOpen U)
    (V : (x : M) → TangentSpace (𝓡 n) x) (W : (y : N) → TangentSpace (𝓡 n) y)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U)
    (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% W) (f '' U))
    (hlink : ∀ p ∈ U, W (f p) = mfderiv (𝓡 n) (𝓡 n) f p (V p))
    (x : M) (hx : x ∈ U) (u : TangentSpace (𝓡 n) x) :
    D'.connection W (f x) (mfderiv (𝓡 n) (𝓡 n) f x u) =
      mfderiv (𝓡 n) (𝓡 n) f x (D.connection V x u) := by
  have hVx := (hV.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hWx := (hW.contMDiffAt
    ((f.toHomeomorph.isOpenMap U hU).mem_nhds ⟨x, hx, rfl⟩)).mdifferentiableAt (by simp)
  have heq : VectorField.mpullback (𝓡 n) (𝓡 n) f W =ᶠ[nhds x] V := by
    filter_upwards [hU.mem_nhds hx] with p hp
    rw [VectorField.mpullback_apply, hlink p hp]
    exact (diffeomorph_mfderiv_isInvertible f p).inverse_apply_self (V p)
  have hconn := D.connection.isCovariantDerivativeOn.congr_of_eventuallyEq
    (mdifferentiableAt_mpullback f W x hWx) hVx Filter.univ_mem heq
  rw [homothety_connection_mpullback g h f Q hf D D' W x hWx u, hconn]

end PoincareConjecture.M13
