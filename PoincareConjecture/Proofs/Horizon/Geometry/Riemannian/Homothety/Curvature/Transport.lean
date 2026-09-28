import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Connection.Transport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Connection.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Curvature.Extensions
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Basic











set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Homothety

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N]


theorem contMDiffOn_mpullback (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞)
    (U : Set M) (V : (y : N) → TangentSpace (𝓡 n) y)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% V) (f '' U)) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (VectorField.mpullback (𝓡 n) (𝓡 n) f V)) U := by
  apply (hV.mpullback_vectorField_preimage f.contMDiff
    (fun x _ ↦ diffeomorph_mfderiv_isInvertible f x) (by decide)).mono
  intro p hp
  exact ⟨p, hp, rfl⟩

variable [T2Space M] [T2Space N]


theorem homothety_iterated_connection_mpullback
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hf : MetricHomothety g h f Q)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (U : Set M) (hU : IsOpen U)
    (Y Z : (y : N) → TangentSpace (𝓡 n) y)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% Y) (f '' U))
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% Z) (f '' U)) (x : M) (hx : x ∈ U) (u : TangentSpace (𝓡 n) x) :
    D'.connection (fun y ↦ D'.connection Z y (Y y)) (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x u) =
        mfderiv (𝓡 n) (𝓡 n) f x
          (D.connection (fun p ↦ D.connection (VectorField.mpullback (𝓡 n) (𝓡 n) f Z) p
            (VectorField.mpullback (𝓡 n) (𝓡 n) f Y p)) x u) := by
  have hU' : IsOpen (f '' U) := f.toHomeomorph.isOpenMap U hU
  apply homothety_connection_eq g h f Q hf D D' U hU
    (fun p ↦ D.connection (VectorField.mpullback (𝓡 n) (𝓡 n) f Z) p
      (VectorField.mpullback (𝓡 n) (𝓡 n) f Y p))
    (fun y ↦ D'.connection Z y (Y y))
    (connection_apply_contMDiffOn g D U hU _ _
      (contMDiffOn_mpullback f U Y hY) (contMDiffOn_mpullback f U Z hZ))
    (connection_apply_contMDiffOn h D' (f '' U) hU' Y Z hY hZ) _ x hx u
  intro p hp
  have hZp := (hZ.contMDiffAt (hU'.mem_nhds ⟨p, hp, rfl⟩)).mdifferentiableAt (by simp)
  simpa only [diffeomorph_mfderiv_mpullback] using
    homothety_connection_mpullback g h f Q hf D D' Z p hZp
      (VectorField.mpullback (𝓡 n) (𝓡 n) f Y p)


theorem homothety_curvatureOnFields_mpullback
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hf : MetricHomothety g h f Q)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (U : Set M) (hU : IsOpen U)
    (X Y Z : (y : N) → TangentSpace (𝓡 n) y)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% X) (f '' U))
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% Y) (f '' U))
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% Z) (f '' U)) (x : M) (hx : x ∈ U) :
    D'.curvatureOnFields X Y Z (f x) =
      mfderiv (𝓡 n) (𝓡 n) f x
        (D.curvatureOnFields (VectorField.mpullback (𝓡 n) (𝓡 n) f X)
          (VectorField.mpullback (𝓡 n) (𝓡 n) f Y)
          (VectorField.mpullback (𝓡 n) (𝓡 n) f Z) x) := by
  have hU' : IsOpen (f '' U) := f.toHomeomorph.isOpenMap U hU
  have hXx := (hX.contMDiffAt (hU'.mem_nhds ⟨x, hx, rfl⟩)).mdifferentiableAt (by simp)
  have hYx := (hY.contMDiffAt (hU'.mem_nhds ⟨x, hx, rfl⟩)).mdifferentiableAt (by simp)
  have hZx := (hZ.contMDiffAt (hU'.mem_nhds ⟨x, hx, rfl⟩)).mdifferentiableAt (by simp)
  unfold LeviCivitaData.curvatureOnFields
  rw [← diffeomorph_mfderiv_mpullback f X x,
    homothety_iterated_connection_mpullback g h f Q hf D D' U hU Y Z hY hZ x hx,
    ← diffeomorph_mfderiv_mpullback f Y x,
    homothety_iterated_connection_mpullback g h f Q hf D D' U hU X Z hX hZ x hx,
    ← diffeomorph_mfderiv_mpullback f (VectorField.mlieBracket (𝓡 n) X Y) x,
    homothety_connection_mpullback g h f Q hf D D' Z x hZx,
    diffeomorph_mpullback_mlieBracket f X Y x hXx hYx, map_sub, map_sub]


theorem homothety_curvature_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hf : MetricHomothety g h f Q)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M)
    (u v w : TangentSpace (𝓡 n) x) :
    D'.curvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
      (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w) =
        mfderiv (𝓡 n) (𝓡 n) f x (D.curvature x u v w) := by
  obtain ⟨V, hV, hxV, hX, hY, hZ⟩ := exists_open_smooth_extensions (f x)
    (mfderiv (𝓡 n) (𝓡 n) f x u) (mfderiv (𝓡 n) (𝓡 n) f x v)
    (mfderiv (𝓡 n) (𝓡 n) f x w)
  let U := f ⁻¹' V
  have hU : IsOpen U := hV.preimage f.continuous
  have hUV : f '' U = V := Set.image_preimage_eq V f.surjective
  rw [← hUV] at hX hY hZ
  have HP := homothety_curvatureOnFields_mpullback g h f Q hf D D' U hU
    _ _ _ hX hY hZ x hxV
  have HC := curvature_eq_curvatureOnFields D U hU _ _ _
    (contMDiffOn_mpullback f U _ hX) (contMDiffOn_mpullback f U _ hY)
    (contMDiffOn_mpullback f U _ hZ) x hxV
  have hpull (a : TangentSpace (𝓡 n) x) :
      VectorField.mpullback (𝓡 n) (𝓡 n) f
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (mfderiv (𝓡 n) (𝓡 n) f x a)) x = a := by
    change (mfderiv (𝓡 n) (𝓡 n) f x).inverse
      (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (mfderiv (𝓡 n) (𝓡 n) f x a) (f x)) = a
    rw [FiberBundle.extend_apply_self]
    exact (diffeomorph_mfderiv_isInvertible f x).inverse_apply_self a
  rw [hpull, hpull, hpull] at HC
  exact HP.trans (congrArg (mfderiv (𝓡 n) (𝓡 n) f x) HC.symm)


theorem homothety_curvatureTensor_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hf : MetricHomothety g h f Q)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D'.curvatureTensor (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
      (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)
      (mfderiv (𝓡 n) (𝓡 n) f x z) = Q * D.curvatureTensor x u v w z := by
  unfold LeviCivitaData.curvatureTensor
  rw [homothety_curvature_eq g h f Q hf D D', hf]


theorem homothety_sectionalCurvature_eq
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (D : LeviCivitaData g) (D' : LeviCivitaData h) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    D'.sectionalCurvature (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
      (mfderiv (𝓡 n) (𝓡 n) f x v) = D.sectionalCurvature x u v / Q := by
  unfold LeviCivitaData.sectionalCurvature
  rw [homothety_curvatureTensor_eq g h f Q hf D D', hf, hf, hf]
  rw [show (Q * g.inner x u u) * (Q * g.inner x v v) - (Q * g.inner x u v) ^ 2 =
    Q * (Q * (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)) by ring]
  rw [mul_div_mul_left _ _ hQ.ne', div_mul_eq_div_div, div_right_comm]

end PoincareConjecture.Homothety
