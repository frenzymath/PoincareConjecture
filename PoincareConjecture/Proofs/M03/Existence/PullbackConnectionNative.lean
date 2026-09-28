import PoincareConjecture.Proofs.M03.Existence.PullbackMetricNative
import PoincareConjecture.Proofs.Ch01.Koszul
import PoincareConjecture.Proofs.M03.CurvatureExtension
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

noncomputable section

universe u

namespace PoincareConjecture.DiffeomorphNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "Vec" => EuclideanSpace ℝ (Fin n)

def pullField (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (Y : (x : M) → TangentSpace (𝓡 n) x) :
    (x : M) → TangentSpace (𝓡 n) x :=
  VectorField.mpullback (𝓡 n) (𝓡 n) Φ Y

theorem mfderiv_isInvertible (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) (x : M) :
    (mfderiv (𝓡 n) (𝓡 n) Φ x).IsInvertible := by
  exact ⟨Φ.mfderivToContinuousLinearEquiv (by simp) x, rfl⟩

theorem mfderiv_pullField (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (Y : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    mfderiv (𝓡 n) (𝓡 n) Φ x (pullField Φ Y x) = Y (Φ x) := by
  exact (mfderiv_isInvertible Φ x).self_apply_inverse _

theorem mdifferentiableAt_pullField
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% Y) (Φ x)) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec))
      (T% (pullField Φ Y)) x := by
  exact hY.mpullback_vectorField (Φ.contMDiffAt) (mfderiv_isInvertible Φ x)
    (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

theorem contMDiffOn_pullField
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    {Y : (x : M) → TangentSpace (𝓡 n) x} {U : Set M}
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% Y) U) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞
      (T% (pullField Φ Y)) (Φ ⁻¹' U) :=
  hY.mpullback_vectorField_preimage Φ.contMDiff
    (fun x _ => mfderiv_isInvertible Φ x) (by simp)

theorem pullField_mlieBracket
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% X) (Φ x))
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% Y) (Φ x)) :
    pullField Φ (VectorField.mlieBracket (𝓡 n) X Y) x =
      VectorField.mlieBracket (𝓡 n) (pullField Φ X) (pullField Φ Y) x := by
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞)
      (by simpa using (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
  exact VectorField.mpullback_mlieBracket hX hY (Φ.contMDiffAt)
    (by simpa using (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))

variable (g : RiemannianMetric n M)
  (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)

theorem pullbackMetric_pullField_inner
    (hsmooth : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, Vec →L[ℝ] Vec →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (Vec →L[ℝ] Vec →L[ℝ] ℝ) x (pinner g Φ x)))
    (Y Z : (x : M) → TangentSpace (𝓡 n) x) (x : M) :
    (pullbackMetric g Φ hsmooth).inner x (pullField Φ Y x) (pullField Φ Z x) =
      g.inner (Φ x) (Y (Φ x)) (Z (Φ x)) := by
  rw [pullbackMetric_inner, mfderiv_pullField, mfderiv_pullField]

theorem pullbackMetric_mvfderiv_inner
    (hsmooth : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, Vec →L[ℝ] Vec →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (Vec →L[ℝ] Vec →L[ℝ] ℝ) x (pinner g Φ x)))
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% Y) (Φ x))
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% Z) (Φ x)) :
    mvfderiv (𝓡 n) (fun y => (pullbackMetric g Φ hsmooth).inner y
        (pullField Φ Y y) (pullField Φ Z y)) x (pullField Φ X x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) (Φ x) (X (Φ x)) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hpair : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => g.inner y (Y y) (Z y)) (Φ x) := hY.inner_bundle hZ
  have heq : (fun y => (pullbackMetric g Φ hsmooth).inner y
      (pullField Φ Y y) (pullField Φ Z y)) =
      (fun y => g.inner y (Y y) (Z y)) ∘ Φ := by
    funext y
    exact pullbackMetric_pullField_inner g Φ hsmooth Y Z y
  rw [heq, mvfderiv_comp_apply x hpair (Φ.mdifferentiable (by simp) x),
    mfderiv_pullField]

theorem connection_pullField
    (hsmooth : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, Vec →L[ℝ] Vec →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (Vec →L[ℝ] Vec →L[ℝ] ℝ) x (pinner g Φ x)))
    (D : LeviCivitaData g) (P : LeviCivitaData (pullbackMetric g Φ hsmooth))
    (X Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% X) (Φ x))
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% Y) (Φ x)) :
    mfderiv (𝓡 n) (𝓡 n) Φ x
      (P.connection (pullField Φ Y) x (pullField Φ X x)) =
      D.connection Y (Φ x) (X (Φ x)) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro z
  let Z : (y : M) → TangentSpace (𝓡 n) y := FiberBundle.extend Vec z
  have hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% Z) (Φ x) :=
    FiberBundle.mdifferentiableAt_extend (𝓡 n) Vec z
  have hZx : Z (Φ x) = z := FiberBundle.extend_apply_self Vec z
  have hp := P.koszul (pullField Φ X) (pullField Φ Y) (pullField Φ Z)
    (mdifferentiableAt_pullField Φ hX) (mdifferentiableAt_pullField Φ hY)
    (mdifferentiableAt_pullField Φ hZ)
  have hg := D.koszul X Y Z hX hY hZ
  rw [pullbackMetric_mvfderiv_inner g Φ hsmooth X Y Z hY hZ,
    pullbackMetric_mvfderiv_inner g Φ hsmooth Y Z X hZ hX,
    pullbackMetric_mvfderiv_inner g Φ hsmooth Z X Y hX hY,
    ← pullField_mlieBracket Φ hX hY,
    ← pullField_mlieBracket Φ hX hZ,
    ← pullField_mlieBracket Φ hY hZ] at hp
  simp_rw [pullbackMetric_pullField_inner g Φ hsmooth] at hp
  rw [pullbackMetric_inner] at hp
  rw [mfderiv_pullField, hZx] at hp
  rw [hZx] at hg
  change g.inner (Φ x)
      (mfderiv (𝓡 n) (𝓡 n) Φ x
        (P.connection (pullField Φ Y) x (pullField Φ X x))) z =
    g.inner (Φ x) (D.connection Y (Φ x) (X (Φ x))) z
  linarith only [hp, hg]

theorem pullField_connection
    (hPull : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, Vec →L[ℝ] Vec →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (Vec →L[ℝ] Vec →L[ℝ] ℝ) x (pinner g Φ x)))
    (D : LeviCivitaData g) (P : LeviCivitaData (pullbackMetric g Φ hPull))
    (X Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% X) (Φ x))
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% Y) (Φ x)) :
    pullField Φ (fun y => D.connection Y y (X y)) x =
      P.connection (pullField Φ Y) x (pullField Φ X x) := by
  apply (Φ.mfderivToContinuousLinearEquiv (by simp) x).injective
  change mfderiv (𝓡 n) (𝓡 n) Φ x
      (pullField Φ (fun y => D.connection Y y (X y)) x) =
    mfderiv (𝓡 n) (𝓡 n) Φ x (P.connection (pullField Φ Y) x (pullField Φ X x))
  rw [mfderiv_pullField]
  exact (connection_pullField g Φ hPull D P X Y hX hY).symm

theorem connection_pullField_apply
    (hPull : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, Vec →L[ℝ] Vec →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (Vec →L[ℝ] Vec →L[ℝ] ℝ) x (pinner g Φ x)))
    (D : LeviCivitaData g) (P : LeviCivitaData (pullbackMetric g Φ hPull))
    (Y : (x : M) → TangentSpace (𝓡 n) x) {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% Y) (Φ x))
    (v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) (𝓡 n) Φ x (P.connection (pullField Φ Y) x v) =
      D.connection Y (Φ x) (mfderiv (𝓡 n) (𝓡 n) Φ x v) := by
  let X : (y : M) → TangentSpace (𝓡 n) y :=
    FiberBundle.extend Vec (mfderiv (𝓡 n) (𝓡 n) Φ x v)
  have hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% X) (Φ x) :=
    FiberBundle.mdifferentiableAt_extend (𝓡 n) Vec _
  have hXx : X (Φ x) = mfderiv (𝓡 n) (𝓡 n) Φ x v := FiberBundle.extend_apply_self Vec _
  have hpX : pullField Φ X x = v := by
    apply (Φ.mfderivToContinuousLinearEquiv (by simp) x).injective
    exact (mfderiv_pullField Φ X x).trans hXx
  simpa only [hpX, hXx] using connection_pullField g Φ hPull D P X Y hX hY

theorem curvatureOnFields_pullField
    (hPull : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, Vec →L[ℝ] Vec →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (Vec →L[ℝ] Vec →L[ℝ] ℝ) x (pinner g Φ x)))
    (D : LeviCivitaData g) (P : LeviCivitaData (pullbackMetric g Φ hPull))
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% Z) U)
    {x : M} (hx : Φ x ∈ U) :
    mfderiv (𝓡 n) (𝓡 n) Φ x
      (P.curvatureOnFields (pullField Φ X) (pullField Φ Y) (pullField Φ Z) x) =
        D.curvatureOnFields X Y Z (Φ x) := by
  have hpre : IsOpen (Φ ⁻¹' U) := hU.preimage Φ.continuous
  have hpx : x ∈ Φ ⁻¹' U := hx
  have hpZ := contMDiffOn_pullField Φ hZ
  have hmd (A : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% A) U)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) (T% A) y :=
    (hA.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hsecond (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% B) U) :
      mfderiv (𝓡 n) (𝓡 n) Φ x
        (P.connection (fun y => P.connection (pullField Φ Z) y (pullField Φ B y)) x
          (pullField Φ A x)) =
        D.connection (fun y => D.connection Z y (B y)) (Φ x) (A (Φ x)) := by
    have hDZ := D.contMDiffOn_connection_apply hU B Z hB hZ
    have hpDZ := contMDiffOn_pullField Φ hDZ
    have hPZ := P.contMDiffOn_connection_apply hpre (pullField Φ B) (pullField Φ Z)
      (contMDiffOn_pullField Φ hB) hpZ
    have hconn :
        P.connection (fun y => P.connection (pullField Φ Z) y (pullField Φ B y)) x =
          P.connection (pullField Φ (fun y => D.connection Z y (B y))) x := by
      apply P.connection.isCovariantDerivativeOn.congr_of_eqOn
        ((hPZ.contMDiffAt (hpre.mem_nhds hpx)).mdifferentiableAt (by simp))
        ((hpDZ.contMDiffAt (hpre.mem_nhds hpx)).mdifferentiableAt (by simp))
        (hpre.mem_nhds hpx)
      intro y hy
      exact (pullField_connection g Φ hPull D P B Z (hmd B hB hy) (hmd Z hZ hy)).symm
    rw [hconn]
    exact connection_pullField g Φ hPull D P A _ (hmd A hA hx) (hmd _ hDZ hx)
  have hbracket : mfderiv (𝓡 n) (𝓡 n) Φ x
      (VectorField.mlieBracket (𝓡 n) (pullField Φ X) (pullField Φ Y) x) =
        VectorField.mlieBracket (𝓡 n) X Y (Φ x) := by
    rw [← pullField_mlieBracket Φ (hmd X hX hx) (hmd Y hY hx), mfderiv_pullField]
  unfold LeviCivitaData.curvatureOnFields
  rw [map_sub, map_sub, hsecond X Y hX hY, hsecond Y X hY hX,
    connection_pullField_apply g Φ hPull D P Z (hmd Z hZ hx), hbracket]

theorem curvature_pullback
    (hPull : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, Vec →L[ℝ] Vec →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (Vec →L[ℝ] Vec →L[ℝ] ℝ) x (pinner g Φ x)))
    (D : LeviCivitaData g) (P : LeviCivitaData (pullbackMetric g Φ hPull))
    (x : M) (u v w : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) (𝓡 n) Φ x (P.curvature x u v w) =
      D.curvature (Φ x) (mfderiv (𝓡 n) (𝓡 n) Φ x u)
        (mfderiv (𝓡 n) (𝓡 n) Φ x v) (mfderiv (𝓡 n) (𝓡 n) Φ x w) := by
  let A := Φ.mfderivToContinuousLinearEquiv (by simp) x
  let X := FiberBundle.extend Vec (A u)
  let Y := FiberBundle.extend Vec (A v)
  let Z := FiberBundle.extend Vec (A w)
  obtain ⟨Ux, hUx, hX⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) Vec (A u)
  obtain ⟨Uy, hUy, hY⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) Vec (A v)
  obtain ⟨Uz, hUz, hZ⟩ := FiberBundle.exists_contMDiffOn_extend (k := ∞) (𝓡 n) Vec (A w)
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (inter_mem hUx (inter_mem hUy hUz))
  have hXU : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% X) U :=
    hX.mono (fun _ hy => (hUsub hy).1)
  have hYU : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% Y) U :=
    hY.mono (fun _ hy => (hUsub hy).2.1)
  have hZU : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, Vec)) ∞ (T% Z) U :=
    hZ.mono (fun _ hy => (hUsub hy).2.2)
  have hpX : pullField Φ X x = u := by
    apply A.injective
    exact (mfderiv_pullField Φ X x).trans (FiberBundle.extend_apply_self Vec _)
  have hpY : pullField Φ Y x = v := by
    apply A.injective
    exact (mfderiv_pullField Φ Y x).trans (FiberBundle.extend_apply_self Vec _)
  have hpZ : pullField Φ Z x = w := by
    apply A.injective
    exact (mfderiv_pullField Φ Z x).trans (FiberBundle.extend_apply_self Vec _)
  have hpcurv := Proofs.M03.curvature_eq_curvatureOnFields P (hU.preimage Φ.continuous)
    (pullField Φ X) (pullField Φ Y) (pullField Φ Z)
    (contMDiffOn_pullField Φ hXU) (contMDiffOn_pullField Φ hYU) (contMDiffOn_pullField Φ hZU)
    (show x ∈ Φ ⁻¹' U from hxU)
  rw [hpX, hpY, hpZ] at hpcurv
  rw [hpcurv, curvatureOnFields_pullField g Φ hPull D P hU X Y Z hXU hYU hZU hxU,
    ← Proofs.M03.curvature_eq_curvatureOnFields D hU X Y Z hXU hYU hZU hxU]
  simp only [X, Y, Z, FiberBundle.extend_apply_self, A,
    Diffeomorph.mfderivToContinuousLinearEquiv_coe]
  rfl

end PoincareConjecture.DiffeomorphNative
