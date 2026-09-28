
import PoincareConjecture.Statements.Ch01.CurvatureCalculus
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


noncomputable def covariantDerivativeOnFields (D : LeviCivitaData g)
    (X Y : (x : M) → TangentSpace (𝓡 n) x) (x : M) :=
  D.connection Y x (X x)


noncomputable def curvatureDerivativeOnFields (D : LeviCivitaData g)
    (X Y Z W : (x : M) → TangentSpace (𝓡 n) x) (x : M) :=
  D.connection (D.curvatureOnFields Y Z W) x (X x) -
    D.curvatureOnFields (D.covariantDerivativeOnFields X Y) Z W x -
    D.curvatureOnFields Y (D.covariantDerivativeOnFields X Z) W x -
    D.curvatureOnFields Y Z (D.covariantDerivativeOnFields X W) x

lemma contMDiff_covariantDerivativeOnFields (D : LeviCivitaData g)
    {X Y : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X))
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y)) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (D.covariantDerivativeOnFields X Y)) := by
  have hY' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (∞ + 1) (T% Y) univ := by simpa using hY.contMDiffOn
  have hcov := D.smooth.contMDiff.contMDiff hY'
  exact contMDiffOn_univ.mp (hcov.clm_bundle_apply hX.contMDiffOn)

lemma contMDiff_mlieBracket
    {X Y : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X))
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y)) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (mlieBracket (𝓡 n) X Y)) := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 M)
  have : IsManifold (𝓡 n) (∞ + 1) M := by simpa using
    (inferInstance : IsManifold (𝓡 n) ∞ M)
  intro x
  exact (hX x).mlieBracket_vectorField (hY x) (by simp)

lemma connection_sub (D : LeviCivitaData g)
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    D.connection (X - Y) x = D.connection X x - D.connection Y x := by
  have hneg := mdifferentiableAt_neg_section hY
  have hsum := D.connection.isCovariantDerivativeOn.add hY hneg
  have hz : D.connection (Y + -Y) x = 0 := by
    rw [add_neg_cancel]
    exact D.connection.isCovariantDerivativeOn.zero
  rw [hz] at hsum
  have hn : D.connection (-Y) x = -D.connection Y x :=
    eq_neg_of_add_eq_zero_right hsum.symm
  rw [sub_eq_add_neg, D.connection.isCovariantDerivativeOn.add hX hneg, hn,
    sub_eq_add_neg]

lemma covariantDerivativeOnFields_sub_swap (D : LeviCivitaData g)
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x) :
    D.covariantDerivativeOnFields X Y x - D.covariantDerivativeOnFields Y X x =
      mlieBracket (𝓡 n) X Y x :=
  D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero hX hY

lemma connection_curvatureOnFields (D : LeviCivitaData g)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y))
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z))
    (hW : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W)) :
    D.connection (D.curvatureOnFields Y Z W) x (X x) =
      D.connection (D.covariantDerivativeOnFields Y (D.covariantDerivativeOnFields Z W)) x (X x) -
      D.connection (D.covariantDerivativeOnFields Z (D.covariantDerivativeOnFields Y W)) x (X x) -
      D.connection (D.covariantDerivativeOnFields (mlieBracket (𝓡 n) Y Z) W) x (X x) := by
  have h1 := D.contMDiff_covariantDerivativeOnFields hY
    (D.contMDiff_covariantDerivativeOnFields hZ hW)
  have h2 := D.contMDiff_covariantDerivativeOnFields hZ
    (D.contMDiff_covariantDerivativeOnFields hY hW)
  have h3 := D.contMDiff_covariantDerivativeOnFields (contMDiff_mlieBracket hY hZ) hW
  change D.connection
    (D.covariantDerivativeOnFields Y (D.covariantDerivativeOnFields Z W) -
      D.covariantDerivativeOnFields Z (D.covariantDerivativeOnFields Y W) -
      D.covariantDerivativeOnFields (mlieBracket (𝓡 n) Y Z) W) x (X x) = _
  rw [D.connection_sub ((h1.sub_section h2) x |>.mdifferentiableAt (by simp))
    (h3 x |>.mdifferentiableAt (by simp)),
    D.connection_sub (h1 x |>.mdifferentiableAt (by simp))
      (h2 x |>.mdifferentiableAt (by simp))]
  rfl

lemma connection_torsion_collapse (D : LeviCivitaData g)
    {a A B W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hA : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A))
    (hB : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B))
    (hW : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W)) :
    D.connection (D.covariantDerivativeOnFields (D.covariantDerivativeOnFields A B) W) x (a x) -
      D.connection (D.covariantDerivativeOnFields (D.covariantDerivativeOnFields B A) W) x (a x) -
      D.connection (D.covariantDerivativeOnFields (mlieBracket (𝓡 n) A B) W) x (a x) = 0 := by
  have h1 := D.contMDiff_covariantDerivativeOnFields
    (D.contMDiff_covariantDerivativeOnFields hA hB) hW
  have h2 := D.contMDiff_covariantDerivativeOnFields
    (D.contMDiff_covariantDerivativeOnFields hB hA) hW
  have h3 := D.contMDiff_covariantDerivativeOnFields (contMDiff_mlieBracket hA hB) hW
  have heq : D.covariantDerivativeOnFields (D.covariantDerivativeOnFields A B) W -
      D.covariantDerivativeOnFields (D.covariantDerivativeOnFields B A) W -
      D.covariantDerivativeOnFields (mlieBracket (𝓡 n) A B) W = 0 := by
    funext y
    have ht := D.covariantDerivativeOnFields_sub_swap
      (hA y |>.mdifferentiableAt (by simp)) (hB y |>.mdifferentiableAt (by simp))
    simp only [Pi.sub_apply, Pi.zero_apply, covariantDerivativeOnFields]
    rw [← ht, map_sub]
    simp only [covariantDerivativeOnFields, sub_self]
  have heq' := congrArg (fun S => D.connection S x) heq
  rw [D.connection_sub ((h1.sub_section h2) x |>.mdifferentiableAt (by simp))
      (h3 x |>.mdifferentiableAt (by simp)),
    D.connection_sub (h1 x |>.mdifferentiableAt (by simp))
      (h2 x |>.mdifferentiableAt (by simp)),
    D.connection.isCovariantDerivativeOn.zero] at heq'
  exact congrArg (fun L => L (a x)) heq'

lemma connection_torsion_vector_collapse (D : LeviCivitaData g)
    {A B S : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hA : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) x)
    (hB : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% B) x) :
    D.connection S x (D.covariantDerivativeOnFields A B x) -
      D.connection S x (D.covariantDerivativeOnFields B A x) -
      D.connection S x (mlieBracket (𝓡 n) A B x) = 0 := by
  rw [← D.covariantDerivativeOnFields_sub_swap hA hB, map_sub]
  abel

lemma covariantDerivativeOnFields_eq_swap_add (D : LeviCivitaData g)
    {A B : (x : M) → TangentSpace (𝓡 n) x}
    (hA : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A))
    (hB : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B)) :
    D.covariantDerivativeOnFields A B =
      D.covariantDerivativeOnFields B A + mlieBracket (𝓡 n) A B := by
  funext x
  have ht := D.covariantDerivativeOnFields_sub_swap
    (hA x |>.mdifferentiableAt (by simp)) (hB x |>.mdifferentiableAt (by simp))
  simpa only [Pi.add_apply] using (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)

lemma mlieBracket_covariantDerivative_pair (D : LeviCivitaData g)
    {A B C : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hA : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A))
    (hB : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B)) :
    mlieBracket (𝓡 n) (D.covariantDerivativeOnFields A B) C x +
      mlieBracket (𝓡 n) C (D.covariantDerivativeOnFields B A) x =
      mlieBracket (𝓡 n) (mlieBracket (𝓡 n) A B) C x := by
  rw [mlieBracket_swap_apply (V := C), D.covariantDerivativeOnFields_eq_swap_add hA hB,
    mlieBracket_add_left
      (D.contMDiff_covariantDerivativeOnFields hB hA x |>.mdifferentiableAt (by simp))
      (contMDiff_mlieBracket hA hB x |>.mdifferentiableAt (by simp))]
  abel

lemma bianchi_bracket_sum (D : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X))
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y))
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z)) :
    mlieBracket (𝓡 n) (D.covariantDerivativeOnFields X Y) Z x +
      mlieBracket (𝓡 n) Y (D.covariantDerivativeOnFields X Z) x +
      mlieBracket (𝓡 n) (D.covariantDerivativeOnFields Y Z) X x +
      mlieBracket (𝓡 n) Z (D.covariantDerivativeOnFields Y X) x +
      mlieBracket (𝓡 n) (D.covariantDerivativeOnFields Z X) Y x +
      mlieBracket (𝓡 n) X (D.covariantDerivativeOnFields Z Y) x = 0 := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 3) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 3 M)
  have p1 := D.mlieBracket_covariantDerivative_pair (C := Z) (x := x) hX hY
  have p2 := D.mlieBracket_covariantDerivative_pair (C := Y) (x := x) hZ hX
  have p3 := D.mlieBracket_covariantDerivative_pair (C := X) (x := x) hY hZ
  have hj := leibniz_identity_mlieBracket_apply (I := 𝓡 n)
    ((hX x).of_le (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast))
    ((hY x).of_le (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast))
    ((hZ x).of_le (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast))
  have hn : mlieBracket (𝓡 n) Y (mlieBracket (𝓡 n) X Z) x =
      -mlieBracket (𝓡 n) Y (mlieBracket (𝓡 n) Z X) x := by
    rw [mlieBracket_swap (V := X) (W := Z)]
    rw [show -mlieBracket (𝓡 n) Z X = (-1 : ℝ) • mlieBracket (𝓡 n) Z X by simp]
    rw [mlieBracket_const_smul_right
      (contMDiff_mlieBracket hZ hX x |>.mdifferentiableAt (by simp))]
    simp
  rw [hn] at hj
  rw [mlieBracket_swap_apply (V := mlieBracket (𝓡 n) X Y) (W := Z)] at p1
  rw [mlieBracket_swap_apply (V := mlieBracket (𝓡 n) Z X) (W := Y)] at p2
  rw [mlieBracket_swap_apply (V := mlieBracket (𝓡 n) Y Z) (W := X)] at p3
  rw [mlieBracket_swap_apply (V := mlieBracket (𝓡 n) X Y) (W := Z)] at hj
  linear_combination (norm := abel) p1 + p2 + p3 - hj

lemma curvatureDerivativeOnFields_expand (D : LeviCivitaData g)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y))
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z))
    (hW : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W)) :
    D.curvatureDerivativeOnFields X Y Z W x =
      D.connection (D.covariantDerivativeOnFields Y (D.covariantDerivativeOnFields Z W)) x (X x) -
      D.connection (D.covariantDerivativeOnFields Z (D.covariantDerivativeOnFields Y W)) x (X x) -
      D.connection (D.covariantDerivativeOnFields (mlieBracket (𝓡 n) Y Z) W) x (X x) -
      (D.connection (D.covariantDerivativeOnFields Z W) x (D.covariantDerivativeOnFields X Y x) -
        D.connection (D.covariantDerivativeOnFields (D.covariantDerivativeOnFields X Y) W) x (Z x) -
        D.connection W x (mlieBracket (𝓡 n) (D.covariantDerivativeOnFields X Y) Z x)) -
      (D.connection (D.covariantDerivativeOnFields (D.covariantDerivativeOnFields X Z) W) x (Y x) -
        D.connection (D.covariantDerivativeOnFields Y W) x (D.covariantDerivativeOnFields X Z x) -
        D.connection W x (mlieBracket (𝓡 n) Y (D.covariantDerivativeOnFields X Z) x)) -
      (D.connection (D.covariantDerivativeOnFields Z (D.covariantDerivativeOnFields X W)) x (Y x) -
        D.connection (D.covariantDerivativeOnFields Y (D.covariantDerivativeOnFields X W)) x (Z x) -
        D.connection (D.covariantDerivativeOnFields X W) x (mlieBracket (𝓡 n) Y Z x)) := by
  rw [curvatureDerivativeOnFields, D.connection_curvatureOnFields hY hZ hW]
  rfl


theorem second_bianchi_on_fields (D : LeviCivitaData g)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X))
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y))
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z))
    (hW : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W)) :
    D.curvatureDerivativeOnFields X Y Z W x +
      D.curvatureDerivativeOnFields Y Z X W x +
      D.curvatureDerivativeOnFields Z X Y W x = 0 := by
  rw [D.curvatureDerivativeOnFields_expand hY hZ hW,
    D.curvatureDerivativeOnFields_expand hZ hX hW,
    D.curvatureDerivativeOnFields_expand hX hY hW]
  have g1 := D.connection_torsion_collapse (a := X) (x := x) hY hZ hW
  have g2 := D.connection_torsion_collapse (a := Y) (x := x) hZ hX hW
  have g3 := D.connection_torsion_collapse (a := Z) (x := x) hX hY hW
  have g4 := D.connection_torsion_vector_collapse (S := D.covariantDerivativeOnFields Z W)
    (hX x |>.mdifferentiableAt (by simp)) (hY x |>.mdifferentiableAt (by simp))
  have g5 := D.connection_torsion_vector_collapse (S := D.covariantDerivativeOnFields X W)
    (hY x |>.mdifferentiableAt (by simp)) (hZ x |>.mdifferentiableAt (by simp))
  have g6 := D.connection_torsion_vector_collapse (S := D.covariantDerivativeOnFields Y W)
    (hZ x |>.mdifferentiableAt (by simp)) (hX x |>.mdifferentiableAt (by simp))
  have g7 := congrArg (D.connection W x) (D.bianchi_bracket_sum (x := x) hX hY hZ)
  simp only [map_add, map_zero] at g7
  linear_combination (norm := abel) g1 + g2 + g3 - g4 - g5 - g6 + g7

lemma contMDiff_curvatureOnFields (D : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X))
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y))
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z)) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (D.curvatureOnFields X Y Z)) :=
  ((D.contMDiff_covariantDerivativeOnFields hX
    (D.contMDiff_covariantDerivativeOnFields hY hZ)).sub_section
    (D.contMDiff_covariantDerivativeOnFields hY
      (D.contMDiff_covariantDerivativeOnFields hX hZ))).sub_section
    (D.contMDiff_covariantDerivativeOnFields (contMDiff_mlieBracket hX hY) hZ)

lemma mvfderiv_inner_on_fields (D : LeviCivitaData g)
    (X : (x : M) → TangentSpace (𝓡 n) x)
    {Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x (X x) =
      g.inner x (D.covariantDerivativeOnFields X Y x) (Z x) +
      g.inner x (Y x) (D.covariantDerivativeOnFields X Z x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact D.metricCompatible.mvfderiv_inner_eq X hY hZ


lemma inner_curvatureDerivativeOnFields (D : LeviCivitaData g)
    {X Y Z V W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y))
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z))
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V))
    (hW : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W)) :
    g.inner x (D.curvatureDerivativeOnFields X Y Z W x) (V x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (D.curvatureOnFields Y Z W y) (V y)) x (X x) -
      g.inner x (D.curvatureOnFields (D.covariantDerivativeOnFields X Y) Z W x) (V x) -
      g.inner x (D.curvatureOnFields Y (D.covariantDerivativeOnFields X Z) W x) (V x) -
      g.inner x (D.curvatureOnFields Y Z W x) (D.covariantDerivativeOnFields X V x) -
      g.inner x (D.curvatureOnFields Y Z (D.covariantDerivativeOnFields X W) x) (V x) := by
  rw [D.mvfderiv_inner_on_fields X
    (D.contMDiff_curvatureOnFields hY hZ hW x |>.mdifferentiableAt (by simp))
    (hV x |>.mdifferentiableAt (by simp))]
  simp only [curvatureDerivativeOnFields, map_sub, sub_apply,
    covariantDerivativeOnFields]
  abel


theorem second_bianchi_inner_on_fields (D : LeviCivitaData g)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (v : TangentSpace (𝓡 n) x)
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X))
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y))
    (hZ : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z))
    (hW : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W)) :
    g.inner x (D.curvatureDerivativeOnFields X Y Z W x) v +
      g.inner x (D.curvatureDerivativeOnFields Y Z X W x) v +
      g.inner x (D.curvatureDerivativeOnFields Z X Y W x) v = 0 := by
  have h := congrArg (fun w => g.inner x w v) (D.second_bianchi_on_fields hX hY hZ hW)
  simpa only [map_add, add_apply, map_zero, zero_apply] using h


lemma koszul_identity (D : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) x)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Z) x) :
    2 * g.inner x (D.covariantDerivativeOnFields X Y x) (Z x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (Y y) (Z y)) x (X x) +
      mvfderiv (𝓡 n) (fun y => g.inner y (Z y) (X y)) x (Y x) -
      mvfderiv (𝓡 n) (fun y => g.inner y (X y) (Y y)) x (Z x) +
      g.inner x (mlieBracket (𝓡 n) X Y x) (Z x) -
      g.inner x (mlieBracket (𝓡 n) Y Z x) (X x) +
      g.inner x (mlieBracket (𝓡 n) Z X x) (Y x) := by
  rw [D.mvfderiv_inner_on_fields X hY hZ, D.mvfderiv_inner_on_fields Y hZ hX,
    D.mvfderiv_inner_on_fields Z hX hY,
    ← D.covariantDerivativeOnFields_sub_swap hX hY,
    ← D.covariantDerivativeOnFields_sub_swap hY hZ,
    ← D.covariantDerivativeOnFields_sub_swap hZ hX]
  simp only [map_sub, sub_apply]
  rw [g.symm x (Y x), g.symm x (Z x), g.symm x (X x)]
  ring

lemma contMDiffAt_mvfderiv_apply
    {f : M → ℝ} {X : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => mvfderiv (𝓡 n) f y (X y)) x := by
  have hd := hf.mfderiv_const (m := ∞) (by simp)
  have h := hd.clm_apply_of_inCoordinates hX hf
  rw [contMDiffAt_totalSpace] at h
  convert h.2 using 1
  funext y
  simp only [mvfderiv, ContinuousLinearMap.comp_apply]
  simp
  rfl

lemma eventually_mdifferentiableAt_of_contMDiffAt
    {X : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% X) y := by
  have h1 := hX.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by norm_cast)
  exact ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp h1).mono
    fun y hy => hy.mdifferentiableAt (by simp)

lemma contMDiffAt_mlieBracket
    {X Y : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (mlieBracket (𝓡 n) X Y)) x := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 M)
  have : IsManifold (𝓡 n) (∞ + 1) M := by simpa using
    (inferInstance : IsManifold (𝓡 n) ∞ M)
  exact hX.mlieBracket_vectorField hY (by simp)


lemma contMDiffAt_inner_covariantDerivativeOnFields (D : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (D.covariantDerivativeOnFields X Y y) (Z y)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hi (A B : (x : M) → TangentSpace (𝓡 n) x)
      (hA : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) x)
      (hB : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) x) :
      ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => g.inner y (A y) (B y)) x :=
    hA.inner_bundle hB
  have hs := (((((contMDiffAt_mvfderiv_apply (hi Y Z hY hZ) hX).add
    (contMDiffAt_mvfderiv_apply (hi Z X hZ hX) hY)).sub
    (contMDiffAt_mvfderiv_apply (hi X Y hX hY) hZ)).add
    (hi _ Z (contMDiffAt_mlieBracket hX hY) hZ)).sub
    (hi _ X (contMDiffAt_mlieBracket hY hZ) hX)).add
    (hi _ Y (contMDiffAt_mlieBracket hZ hX) hY)
  have hhalf := (ContinuousLinearMap.lsmul ℝ ℝ (1 / 2 : ℝ)).contDiff.contMDiff.contMDiffAt.comp x hs
  apply hhalf.congr_of_eventuallyEq
  filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hX,
    eventually_mdifferentiableAt_of_contMDiffAt hY,
    eventually_mdifferentiableAt_of_contMDiffAt hZ] with y hyX hyY hyZ
  simp only [Function.comp_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Pi.add_apply]
  linarith [D.koszul_identity hyX hyY hyZ]

end PoincareConjecture.LeviCivitaData
