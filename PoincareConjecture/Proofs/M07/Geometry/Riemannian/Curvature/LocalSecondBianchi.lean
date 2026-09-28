import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.LocalRegularity









set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma connection_curvatureOnFields_local (D : LeviCivitaData g)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
    D.connection (D.curvatureOnFields Y Z W) x (X x) =
      D.connection (D.covariantDerivativeOnFields Y (D.covariantDerivativeOnFields Z W)) x (X x) -
      D.connection (D.covariantDerivativeOnFields Z (D.covariantDerivativeOnFields Y W)) x (X x) -
      D.connection (D.covariantDerivativeOnFields (mlieBracket (𝓡 n) Y Z) W) x (X x) := by
  have h1 := D.contMDiffAt_covariantDerivativeOnFields hY
    (D.contMDiffAt_covariantDerivativeOnFields hZ hW)
  have h2 := D.contMDiffAt_covariantDerivativeOnFields hZ
    (D.contMDiffAt_covariantDerivativeOnFields hY hW)
  have h3 := D.contMDiffAt_covariantDerivativeOnFields (contMDiffAt_mlieBracket hY hZ) hW
  change D.connection
    (D.covariantDerivativeOnFields Y (D.covariantDerivativeOnFields Z W) -
      D.covariantDerivativeOnFields Z (D.covariantDerivativeOnFields Y W) -
      D.covariantDerivativeOnFields (mlieBracket (𝓡 n) Y Z) W) x (X x) = _
  rw [D.connection_sub ((h1.sub_section h2) |>.mdifferentiableAt (by simp))
    (h3 |>.mdifferentiableAt (by simp)),
    D.connection_sub (h1 |>.mdifferentiableAt (by simp))
      (h2 |>.mdifferentiableAt (by simp))]
  rfl

lemma connection_torsion_collapse_local (D : LeviCivitaData g)
    {a A B W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hA : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) x)
    (hB : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
    D.connection (D.covariantDerivativeOnFields (D.covariantDerivativeOnFields A B) W) x (a x) -
      D.connection (D.covariantDerivativeOnFields (D.covariantDerivativeOnFields B A) W) x (a x) -
      D.connection (D.covariantDerivativeOnFields (mlieBracket (𝓡 n) A B) W) x (a x) = 0 := by
  have h1 := D.contMDiffAt_covariantDerivativeOnFields
    (D.contMDiffAt_covariantDerivativeOnFields hA hB) hW
  have h2 := D.contMDiffAt_covariantDerivativeOnFields
    (D.contMDiffAt_covariantDerivativeOnFields hB hA) hW
  have h3 := D.contMDiffAt_covariantDerivativeOnFields (contMDiffAt_mlieBracket hA hB) hW
  have heq : D.covariantDerivativeOnFields (D.covariantDerivativeOnFields A B) W -
      D.covariantDerivativeOnFields (D.covariantDerivativeOnFields B A) W =ᶠ[𝓝 x]
      D.covariantDerivativeOnFields (mlieBracket (𝓡 n) A B) W := by
    filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hA,
      eventually_mdifferentiableAt_of_contMDiffAt hB] with y hyA hyB
    have ht := D.covariantDerivativeOnFields_sub_swap hyA hyB
    simp only [Pi.sub_apply, covariantDerivativeOnFields]
    rw [← ht, map_sub]
    rfl
  have heq' := D.connection.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((h1.sub_section h2).mdifferentiableAt (by simp))
    (h3.mdifferentiableAt (by simp)) (by simp) heq
  rw [D.connection_sub (h1.mdifferentiableAt (by simp))
      (h2.mdifferentiableAt (by simp))] at heq'
  exact sub_eq_zero.mpr (congrArg (fun L => L (a x)) heq')

lemma mlieBracket_covariantDerivative_pair_local (D : LeviCivitaData g)
    {A B C : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hA : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) x)
    (hB : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) x) :
    mlieBracket (𝓡 n) (D.covariantDerivativeOnFields A B) C x +
      mlieBracket (𝓡 n) C (D.covariantDerivativeOnFields B A) x =
      mlieBracket (𝓡 n) (mlieBracket (𝓡 n) A B) C x := by
  have heq : ∀ᶠ y in 𝓝 x, D.covariantDerivativeOnFields A B y =
      D.covariantDerivativeOnFields B A y + mlieBracket (𝓡 n) A B y := by
    filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hA,
      eventually_mdifferentiableAt_of_contMDiffAt hB] with y hyA hyB
    have ht := D.covariantDerivativeOnFields_sub_swap hyA hyB
    simpa only [Pi.add_apply] using (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)
  rw [mlieBracket_swap_apply (V := C),
    Filter.EventuallyEq.mlieBracket_vectorField_eq (I := 𝓡 n)
      (V₁ := D.covariantDerivativeOnFields A B)
      (V := D.covariantDerivativeOnFields B A + mlieBracket (𝓡 n) A B)
      (W₁ := C) (W := C) heq (Filter.EventuallyEq.rfl),
    mlieBracket_add_left
      ((D.contMDiffAt_covariantDerivativeOnFields hB hA).mdifferentiableAt (by simp))
      ((contMDiffAt_mlieBracket hA hB).mdifferentiableAt (by simp))]
  abel

lemma bianchi_bracket_sum_local (D : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    mlieBracket (𝓡 n) (D.covariantDerivativeOnFields X Y) Z x +
      mlieBracket (𝓡 n) Y (D.covariantDerivativeOnFields X Z) x +
      mlieBracket (𝓡 n) (D.covariantDerivativeOnFields Y Z) X x +
      mlieBracket (𝓡 n) Z (D.covariantDerivativeOnFields Y X) x +
      mlieBracket (𝓡 n) (D.covariantDerivativeOnFields Z X) Y x +
      mlieBracket (𝓡 n) X (D.covariantDerivativeOnFields Z Y) x = 0 := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 3) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 3 M)
  have p1 := D.mlieBracket_covariantDerivative_pair_local (C := Z) (x := x) hX hY
  have p2 := D.mlieBracket_covariantDerivative_pair_local (C := Y) (x := x) hZ hX
  have p3 := D.mlieBracket_covariantDerivative_pair_local (C := X) (x := x) hY hZ
  have hj := leibniz_identity_mlieBracket_apply (I := 𝓡 n)
    ((hX).of_le (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast))
    ((hY).of_le (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast))
    ((hZ).of_le (show minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) by
      rw [minSmoothness_of_isRCLikeNormedField]; norm_cast))
  have hn : mlieBracket (𝓡 n) Y (mlieBracket (𝓡 n) X Z) x =
      -mlieBracket (𝓡 n) Y (mlieBracket (𝓡 n) Z X) x := by
    rw [mlieBracket_swap (V := X) (W := Z)]
    rw [show -mlieBracket (𝓡 n) Z X = (-1 : ℝ) • mlieBracket (𝓡 n) Z X by simp]
    rw [mlieBracket_const_smul_right
      (contMDiffAt_mlieBracket hZ hX |>.mdifferentiableAt (by simp))]
    simp
  rw [hn] at hj
  rw [mlieBracket_swap_apply (V := mlieBracket (𝓡 n) X Y) (W := Z)] at p1
  rw [mlieBracket_swap_apply (V := mlieBracket (𝓡 n) Z X) (W := Y)] at p2
  rw [mlieBracket_swap_apply (V := mlieBracket (𝓡 n) Y Z) (W := X)] at p3
  rw [mlieBracket_swap_apply (V := mlieBracket (𝓡 n) X Y) (W := Z)] at hj
  linear_combination (norm := abel) p1 + p2 + p3 - hj

lemma curvatureDerivativeOnFields_expand_local (D : LeviCivitaData g)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
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
  rw [curvatureDerivativeOnFields, D.connection_curvatureOnFields_local hY hZ hW]
  rfl


theorem second_bianchi_on_fields_local (D : LeviCivitaData g)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
    D.curvatureDerivativeOnFields X Y Z W x +
      D.curvatureDerivativeOnFields Y Z X W x +
      D.curvatureDerivativeOnFields Z X Y W x = 0 := by
  rw [D.curvatureDerivativeOnFields_expand_local hY hZ hW,
    D.curvatureDerivativeOnFields_expand_local hZ hX hW,
    D.curvatureDerivativeOnFields_expand_local hX hY hW]
  have g1 := D.connection_torsion_collapse_local (a := X) (x := x) hY hZ hW
  have g2 := D.connection_torsion_collapse_local (a := Y) (x := x) hZ hX hW
  have g3 := D.connection_torsion_collapse_local (a := Z) (x := x) hX hY hW
  have g4 := D.connection_torsion_vector_collapse (S := D.covariantDerivativeOnFields Z W)
    (hX |>.mdifferentiableAt (by simp)) (hY |>.mdifferentiableAt (by simp))
  have g5 := D.connection_torsion_vector_collapse (S := D.covariantDerivativeOnFields X W)
    (hY |>.mdifferentiableAt (by simp)) (hZ |>.mdifferentiableAt (by simp))
  have g6 := D.connection_torsion_vector_collapse (S := D.covariantDerivativeOnFields Y W)
    (hZ |>.mdifferentiableAt (by simp)) (hX |>.mdifferentiableAt (by simp))
  have g7 := congrArg (D.connection W x) (D.bianchi_bracket_sum_local (x := x) hX hY hZ)
  simp only [map_add, map_zero] at g7
  linear_combination (norm := abel) g1 + g2 + g3 - g4 - g5 - g6 + g7

lemma contMDiffAt_curvatureOnFields (D : LeviCivitaData g)
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (D.curvatureOnFields X Y Z)) x :=
  ((D.contMDiffAt_covariantDerivativeOnFields hX
    (D.contMDiffAt_covariantDerivativeOnFields hY hZ)).sub_section
    (D.contMDiffAt_covariantDerivativeOnFields hY
      (D.contMDiffAt_covariantDerivativeOnFields hX hZ))).sub_section
    (D.contMDiffAt_covariantDerivativeOnFields (contMDiffAt_mlieBracket hX hY) hZ)


lemma inner_curvatureDerivativeOnFields_local (D : LeviCivitaData g)
    {X Y Z V W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x)
    (hV : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
    g.inner x (D.curvatureDerivativeOnFields X Y Z W x) (V x) =
      mvfderiv (𝓡 n) (fun y => g.inner y (D.curvatureOnFields Y Z W y) (V y)) x (X x) -
      g.inner x (D.curvatureOnFields (D.covariantDerivativeOnFields X Y) Z W x) (V x) -
      g.inner x (D.curvatureOnFields Y (D.covariantDerivativeOnFields X Z) W x) (V x) -
      g.inner x (D.curvatureOnFields Y Z W x) (D.covariantDerivativeOnFields X V x) -
      g.inner x (D.curvatureOnFields Y Z (D.covariantDerivativeOnFields X W) x) (V x) := by
  rw [D.mvfderiv_inner_on_fields X
    (D.contMDiffAt_curvatureOnFields hY hZ hW |>.mdifferentiableAt (by simp))
    (hV |>.mdifferentiableAt (by simp))]
  simp only [curvatureDerivativeOnFields, map_sub, sub_apply,
    covariantDerivativeOnFields]
  abel


theorem second_bianchi_inner_on_fields_local (D : LeviCivitaData g)
    {X Y Z W : (x : M) → TangentSpace (𝓡 n) x} {x : M}
    (v : TangentSpace (𝓡 n) x)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x)
    (hW : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) x) :
    g.inner x (D.curvatureDerivativeOnFields X Y Z W x) v +
      g.inner x (D.curvatureDerivativeOnFields Y Z X W x) v +
      g.inner x (D.curvatureDerivativeOnFields Z X Y W x) v = 0 := by
  have h := congrArg (fun w => g.inner x w v) (D.second_bianchi_on_fields_local hX hY hZ hW)
  simpa only [map_add, add_apply, map_zero, zero_apply] using h


end PoincareConjecture.LeviCivitaData
