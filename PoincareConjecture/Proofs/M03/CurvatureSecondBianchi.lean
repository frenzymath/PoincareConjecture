import PoincareConjecture.Proofs.M03.CurvatureTensoriality

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureOnFields_second_bianchi
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y Z W : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U)
    {x : M} (hx : x ∈ U) :
    let dR := fun
        (A B C E : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection (fun z => D.curvatureOnFields B C E z) y (A y) -
        D.curvatureOnFields
          (fun z => D.connection B z (A z)) C E y -
        D.curvatureOnFields B
          (fun z => D.connection C z (A z)) E y -
        D.curvatureOnFields B C
          (fun z => D.connection E z (A z)) y
    dR X Y Z W x + dR Y Z X W x + dR Z X Y W x = 0 := by
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 3) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (3 : ℕ∞ω))))
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection B y (A y)
  let L := VectorField.mlieBracket (𝓡 n) (M := M)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let S := fun A : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  have hmd (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) y :=
    (hA.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hU A B hA hB
  have hL (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (L A B) := by
    intro y hy
    exact ((hA.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
      (hB.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤) (by simp)).contMDiffWithinAt
  have htors (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : N A B x - N B A x = L A B x :=
    (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
      (hmd A hA hx) (hmd B hB hx)
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hsub (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (v : TangentSpace (𝓡 n) x) :
      D.connection (A - B) x v = D.connection A x v - D.connection B x v := by
    have heq := congrArg (fun C => C v)
      (hc.add (hmd _ (hA.sub_section hB) hx) (hmd B hB hx))
    rw [sub_add_cancel] at heq
    exact eq_sub_iff_add_eq.mpr heq.symm
  have houter (A B C E : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (hE : S E) :
      N A (R B C E) x = N A (N B (N C E)) x -
        N A (N C (N B E)) x - N A (N (L B C) E) x := by
    change D.connection ((N B (N C E) - N C (N B E)) - N (L B C) E)
      x (A x) = _
    rw [hsub _ _ ((hN B _ hB (hN C E hC hE)).sub_section
      (hN C _ hC (hN B E hB hE))) (hN _ E (hL B C hB hC) hE),
      hsub _ _ (hN B _ hB (hN C E hC hE)) (hN C _ hC (hN B E hB hE))]
  have htwo : (minSmoothness ℝ 2 : ℕ∞ω) ≤ ∞ := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (ENat.LEInfty.out (m := (2 : ℕ∞ω)))
  have hj := VectorField.leibniz_identity_mlieBracket_apply (I := 𝓡 n)
    ((hX.contMDiffAt (hU.mem_nhds hx)).of_le htwo)
    ((hY.contMDiffAt (hU.mem_nhds hx)).of_le htwo)
    ((hZ.contMDiffAt (hU.mem_nhds hx)).of_le htwo)
  have hneg : L Y (-L Z X) x = -L Y (L Z X) x := by
    simpa only [neg_one_smul] using
      (VectorField.mlieBracket_const_smul_right (I := 𝓡 n)
        (V := Y) (W := L Z X) (c := (-1 : ℝ)) (hmd _ (hL Z X hZ hX) hx))
  rw [VectorField.mlieBracket_swap_apply (V := VectorField.mlieBracket (𝓡 n) X Y)
      (W := Z), VectorField.mlieBracket_swap (V := X) (W := Z)] at hj
  change L X (L Y Z) x = -L Z (L X Y) x + L Y (-L Z X) x at hj
  rw [hneg] at hj
  have hJac : L X (L Y Z) x + L Y (L Z X) x + L Z (L X Y) x = 0 := by
    rw [hj]
    module
  have hcomm :
      (N X (R Y Z W) x - R Y Z (N X W) x + R X (L Y Z) W x) +
      (N Y (R Z X W) x - R Z X (N Y W) x + R Y (L Z X) W x) +
      (N Z (R X Y W) x - R X Y (N Z W) x + R Z (L X Y) W x) = 0 := by
    rw [houter X Y Z W hY hZ hW, houter Y Z X W hZ hX hW,
      houter Z X Y W hX hY hW]
    calc
      _ = -D.connection W x (L X (L Y Z) x + L Y (L Z X) x + L Z (L X Y) x) := by
        dsimp only [R, LeviCivitaData.curvatureOnFields, N, L]
        simp only [map_add]
        module
      _ = 0 := by rw [hJac, map_zero, neg_zero]
  have hp (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) :
      R (N A B) C W x + R C (N B A) W x = R (L A B) C W x := by
    have hT := curvatureOnFields_tensorial_first D hU C W hW hx
    have hAB := hN A B hA hB
    have hBA := hN B A hB hA
    have hadd := hT.add (hmd _ (hAB.sub_section hBA) hx) (hmd _ hBA hx)
    rw [sub_add_cancel] at hadd
    have hsubR : R (N A B - N B A) C W x =
        R (N A B) C W x - R (N B A) C W x :=
      eq_sub_iff_add_eq.mpr hadd.symm
    have heq := hT.pointwise (hmd _ (hAB.sub_section hBA) hx)
      (hmd _ (hL A B hA hB) hx) (htors A B hA hB)
    calc
      _ = R (N A B) C W x - R (N B A) C W x := by
        simp only [R, curvatureOnFields_swap D C (N B A) W x, sub_eq_add_neg]
      _ = R (N A B - N B A) C W x := hsubR.symm
      _ = R (L A B) C W x := heq
  have hcorr :
      (R (N X Y) Z W x + R Y (N X Z) W x +
        R (N Y Z) X W x + R Z (N Y X) W x +
        R (N Z X) Y W x + R X (N Z Y) W x) +
      (R X (L Y Z) W x + R Y (L Z X) W x + R Z (L X Y) W x) = 0 := by
    calc
      _ = (R (N X Y) Z W x + R Z (N Y X) W x) +
          (R (N Y Z) X W x + R X (N Z Y) W x) +
          (R (N Z X) Y W x + R Y (N X Z) W x) +
          (R X (L Y Z) W x + R Y (L Z X) W x + R Z (L X Y) W x) := by module
      _ = 0 := by
        rw [hp X Y Z hX hY, hp Y Z X hY hZ, hp Z X Y hZ hX]
        dsimp only [R]
        rw [curvatureOnFields_swap D (L X Y) Z W x,
          curvatureOnFields_swap D (L Y Z) X W x,
          curvatureOnFields_swap D (L Z X) Y W x]
        module
  change (N X (R Y Z W) x - R (N X Y) Z W x - R Y (N X Z) W x -
      R Y Z (N X W) x) +
    (N Y (R Z X W) x - R (N Y Z) X W x - R Z (N Y X) W x -
      R Z X (N Y W) x) +
    (N Z (R X Y W) x - R (N Z X) Y W x - R X (N Z Y) W x -
      R X Y (N Z W) x) = 0
  calc
    _ = ((N X (R Y Z W) x - R Y Z (N X W) x + R X (L Y Z) W x) +
        (N Y (R Z X W) x - R Z X (N Y W) x + R Y (L Z X) W x) +
        (N Z (R X Y W) x - R X Y (N Z W) x + R Z (L X Y) W x)) -
        ((R (N X Y) Z W x + R Y (N X Z) W x +
          R (N Y Z) X W x + R Z (N Y X) W x +
          R (N Z X) Y W x + R X (N Z Y) W x) +
          (R X (L Y Z) W x + R Y (L Z X) W x + R Z (L X Y) W x)) := by module
    _ = 0 := by rw [hcomm, hcorr, sub_self]

end PoincareConjecture.Proofs.M03
