import PoincareConjecture.Proofs.M03.CurvatureTensoriality

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureOnFields_first_bianchi
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y Z x +
      D.curvatureOnFields Y Z X x +
      D.curvatureOnFields Z X Y x = 0 := by
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 3) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (3 : ℕ∞ω))))
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection B y (A y)
  let L := VectorField.mlieBracket (𝓡 n) (M := M)
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
      (hA : S A) (hB : S B) {y : M} (hy : y ∈ U) :
      N A B y - N B A y = L A B y :=
    (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
      (hmd A hA hy) (hmd B hB hy)
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hsub (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (v : TangentSpace (𝓡 n) x) :
      D.connection (A - B) x v = D.connection A x v - D.connection B x v := by
    have heq := congrArg (fun C => C v)
      (hc.add (hmd _ (hA.sub_section hB) hx) (hmd B hB hx))
    rw [sub_add_cancel] at heq
    exact eq_sub_iff_add_eq.mpr heq.symm
  have hcyc (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      N A (N B C) x - N A (N C B) x - N (L B C) A x = L A (L B C) x := by
    have heq := (hc.mono (subset_univ U)).congr_of_eqOn
      (hmd _ ((hN B C hB hC).sub_section (hN C B hC hB)) hx)
      (hmd _ (hL B C hB hC) hx) (hU.mem_nhds hx)
      (fun y hy => htors B C hB hC hy)
    have happ := congrArg (fun C => C (A x)) heq
    rw [hsub _ _ (hN B C hB hC) (hN C B hC hB)] at happ
    change N A (N B C) x - N A (N C B) x = N A (L B C) x at happ
    rw [happ]
    exact htors A (L B C) hA (hL B C hB hC) hx
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
  delta LeviCivitaData.curvatureOnFields
  change (N X (N Y Z) x - N Y (N X Z) x - N (L X Y) Z x) +
    (N Y (N Z X) x - N Z (N Y X) x - N (L Y Z) X x) +
    (N Z (N X Y) x - N X (N Z Y) x - N (L Z X) Y x) = 0
  calc
    _ = (N X (N Y Z) x - N X (N Z Y) x - N (L Y Z) X x) +
        (N Y (N Z X) x - N Y (N X Z) x - N (L Z X) Y x) +
        (N Z (N X Y) x - N Z (N Y X) x - N (L X Y) Z x) := by module
    _ = L X (L Y Z) x + L Y (L Z X) x + L Z (L X Y) x := by
      rw [hcyc X Y Z hX hY hZ, hcyc Y Z X hY hZ hX, hcyc Z X Y hZ hX hY]
    _ = 0 := by rw [hj]; module

end PoincareConjecture.Proofs.M03
