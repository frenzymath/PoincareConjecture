import PoincareConjecture.Proofs.M13.CurvatureTensorial








set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M13

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem connection_sub (D : LeviCivitaData g)
    (V W : (p : M) → TangentSpace (𝓡 n) p) (x : M)
    (hV : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% V) x)
    (hW : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (T% W) x) :
    D.connection (V - W) x = D.connection V x - D.connection W x := by
  have hneg : D.connection (-W) x = -D.connection W x := by
    simpa only [neg_one_smul] using D.connection.isCovariantDerivativeOn.smul_const (-1 : ℝ) hW
  rw [sub_eq_add_neg, D.connection.isCovariantDerivativeOn.add hV
    (mdifferentiableAt_neg_section hW), hneg, sub_eq_add_neg]


theorem smooth_mlieBracket_at (X Y : (p : M) → TangentSpace (𝓡 n) p) (x : M)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (VectorField.mlieBracket (𝓡 n) X Y)) x := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 2) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 2 M)
  have : IsManifold (𝓡 n) ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  exact hX.mlieBracket_vectorField hY
    (by simp only [minSmoothness_of_isRCLikeNormedField]; decide)


theorem mlieBracket_cyclic (X Y Z : (p : M) → TangentSpace (𝓡 n) p) (x : M)
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    VectorField.mlieBracket (𝓡 n) X (VectorField.mlieBracket (𝓡 n) Y Z) x +
      VectorField.mlieBracket (𝓡 n) Y (VectorField.mlieBracket (𝓡 n) Z X) x +
      VectorField.mlieBracket (𝓡 n) Z (VectorField.mlieBracket (𝓡 n) X Y) x = 0 := by
  have : IsManifold (𝓡 n) (minSmoothness ℝ 3) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 3 M)
  have hJ := VectorField.leibniz_identity_mlieBracket_apply
    (hX.of_le (show minSmoothness ℝ 2 ≤ ∞ by
      simp only [minSmoothness_of_isRCLikeNormedField]; decide))
    (hY.of_le (show minSmoothness ℝ 2 ≤ ∞ by
      simp only [minSmoothness_of_isRCLikeNormedField]; decide))
    (hZ.of_le (show minSmoothness ℝ 2 ≤ ∞ by
      simp only [minSmoothness_of_isRCLikeNormedField]; decide))
  have hneg : VectorField.mlieBracket (𝓡 n) Y (-VectorField.mlieBracket (𝓡 n) X Z) x =
      -VectorField.mlieBracket (𝓡 n) Y (VectorField.mlieBracket (𝓡 n) X Z) x := by
    simpa only [neg_one_smul] using
      VectorField.mlieBracket_const_smul_right (I := 𝓡 n) (V := Y) (c := (-1 : ℝ))
        ((smooth_mlieBracket_at X Z x hX hZ).mdifferentiableAt (by simp))
  rw [VectorField.mlieBracket_swap (V := Z) (W := X), hneg,
    VectorField.mlieBracket_swap_apply (V := Z) (W := VectorField.mlieBracket (𝓡 n) X Y), hJ]
  abel

variable [T2Space M]


theorem connection_mlieBracket (D : LeviCivitaData g) (U : Set M) (hU : IsOpen U)
    (Y Z : (p : M) → TangentSpace (𝓡 n) p)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (x : M) (hx : x ∈ U) (u : TangentSpace (𝓡 n) x) :
    D.connection (VectorField.mlieBracket (𝓡 n) Y Z) x u =
      D.connection (fun p ↦ D.connection Z p (Y p)) x u -
        D.connection (fun p ↦ D.connection Y p (Z p)) x u := by
  have hYZ := ((connection_apply_contMDiffOn g D U hU Y Z hY hZ).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hZY := ((connection_apply_contMDiffOn g D U hU Z Y hZ hY).contMDiffAt
    (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hB := (smooth_mlieBracket_at Y Z x (hY.contMDiffAt (hU.mem_nhds hx))
    (hZ.contMDiffAt (hU.mem_nhds hx))).mdifferentiableAt (by simp)
  have heq : ((fun p ↦ D.connection Z p (Y p)) - (fun p ↦ D.connection Y p (Z p)))
      =ᶠ[nhds x] VectorField.mlieBracket (𝓡 n) Y Z := by
    filter_upwards [hU.mem_nhds hx] with p hp
    exact D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero
      ((hY.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))
      ((hZ.contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp))
  have H := D.connection.isCovariantDerivativeOn.congr_of_eventuallyEq
    (mdifferentiableAt_sub_section hYZ hZY) hB Filter.univ_mem heq
  rw [← H, connection_sub D _ _ x hYZ hZY]
  rfl


theorem curvatureOnFields_bianchi (D : LeviCivitaData g) (U : Set M) (hU : IsOpen U)
    (X Y Z : (p : M) → TangentSpace (𝓡 n) p)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (x : M) (hx : x ∈ U) :
    D.curvatureOnFields X Y Z x + D.curvatureOnFields Y Z X x +
      D.curvatureOnFields Z X Y x = 0 := by
  have hXx := hX.contMDiffAt (hU.mem_nhds hx)
  have hYx := hY.contMDiffAt (hU.mem_nhds hx)
  have hZx := hZ.contMDiffAt (hU.mem_nhds hx)
  have hT1 := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero
    (hXx.mdifferentiableAt (by simp))
    ((smooth_mlieBracket_at Y Z x hYx hZx).mdifferentiableAt (by simp))
  have hT2 := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero
    (hYx.mdifferentiableAt (by simp))
    ((smooth_mlieBracket_at Z X x hZx hXx).mdifferentiableAt (by simp))
  have hT3 := D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero
    (hZx.mdifferentiableAt (by simp))
    ((smooth_mlieBracket_at X Y x hXx hYx).mdifferentiableAt (by simp))
  have hJ := mlieBracket_cyclic X Y Z x hXx hYx hZx
  rw [← hT1, ← hT2, ← hT3,
    connection_mlieBracket D U hU Y Z hY hZ x hx,
    connection_mlieBracket D U hU Z X hZ hX x hx,
    connection_mlieBracket D U hU X Y hX hY x hx] at hJ
  convert hJ using 1
  unfold LeviCivitaData.curvatureOnFields
  abel

end PoincareConjecture.M13
