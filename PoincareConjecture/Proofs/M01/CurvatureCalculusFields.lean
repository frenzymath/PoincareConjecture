import PoincareConjecture.Proofs.M01.ConnectionRegularity
import PoincareConjecture.Proofs.M01.Curvature

set_option autoImplicit false
open scoped Manifold ContDiff Bundle
open Filter
universe u
namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem curvatureOnFields_bianchi (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y Z x + D.curvatureOnFields Y Z X x +
      D.curvatureOnFields Z X Y x = 0 := by
  let nabla := fun A B : (y : M) → TangentSpace (𝓡 n) y ↦
    fun y ↦ D.connection B y (A y)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (nabla A B)) U := by
    exact D.m01_contMDiffOn_connection_apply hU A B hA hB
  have hAt (A : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) x :=
    (hA.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hBracket (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (VectorField.mlieBracket (𝓡 n) A B)) U := by
    apply ((hN A B hA hB).sub_section (hN B A hB hA)).congr
    intro y hy
    simp only [Bundle.TotalSpace.mk_inj]
    exact ((D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
      ((hA.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
      ((hB.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))).symm
  have hT (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U) :
      D.connection (nabla A B) x - D.connection (nabla B A) x =
        D.connection (VectorField.mlieBracket (𝓡 n) A B) x := by
    have hsub : D.connection (nabla A B - nabla B A) x =
        D.connection (nabla A B) x - D.connection (nabla B A) x := by
      have hn := D.connection.isCovariantDerivativeOn.smul_const (-1 : ℝ)
        (hAt _ (hN B A hB hA))
      simp only [neg_one_smul] at hn
      rw [sub_eq_add_neg, D.connection.isCovariantDerivativeOn.add
        (hAt _ (hN A B hA hB))
        (mdifferentiableAt_neg_section (hAt _ (hN B A hB hA))), hn, sub_eq_add_neg]
    rw [← hsub]
    apply D.connection.isCovariantDerivativeOn.congr_of_eqOn
      (mdifferentiableAt_sub_section (hAt _ (hN A B hA hB)) (hAt _ (hN B A hB hA)))
      (hAt _ (hBracket A B hA hB)) (hU.mem_nhds hx)
    intro y hy
    exact (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
      ((hA.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
      ((hB.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))
  have h1 := congrArg (fun L ↦ L (X x)) (hT Y Z hY hZ)
  have h2 := congrArg (fun L ↦ L (Y x)) (hT X Z hX hZ)
  have h3 := congrArg (fun L ↦ L (Z x)) (hT X Y hX hY)
  have t1 := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
    (hAt X hX) (hAt _ (hBracket Y Z hY hZ))
  have t2 := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
    (hAt Y hY) (hAt _ (hBracket X Z hX hZ))
  have t3 := (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
    (hAt _ (hBracket X Y hX hY)) (hAt Z hZ)
  have hi3 : IsManifold (𝓡 n) (minSmoothness ℝ 3) M := by
    simpa only [minSmoothness_of_isRCLikeNormedField] using
      (inferInstance : IsManifold (𝓡 n) 3 M)
  have hle : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  have hj := VectorField.leibniz_identity_mlieBracket_apply
    ((hX.contMDiffAt (hU.mem_nhds hx)).of_le hle)
    ((hY.contMDiffAt (hU.mem_nhds hx)).of_le hle)
    ((hZ.contMDiffAt (hU.mem_nhds hx)).of_le hle)
  simp only [sub_apply, nabla] at h1 h2 h3
  unfold curvatureOnFields
  rw [VectorField.mlieBracket_swap_apply (V := Z) (W := X), map_neg]
  calc
    _ = ((D.connection (VectorField.mlieBracket (𝓡 n) Y Z) x) (X x) -
          (D.connection X x) (VectorField.mlieBracket (𝓡 n) Y Z x)) -
        ((D.connection (VectorField.mlieBracket (𝓡 n) X Z) x) (Y x) -
          (D.connection Y x) (VectorField.mlieBracket (𝓡 n) X Z x)) -
        ((D.connection Z x) (VectorField.mlieBracket (𝓡 n) X Y x) -
          (D.connection (VectorField.mlieBracket (𝓡 n) X Y) x) (Z x)) := by
      rw [← h1, ← h2, ← h3]
      abel
    _ = VectorField.mlieBracket (𝓡 n) X (VectorField.mlieBracket (𝓡 n) Y Z) x -
          VectorField.mlieBracket (𝓡 n) Y (VectorField.mlieBracket (𝓡 n) X Z) x -
          VectorField.mlieBracket (𝓡 n) (VectorField.mlieBracket (𝓡 n) X Y) Z x := by
      rw [t1, t2, t3]
    _ = 0 := by rw [hj]; abel

theorem curvatureOnFields_smul_left
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (f : M → ℝ) (X Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f U)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (_hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields (f • X) Y Z x = f x • D.curvatureOnFields X Y Z x := by
  let nabla := fun A B : (y : M) → TangentSpace (𝓡 n) y ↦
    fun y ↦ D.connection B y (A y)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U) :
      ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (nabla A B)) U := by
    exact D.m01_contMDiffOn_connection_apply hU A B hA hB
  have hAt (A : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) x :=
    (hA.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hF : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f x :=
    (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hA := hN X Z hX hZ
  have hleib := D.connection.isCovariantDerivativeOn.leibniz (hAt _ hA) hF
  have hleib' := congrArg (fun L ↦ L (Y x)) hleib
  dsimp [nabla] at hleib'
  have hinner : (fun y ↦ D.connection Z y ((f • X) y)) =
      f • (fun y ↦ D.connection Z y (X y)) := by
    funext y
    change D.connection Z y (f y • X y) = f y • D.connection Z y (X y)
    exact map_smul (D.connection Z y) (f y) (X y)
  unfold curvatureOnFields
  change D.connection (fun y ↦ D.connection Z y (Y y)) x (f x • X x) -
      D.connection (fun y ↦ D.connection Z y ((f • X) y)) x (Y x) -
      D.connection Z x (VectorField.mlieBracket (𝓡 n) (f • X) Y x) = _
  rw [map_smul, hinner, hleib']
  rw [VectorField.mlieBracket_smul_left hF (hAt X hX)]
  simp only [map_add, map_smul, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  module

theorem curvatureOnFields_add_left
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X X' Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hX' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X') U)
    (_hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields (X + X') Y Z x =
      D.curvatureOnFields X Y Z x + D.curvatureOnFields X' Y Z x := by
  let nabla := fun A B : (y : M) → TangentSpace (𝓡 n) y ↦
    fun y ↦ D.connection B y (A y)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (nabla A B)) U := by
    exact D.m01_contMDiffOn_connection_apply hU A B hA hB
  have hAt (A : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) x :=
    (hA.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hinner : (fun y ↦ D.connection Z y ((X + X') y)) =
      (fun y ↦ D.connection Z y (X y)) + (fun y ↦ D.connection Z y (X' y)) := by
    funext y
    change D.connection Z y (X y + X' y) = _
    exact map_add (D.connection Z y) (X y) (X' y)
  have hconn := D.connection.isCovariantDerivativeOn.add
    (hAt _ (hN X Z hX hZ)) (hAt _ (hN X' Z hX' hZ))
  have hconn' := congrArg (fun L ↦ L (Y x)) hconn
  dsimp [nabla] at hconn'
  unfold curvatureOnFields
  change D.connection (fun y ↦ D.connection Z y (Y y)) x (X x + X' x) -
      D.connection (fun y ↦ D.connection Z y ((X + X') y)) x (Y x) -
      D.connection Z x (VectorField.mlieBracket (𝓡 n) (X + X') Y x) = _
  rw [map_add, hinner, hconn', VectorField.mlieBracket_add_left
    (hAt X hX) (hAt X' hX')]
  simp only [map_add, add_apply, sub_eq_add_neg]
  abel

theorem curvatureOnFields_smul_second
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (f : M → ℝ) (X Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X (f • Y) Z x = f x • D.curvatureOnFields X Y Z x := by
  rw [D.m01_curvatureOnFields_swap, D.curvatureOnFields_smul_left hU f Y X Z
    hf hY hX hZ hx]
  have hs := D.m01_curvatureOnFields_swap Y X Z x
  rw [hs]
  simp only [smul_neg]

theorem curvatureOnFields_add_second
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y Y' Z : (y : M) → TangentSpace (𝓡 n) y)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hY' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y') U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X (Y + Y') Z x =
      D.curvatureOnFields X Y Z x + D.curvatureOnFields X Y' Z x := by
  calc
    D.curvatureOnFields X (Y + Y') Z x =
        -D.curvatureOnFields (Y + Y') X Z x :=
      D.m01_curvatureOnFields_swap (Y + Y') X Z x
    _ = -(D.curvatureOnFields Y X Z x + D.curvatureOnFields Y' X Z x) := by
      rw [D.curvatureOnFields_add_left hU Y Y' X Z hY hY' hX hZ hx]
    _ = D.curvatureOnFields X Y Z x + D.curvatureOnFields X Y' Z x := by
      rw [D.m01_curvatureOnFields_swap Y X Z x, D.m01_curvatureOnFields_swap Y' X Z x]
      module

theorem curvatureOnFields_smul_third
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (f : M → ℝ) (X Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y (f • Z) x = f x • D.curvatureOnFields X Y Z x := by
  have hB := D.curvatureOnFields_bianchi hU X Y (f • Z) hX hY
    (hf.smul_section hZ) hx
  have h0 := D.curvatureOnFields_bianchi hU X Y Z hX hY hZ hx
  have hYZ := D.curvatureOnFields_smul_second hU f Y Z X hf hY hZ hX hx
  have hZX := D.curvatureOnFields_smul_left hU f Z X Y hf hZ hX hY hx
  rw [hYZ, hZX] at hB
  have h0' := congrArg (fun q ↦ f x • q) h0
  simp only [smul_zero] at h0'
  apply sub_eq_zero.mp
  calc
    D.curvatureOnFields X Y (f • Z) x -
        f x • D.curvatureOnFields X Y Z x =
      (D.curvatureOnFields X Y (f • Z) x +
          f x • D.curvatureOnFields Y Z X x +
          f x • D.curvatureOnFields Z X Y x) -
        f x • (D.curvatureOnFields X Y Z x +
          D.curvatureOnFields Y Z X x + D.curvatureOnFields Z X Y x) := by
            module
    _ = 0 := by rw [hB, h0']; simp

theorem curvatureOnFields_add_third
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y Z Z' : (y : M) → TangentSpace (𝓡 n) y)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hZ' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z') U)
    {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y (Z + Z') x =
      D.curvatureOnFields X Y Z x + D.curvatureOnFields X Y Z' x := by
  have hB := D.curvatureOnFields_bianchi hU X Y (Z + Z') hX hY
    (hZ.add_section hZ') hx
  have hB0 := D.curvatureOnFields_bianchi hU X Y Z hX hY hZ hx
  have hB1 := D.curvatureOnFields_bianchi hU X Y Z' hX hY hZ' hx
  have hYZ := D.curvatureOnFields_add_second hU Y Z Z' X hY hZ hZ' hX hx
  have hZX := D.curvatureOnFields_add_left hU Z Z' X Y hZ hZ' hX hY hx
  rw [hYZ, hZX] at hB
  apply sub_eq_zero.mp
  calc
    D.curvatureOnFields X Y (Z + Z') x -
        (D.curvatureOnFields X Y Z x + D.curvatureOnFields X Y Z' x) =
      (D.curvatureOnFields X Y (Z + Z') x +
          (D.curvatureOnFields Y Z X x + D.curvatureOnFields Y Z' X x) +
          (D.curvatureOnFields Z X Y x + D.curvatureOnFields Z' X Y x)) -
        (D.curvatureOnFields X Y Z x + D.curvatureOnFields Y Z X x +
          D.curvatureOnFields Z X Y x) -
        (D.curvatureOnFields X Y Z' x + D.curvatureOnFields Y Z' X x +
          D.curvatureOnFields Z' X Y x) := by
            module
    _ = 0 := by rw [hB, hB0, hB1]; simp

theorem curvatureOnFields_congr_of_eqOn
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X X' Y Y' Z Z' : (y : M) → TangentSpace (𝓡 n) y)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hX' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X') U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hY' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y') U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hZ' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z') U)
    (hXe : ∀ y ∈ U, X y = X' y) (hYe : ∀ y ∈ U, Y y = Y' y)
    (hZe : ∀ y ∈ U, Z y = Z' y) {x : M} (hx : x ∈ U) :
    D.curvatureOnFields X Y Z x = D.curvatureOnFields X' Y' Z' x := by
  have hAt (A : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) y :=
    (hA.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hconn_eq
      (A A' B B' : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hA' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A') U)
      (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
      (hB' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B') U)
      (heA : ∀ y ∈ U, A y = A' y) (heB : ∀ y ∈ U, B y = B' y) :
      ∀ y ∈ U, D.connection B y (A y) = D.connection B' y (A' y) := by
    intro y hy
    have hBA := D.connection.isCovariantDerivativeOn.congr_of_eqOn
      (hAt B hB hy) (hAt B' hB' hy) (hU.mem_nhds hy)
      (fun z hz ↦ heB z hz)
    exact congrArg (fun L ↦ L (A y)) hBA |>.trans
      (by rw [heA y hy])
  have hinner1 : ∀ y ∈ U,
      (fun z ↦ D.connection Z z (Y z)) y =
        (fun z ↦ D.connection Z' z (Y' z)) y := by
    intro y hy
    exact hconn_eq Y Y' Z Z' hY hY' hZ hZ' hYe hZe y hy
  have hinner2 : ∀ y ∈ U,
      (fun z ↦ D.connection Z z (X z)) y =
        (fun z ↦ D.connection Z' z (X' z)) y := by
    intro y hy
    exact hconn_eq X X' Z Z' hX hX' hZ hZ' hXe hZe y hy
  have hbr : ∀ y ∈ U,
      VectorField.mlieBracket (𝓡 n) X Y y =
        VectorField.mlieBracket (𝓡 n) X' Y' y := by
    intro y hy
    have hXev : X =ᶠ[nhds y] X' := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hXe z hz
    have hYev : Y =ᶠ[nhds y] Y' := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hYe z hz
    exact hXev.mlieBracket_vectorField_eq hYev
  have houter1 := D.connection.isCovariantDerivativeOn.congr_of_eqOn
    ((D.m01_contMDiffOn_connection_apply hU Y Z hY hZ).contMDiffAt
      (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
    ((D.m01_contMDiffOn_connection_apply hU Y' Z' hY' hZ').contMDiffAt
      (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)) (hU.mem_nhds hx)
    hinner1
  have houter2 := D.connection.isCovariantDerivativeOn.congr_of_eqOn
    ((D.m01_contMDiffOn_connection_apply hU X Z hX hZ).contMDiffAt
      (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
    ((D.m01_contMDiffOn_connection_apply hU X' Z' hX' hZ').contMDiffAt
      (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)) (hU.mem_nhds hx)
    hinner2
  unfold curvatureOnFields
  rw [houter1, houter2]
  have hZx := D.connection.isCovariantDerivativeOn.congr_of_eqOn
    (hAt Z hZ hx) (hAt Z' hZ' hx) (hU.mem_nhds hx) hZe
  rw [hZx]
  rw [hXe x hx, hYe x hx, hbr x hx]

theorem curvatureOnFields_smooth
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y Z W : (y : M) → TangentSpace (𝓡 n) y)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U) :
    ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun x ↦ g.inner x (D.curvatureOnFields X Y Z x) (W x)) U := by
  let nabla := fun A B : (y : M) → TangentSpace (𝓡 n) y ↦
    fun y ↦ D.connection B y (A y)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (nabla A B)) U := by
    exact D.m01_contMDiffOn_connection_apply hU A B hA hB
  have hbr : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (VectorField.mlieBracket (𝓡 n) X Y)) U := by
    apply ((hN X Y hX hY).sub_section (hN Y X hY hX)).congr
    intro x hx
    simp only [Bundle.TotalSpace.mk_inj]
    exact ((D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
      ((hX.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))).symm
  have hxy := hN Y Z hY hZ
  have hyx := hN X Z hX hZ
  have hxyz := hN X (nabla Y Z) hX hxy
  have hyxz := hN Y (nabla X Z) hY hyx
  have hbrz := hN (VectorField.mlieBracket (𝓡 n) X Y) Z hbr hZ
  have hcurv : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (D.curvatureOnFields X Y Z)) U := by
    exact (hxyz.sub_section hyxz).sub_section hbrz
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact hcurv.inner_bundle hW

theorem curvatureOnFields_contMDiffOn
    (D : LeviCivitaData g) {U : Set M} (hU : IsOpen U)
    (X Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U) :
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (D.curvatureOnFields X Y Z)) U := by
  let nabla := fun A B : (y : M) → TangentSpace (𝓡 n) y ↦
    fun y ↦ D.connection B y (A y)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
      (hB : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U) :
      ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (nabla A B)) U := by
    exact D.m01_contMDiffOn_connection_apply hU A B hA hB
  have hbr : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (VectorField.mlieBracket (𝓡 n) X Y)) U := by
    apply ((hN X Y hX hY).sub_section (hN Y X hY hX)).congr
    intro x hx
    simp only [Bundle.TotalSpace.mk_inj]
    exact ((D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
      ((hX.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))).symm
  have hxyz := hN X (nabla Y Z) hX (hN Y Z hY hZ)
  have hyxz := hN Y (nabla X Z) hY (hN X Z hX hZ)
  have hbrz := hN (VectorField.mlieBracket (𝓡 n) X Y) Z hbr hZ
  exact (hxyz.sub_section hyxz).sub_section hbrz

end PoincareConjecture.LeviCivitaData
