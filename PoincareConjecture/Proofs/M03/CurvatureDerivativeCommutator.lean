import PoincareConjecture.Proofs.M03.CurvatureTrilinear
import PoincareConjecture.Proofs.M03.CurvatureDerivativeTensoriality
import PoincareConjecture.Proofs.M03.CurvatureJoint










set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curvatureOnFields_second_derivative_commutator
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y A B C : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hA : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
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
    let ddR := fun
        (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      D.connection (fun z => dR Q A B C z) y (P y) -
        dR (fun z => D.connection Q z (P z)) A B C y -
        dR Q (fun z => D.connection A z (P z)) B C y -
        dR Q A (fun z => D.connection B z (P z)) C y -
        dR Q A B (fun z => D.connection C z (P z)) y
    ddR X Y A B C x - ddR Y X A B C x =
      D.curvatureOnFields X Y
        (fun z => D.curvatureOnFields A B C z) x -
      D.curvatureOnFields
        (fun z => D.curvatureOnFields X Y A z) B C x -
      D.curvatureOnFields A
        (fun z => D.curvatureOnFields X Y B z) C x -
      D.curvatureOnFields A B
        (fun z => D.curvatureOnFields X Y C z) x := by
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection Q y (P y)
  let L := VectorField.mlieBracket (𝓡 n) (M := M)
  let R := fun (P Q E : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields P Q E y
  let K := fun (P E F G : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (R E F G) y - R (N P E) F G y -
      R E (N P F) G y - R E F (N P G) y
  let S := fun E : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% E) U
  have hmd (E : (y : M) → TangentSpace (𝓡 n) y) (hE : S E)
      {y : M} (hy : y ∈ U) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% E) y :=
    (hE.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hN (E F : (y : M) → TangentSpace (𝓡 n) y)
      (hE : S E) (hF : S F) : S (N E F) :=
    D.contMDiffOn_connection_apply hU E F hE hF
  have hL (E F : (y : M) → TangentSpace (𝓡 n) y)
      (hE : S E) (hF : S F) : S (L E F) := by
    intro y hy
    exact ((hE.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
      (hF.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤) (by simp)).contMDiffWithinAt
  have hR (E F G : (y : M) → TangentSpace (𝓡 n) y)
      (hE : S E) (hF : S F) (hG : S G) : S (R E F G) :=
    ((hN E _ hE (hN F G hF hG)).sub_section
      (hN F _ hF (hN E G hE hG))).sub_section
        (hN _ G (hL E F hE hF) hG)
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hsub (E F : (y : M) → TangentSpace (𝓡 n) y)
      (hE : S E) (hF : S F) (v : TangentSpace (𝓡 n) x) :
      D.connection (E - F) x v = D.connection E x v - D.connection F x v := by
    have heq := congrArg (fun C => C v)
      (hc.add (hmd _ (hE.sub_section hF) hx) (hmd F hF hx))
    rw [sub_add_cancel] at heq
    exact eq_sub_iff_add_eq.mpr heq.symm
  have houter (P Q E F G : (y : M) → TangentSpace (𝓡 n) y)
      (hQ : S Q) (hE : S E) (hF : S F) (hG : S G) :
      N P (K Q E F G) x =
        N P (N Q (R E F G)) x - N P (R (N Q E) F G) x -
          N P (R E (N Q F) G) x - N P (R E F (N Q G)) x := by
    have h₀ := hN Q _ hQ (hR E F G hE hF hG)
    have h₁ := hR _ F G (hN Q E hQ hE) hF hG
    have h₂ := hR E _ G hE (hN Q F hQ hF) hG
    have h₃ := hR E F _ hE hF (hN Q G hQ hG)
    change D.connection
      (((N Q (R E F G) - R (N Q E) F G) - R E (N Q F) G) -
        R E F (N Q G)) x (P x) = _
    rw [hsub _ _ ((h₀.sub_section h₁).sub_section h₂) h₃,
      hsub _ _ (h₀.sub_section h₁) h₂, hsub _ _ h₀ h₁]
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  have heval (E F G : (y : M) → TangentSpace (𝓡 n) y)
      (hE : S E) (hF : S F) (hG : S G) :
      R E F G x = T (E x) (F x) (G x) :=
    ((hT (E x) (F x) (G x)).trans
      (curvature_eq_curvatureOnFields D hU E F G hE hF hG hx)).symm
  have hinner (E : (y : M) → TangentSpace (𝓡 n) y) :
      R X Y E x = N X (N Y E) x - N Y (N X E) x - N (L X Y) E x := rfl
  have htors : N X Y x - N Y X x = L X Y x :=
    (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero)
      (hmd X hX hx) (hmd Y hY hx)
  have hdir (E : (y : M) → TangentSpace (𝓡 n) y) :
      N (N X Y) E x = N (N Y X) E x + N (L X Y) E x := by
    have hxy : N X Y x = N Y X x + L X Y x := by
      rw [← htors]
      module
    change D.connection E x (N X Y x) =
      D.connection E x (N Y X x) + D.connection E x (L X Y x)
    rw [hxy, map_add]
  change
    (N X (K Y A B C) x - K (N X Y) A B C x - K Y (N X A) B C x -
      K Y A (N X B) C x - K Y A B (N X C) x) -
    (N Y (K X A B C) x - K (N Y X) A B C x - K X (N Y A) B C x -
      K X A (N Y B) C x - K X A B (N Y C) x) =
    R X Y (R A B C) x - R (R X Y A) B C x -
      R A (R X Y B) C x - R A B (R X Y C) x
  rw [houter X Y A B C hY hA hB hC, houter Y X A B C hX hA hB hC]
  dsimp only [K]
  rw [hinner (R A B C),
    heval (R X Y A) B C (hR X Y A hX hY hA) hB hC,
    heval A (R X Y B) C hA (hR X Y B hX hY hB) hC,
    heval A B (R X Y C) hA hB (hR X Y C hX hY hC),
    hinner A, hinner B, hinner C]
  simp (disch := solve_by_elim [hN, hL, hR]) only
    [heval, hdir, map_sub, LinearMap.sub_apply, map_add, LinearMap.add_apply]
  module

theorem curvatureOnFields_third_derivative_commutator
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y A B C G : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
    (hG : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% G) U)
    {x : M} (hx : x ∈ U) :
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
    let R := fun (P Q E : (y : M) → TangentSpace (𝓡 n) y) y => D.curvatureOnFields P Q E y
    let K := fun (P E F H : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (R E F H) y - R (N P E) F H y - R E (N P F) H y - R E F (N P H) y
    let H := fun (P Q E F G : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (K Q E F G) y - K (N P Q) E F G y - K Q (N P E) F G y -
      K Q E (N P F) G y - K Q E F (N P G) y
    let J := fun (P Q E F G L : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (H Q E F G L) y - H (N P Q) E F G L y - H Q (N P E) F G L y -
      H Q E (N P F) G L y - H Q E F (N P G) L y - H Q E F G (N P L) y
    J X Y A B C G x - J Y X A B C G x =
      R X Y (K A B C G) x - K (R X Y A) B C G x - K A (R X Y B) C G x -
        K A B (R X Y C) G x - K A B C (R X Y G) x := by
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
  let L := VectorField.mlieBracket (𝓡 n) (M := M)
  let R := fun (P Q E : (y : M) → TangentSpace (𝓡 n) y) y => D.curvatureOnFields P Q E y
  let K := fun (P E F H : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (R E F H) y - R (N P E) F H y - R E (N P F) H y - R E F (N P H) y
  let H := fun (P Q E F G : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (K Q E F G) y - K (N P Q) E F G y - K Q (N P E) F G y -
    K Q E (N P F) G y - K Q E F (N P G) y
  let S := fun E : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% E) U
  have hmd (E : (y : M) → TangentSpace (𝓡 n) y) (hE : S E)
      {y : M} (hy : y ∈ U) : MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% E) y :=
    (hE.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hN (E F : (y : M) → TangentSpace (𝓡 n) y) (hE : S E) (hF : S F) : S (N E F) :=
    D.contMDiffOn_connection_apply hU E F hE hF
  have hL (E F : (y : M) → TangentSpace (𝓡 n) y) (hE : S E) (hF : S F) : S (L E F) := by
    intro y hy
    exact ((hE.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
      (hF.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤) (by simp)).contMDiffWithinAt
  have hR (E F G : (y : M) → TangentSpace (𝓡 n) y)
      (hE : S E) (hF : S F) (hG : S G) : S (R E F G) :=
    ((hN E _ hE (hN F G hF hG)).sub_section
      (hN F _ hF (hN E G hE hG))).sub_section (hN _ G (hL E F hE hF) hG)
  have hK (P E F G : (y : M) → TangentSpace (𝓡 n) y)
      (hP : S P) (hE : S E) (hF : S F) (hG : S G) : S (K P E F G) :=
    (((hN P _ hP (hR E F G hE hF hG)).sub_section
      (hR _ F G (hN P E hP hE) hF hG)).sub_section
      (hR E _ G hE (hN P F hP hF) hG)).sub_section
      (hR E F _ hE hF (hN P G hP hG))
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hsub (E F : (y : M) → TangentSpace (𝓡 n) y)
      (hE : S E) (hF : S F) (v : TangentSpace (𝓡 n) x) :
      D.connection (E - F) x v = D.connection E x v - D.connection F x v := by
    have heq := congrArg (fun C => C v)
      (hc.add (hmd _ (hE.sub_section hF) hx) (hmd F hF hx))
    rw [sub_add_cancel] at heq
    exact eq_sub_iff_add_eq.mpr heq.symm
  have houter (P Q A B C G : (y : M) → TangentSpace (𝓡 n) y)
      (hQ : S Q) (hA : S A) (hB : S B) (hC : S C) (hG : S G) :
      N P (H Q A B C G) x =
        N P (N Q (K A B C G)) x - N P (K (N Q A) B C G) x -
          N P (K A (N Q B) C G) x - N P (K A B (N Q C) G) x -
          N P (K A B C (N Q G)) x := by
    have h0 := hN Q _ hQ (hK A B C G hA hB hC hG)
    have h1 := hK _ B C G (hN Q A hQ hA) hB hC hG
    have h2 := hK A _ C G hA (hN Q B hQ hB) hC hG
    have h3 := hK A B _ G hA hB (hN Q C hQ hC) hG
    have h4 := hK A B C _ hA hB hC (hN Q G hQ hG)
    change D.connection
      ((((N Q (K A B C G) - K (N Q A) B C G) - K A (N Q B) C G) -
        K A B (N Q C) G) - K A B C (N Q G)) x (P x) = _
    rw [hsub _ _ (((h0.sub_section h1).sub_section h2).sub_section h3) h4,
      hsub _ _ ((h0.sub_section h1).sub_section h2) h3,
      hsub _ _ (h0.sub_section h1) h2, hsub _ _ h0 h1]
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_derivative_quadrilinearMap D x
  have heval (A B C G : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) (hG : S G) :
      K A B C G x = T (A x) (B x) (C x) (G x) :=
    (hT hU A B C G hA hB hC hG hx).symm
  have hinner (E : (y : M) → TangentSpace (𝓡 n) y) :
      R X Y E x = N X (N Y E) x - N Y (N X E) x - N (L X Y) E x := rfl
  have htors : N X Y x - N Y X x = L X Y x :=
    (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) (hmd X hX hx) (hmd Y hY hx)
  have hdir (E : (y : M) → TangentSpace (𝓡 n) y) :
      N (N X Y) E x = N (N Y X) E x + N (L X Y) E x := by
    have hxy : N X Y x = N Y X x + L X Y x := by rw [← htors]; module
    change D.connection E x (N X Y x) =
      D.connection E x (N Y X x) + D.connection E x (L X Y x)
    rw [hxy, map_add]
  change
    (N X (H Y A B C G) x - H (N X Y) A B C G x - H Y (N X A) B C G x -
      H Y A (N X B) C G x - H Y A B (N X C) G x - H Y A B C (N X G) x) -
    (N Y (H X A B C G) x - H (N Y X) A B C G x - H X (N Y A) B C G x -
      H X A (N Y B) C G x - H X A B (N Y C) G x - H X A B C (N Y G) x) =
    R X Y (K A B C G) x - K (R X Y A) B C G x - K A (R X Y B) C G x -
      K A B (R X Y C) G x - K A B C (R X Y G) x
  rw [houter X Y A B C G hY hA hB hC hG, houter Y X A B C G hX hA hB hC hG]
  dsimp only [H]
  rw [hinner (K A B C G),
    heval (R X Y A) B C G (hR X Y A hX hY hA) hB hC hG,
    heval A (R X Y B) C G hA (hR X Y B hX hY hB) hC hG,
    heval A B (R X Y C) G hA hB (hR X Y C hX hY hC) hG,
    heval A B C (R X Y G) hA hB hC (hR X Y G hX hY hG),
    hinner A, hinner B, hinner C, hinner G]
  simp (disch := solve_by_elim [hN, hL, hR, hK]) only
    [heval, hdir, map_sub, LinearMap.sub_apply, map_add, LinearMap.add_apply]
  module

theorem curvatureOnFields_third_derivative_inner_commutator
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (P X Y A B C : (x : M) → TangentSpace (𝓡 n) x)
    (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hX : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
    {x : M} (hx : x ∈ U) :
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
    let R := fun (P Q E : (y : M) → TangentSpace (𝓡 n) y) y => D.curvatureOnFields P Q E y
    let K := fun (P E F G : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (R E F G) y - R (N P E) F G y - R E (N P F) G y - R E F (N P G) y
    let H := fun (P Q E F G : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (K Q E F G) y - K (N P Q) E F G y - K Q (N P E) F G y -
      K Q E (N P F) G y - K Q E F (N P G) y
    let J := fun (P Q E F G L : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (H Q E F G L) y - H (N P Q) E F G L y - H Q (N P E) F G L y -
      H Q E (N P F) G L y - H Q E F (N P G) L y - H Q E F G (N P L) y
    J P X Y A B C x - J P Y X A B C x =
      K P X Y (R A B C) x + R X Y (K P A B C) x -
        K P (R X Y A) B C x - R (K P X Y A) B C x -
        K P A (R X Y B) C x - R A (K P X Y B) C x -
        K P A B (R X Y C) x - R A B (K P X Y C) x := by
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
  let R := fun (P Q E : (y : M) → TangentSpace (𝓡 n) y) y => D.curvatureOnFields P Q E y
  let K := fun (P E F G : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (R E F G) y - R (N P E) F G y - R E (N P F) G y - R E F (N P G) y
  let H := fun (P Q E F G : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (K Q E F G) y - K (N P Q) E F G y - K Q (N P E) F G y -
    K Q E (N P F) G y - K Q E F (N P G) y
  let J := fun (P Q E F G L : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (H Q E F G L) y - H (N P Q) E F G L y - H Q (N P E) F G L y -
    H Q E (N P F) G L y - H Q E F (N P G) L y - H Q E F G (N P L) y
  let S := fun E : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% E) U
  let E := fun (X Y A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    R X Y (R A B C) y - R (R X Y A) B C y -
      R A (R X Y B) C y - R A B (R X Y C) y
  have hmd (Q : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% Q) x :=
    (hQ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hN (Q V : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) (hV : S V) : S (N Q V) :=
    D.contMDiffOn_connection_apply hU Q V hQ hV
  have hR (Q V W : (y : M) → TangentSpace (𝓡 n) y)
      (hQ : S Q) (hV : S V) (hW : S W) : S (R Q V W) := by
    have hb : S (VectorField.mlieBracket (𝓡 n) Q V) := by
      intro y hy
      exact ((hQ.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
        (hV.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤) (by simp)).contMDiffWithinAt
    exact ((hN Q _ hQ (hN V W hV hW)).sub_section
      (hN V _ hV (hN Q W hQ hW))).sub_section (hN _ W hb hW)
  have hK (Q V W Z : (y : M) → TangentSpace (𝓡 n) y)
      (hQ : S Q) (hV : S V) (hW : S W) (hZ : S Z) : S (K Q V W Z) :=
    (((hN Q _ hQ (hR V W Z hV hW hZ)).sub_section
      (hR _ W Z (hN Q V hQ hV) hW hZ)).sub_section
      (hR V _ Z hV (hN Q W hQ hW) hZ)).sub_section
      (hR V W _ hV hW (hN Q Z hQ hZ))
  have hH (Q V W Z L : (y : M) → TangentSpace (𝓡 n) y)
      (hQ : S Q) (hV : S V) (hW : S W) (hZ : S Z) (hL : S L) : S (H Q V W Z L) :=
    ((((hN Q _ hQ (hK V W Z L hV hW hZ hL)).sub_section
      (hK _ W Z L (hN Q V hQ hV) hW hZ hL)).sub_section
      (hK V _ Z L hV (hN Q W hQ hW) hZ hL)).sub_section
      (hK V W _ L hV hW (hN Q Z hQ hZ) hL)).sub_section
      (hK V W Z _ hV hW hZ (hN Q L hQ hL))
  have hcomm (Q V W Z L : (y : M) → TangentSpace (𝓡 n) y)
      (hQ : S Q) (hV : S V) (hW : S W) (hZ : S Z) (hL : S L)
      {y : M} (hy : y ∈ U) :
      H Q V W Z L y - H V Q W Z L y = E Q V W Z L y :=
    curvatureOnFields_second_derivative_commutator D hU Q V W Z L hQ hV hW hZ hL hy
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hsub (Q V : (y : M) → TangentSpace (𝓡 n) y) (hQ : S Q) (hV : S V) :
      N P (Q - V) x = N P Q x - N P V x := by
    have heq := congrArg (fun f => f (P x)) (hc.add (hmd _ (hQ.sub_section hV)) (hmd V hV))
    rw [sub_add_cancel] at heq
    exact eq_sub_iff_add_eq.mpr heq.symm
  have h0 := hR X Y _ hX hY (hR A B C hA hB hC)
  have h1 := hR _ B C (hR X Y A hX hY hA) hB hC
  have h2 := hR A _ C hA (hR X Y B hX hY hB) hC
  have h3 := hR A B _ hA hB (hR X Y C hX hY hC)
  have houter :
      N P (H X Y A B C) x - N P (H Y X A B C) x = N P (E X Y A B C) x := by
    have heq := congrArg (fun f => f (P x))
      ((D.connection.isCovariantDerivativeOn (s := U)).congr_of_eqOn
        (hmd _ ((hH X Y A B C hX hY hA hB hC).sub_section
          (hH Y X A B C hY hX hA hB hC)))
        (hmd _ (((h0.sub_section h1).sub_section h2).sub_section h3))
        (hU.mem_nhds hx) (fun y hy => hcomm X Y A B C hX hY hA hB hC hy))
    change N P (H X Y A B C - H Y X A B C) x = N P (E X Y A B C) x at heq
    rw [hsub _ _ (hH X Y A B C hX hY hA hB hC) (hH Y X A B C hY hX hA hB hC)] at heq
    exact heq
  have hEouter : N P (E X Y A B C) x =
      N P (R X Y (R A B C)) x - N P (R (R X Y A) B C) x -
        N P (R A (R X Y B) C) x - N P (R A B (R X Y C)) x := by
    change N P (((R X Y (R A B C) - R (R X Y A) B C) - R A (R X Y B) C) -
      R A B (R X Y C)) x = _
    rw [hsub _ _ ((h0.sub_section h1).sub_section h2) h3,
      hsub _ _ (h0.sub_section h1) h2, hsub _ _ h0 h1]
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  have heval (Q V W : (y : M) → TangentSpace (𝓡 n) y)
      (hQ : S Q) (hV : S V) (hW : S W) :
      R Q V W x = T (Q x) (V x) (W x) :=
    ((hT (Q x) (V x) (W x)).trans
      (curvature_eq_curvatureOnFields D hU Q V W hQ hV hW hx)).symm
  change J P X Y A B C x - J P Y X A B C x =
    K P X Y (R A B C) x + R X Y (K P A B C) x -
      K P (R X Y A) B C x - R (K P X Y A) B C x -
      K P A (R X Y B) C x - R A (K P X Y B) C x -
      K P A B (R X Y C) x - R A B (K P X Y C) x
  calc
    _ = (N P (H X Y A B C) x - N P (H Y X A B C) x) -
        (H (N P X) Y A B C x - H Y (N P X) A B C x) -
        (H X (N P Y) A B C x - H (N P Y) X A B C x) -
        (H X Y (N P A) B C x - H Y X (N P A) B C x) -
        (H X Y A (N P B) C x - H Y X A (N P B) C x) -
        (H X Y A B (N P C) x - H Y X A B (N P C) x) := by
      dsimp only [J]
      module
    _ = N P (E X Y A B C) x - E (N P X) Y A B C x - E X (N P Y) A B C x -
        E X Y (N P A) B C x - E X Y A (N P B) C x - E X Y A B (N P C) x := by
      rw [houter, hcomm _ _ _ _ _ (hN P X hP hX) hY hA hB hC hx,
        hcomm _ _ _ _ _ hX (hN P Y hP hY) hA hB hC hx,
        hcomm _ _ _ _ _ hX hY (hN P A hP hA) hB hC hx,
        hcomm _ _ _ _ _ hX hY hA (hN P B hP hB) hC hx,
        hcomm _ _ _ _ _ hX hY hA hB (hN P C hP hC) hx]
    _ = _ := by
      rw [hEouter,
        heval X Y (K P A B C) hX hY (hK P A B C hP hA hB hC),
        heval (K P X Y A) B C (hK P X Y A hP hX hY hA) hB hC,
        heval A (K P X Y B) C hA (hK P X Y B hP hX hY hB) hC,
        heval A B (K P X Y C) hA hB (hK P X Y C hP hX hY hC)]
      dsimp only [E, K]
      simp (disch := solve_by_elim (maxDepth := 16) only [hP, hX, hY, hA, hB, hC, hN, hR]) only
        [heval, map_sub, LinearMap.sub_apply]
      module

theorem curvatureOnFields_third_derivative_diagonal_interchange
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (P E A B C : (x : M) → TangentSpace (𝓡 n) x)
    (hP : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hE : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% E) U)
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
    {x : M} (hx : x ∈ U) :
    let N := fun (P Q : (y : M) → TangentSpace (𝓡 n) y) y => D.connection Q y (P y)
    let R := fun (P Q E : (y : M) → TangentSpace (𝓡 n) y) y => D.curvatureOnFields P Q E y
    let K := fun (P E F G : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (R E F G) y - R (N P E) F G y - R E (N P F) G y - R E F (N P G) y
    let H := fun (P Q E F G : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (K Q E F G) y - K (N P Q) E F G y - K Q (N P E) F G y -
      K Q E (N P F) G y - K Q E F (N P G) y
    let J := fun (P Q E F G L : (y : M) → TangentSpace (𝓡 n) y) y =>
      N P (H Q E F G L) y - H (N P Q) E F G L y - H Q (N P E) F G L y -
      H Q E (N P F) G L y - H Q E F (N P G) L y - H Q E F G (N P L) y
    J P E E A B C x - J E E P A B C x =
      (2 : ℝ) • R P E (K E A B C) x - K (R P E E) A B C x -
        (2 : ℝ) • K E (R P E A) B C x - (2 : ℝ) • K E A (R P E B) C x -
        (2 : ℝ) • K E A B (R P E C) x + K E P E (R A B C) x -
        R (K E P E A) B C x - R A (K E P E B) C x - R A B (K E P E C) x := by
  have houter := curvatureOnFields_third_derivative_commutator D hU
    P E E A B C hP hE hE hA hB hC hx
  have hinner := curvatureOnFields_third_derivative_inner_commutator D hU
    E P E A B C hE hP hE hA hB hC hx
  dsimp only at houter hinner ⊢
  linear_combination (norm := module) houter + hinner

theorem curvatureOnFields_iteratedCovariantDerivative_outer_commutator
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (P Q : (y : M) → TangentSpace (𝓡 n) y)
    (Z : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hQ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
    (hZ : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (Z j)) U)
    {x : M} (hx : x ∈ U) :
    curvatureOnFields_iteratedCovariantDerivative D (k + 2) (Fin.cons P (Fin.cons Q Z)) x -
      curvatureOnFields_iteratedCovariantDerivative D (k + 2) (Fin.cons Q (Fin.cons P Z)) x =
      D.curvatureOnFields P Q (curvatureOnFields_iteratedCovariantDerivative D k Z) x -
        ∑ j : Fin (k + 3), curvatureOnFields_iteratedCovariantDerivative D k
          (Function.update Z j (fun y => D.curvatureOnFields P Q (Z j) y)) x := by
  classical
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection B y (A y)
  let L := VectorField.mlieBracket (𝓡 n) (M := M)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let S := fun A : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  have hmd (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% A) x :=
    (hA.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hU A B hA hB
  have hL (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (L A B) := by
    intro y hy
    exact ((hA.contMDiffAt (hU.mem_nhds hy)).mlieBracket_vectorField
      (hB.contMDiffAt (hU.mem_nhds hy)) (m := ⊤) (n := ⊤) (by simp)).contMDiffWithinAt
  have hR (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (R A B C) :=
    ((hN A _ hA (hN B C hB hC)).sub_section
      (hN B _ hB (hN A C hA hC))).sub_section
        (hN _ C (hL A B hA hB) hC)
  have hup (V : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hV : ∀ j, S (V j)) (j : Fin (k + 3))
      (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) :
      ∀ i, S (Function.update V j A i) := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using hA
    · simpa only [Function.update_of_ne hij] using hV i
  have hK (V : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hV : ∀ j, S (V j)) : S (K k V) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D hU k V hV
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hsub (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (v : TangentSpace (𝓡 n) x) :
      D.connection (A - B) x v = D.connection A x v - D.connection B x v := by
    have hh := congrArg (fun C => C v)
      (hc.add (hmd _ (hA.sub_section hB)) (hmd B hB))
    rw [sub_add_cancel] at hh
    exact eq_sub_iff_add_eq.mpr hh.symm
  have hnsum (V : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hV : ∀ j, S (V j)) (v : TangentSpace (𝓡 n) x) :
      D.connection (fun y => ∑ j, V j y) x v = ∑ j, D.connection (V j) x v := by
    have aux (s : Finset (Fin (k + 3))) :
        D.connection (fun y => ∑ j ∈ s, V j y) x v =
          ∑ j ∈ s, D.connection (V j) x v := by
      induction s using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty]
          change D.connection 0 x v = 0
          rw [hc.zero, zero_apply]
      | @insert j s hj ih =>
          simp only [Finset.sum_insert hj]
          change D.connection (V j + fun y => ∑ l ∈ s, V l y) x v = _
          rw [hc.add (hmd _ (hV j))
            (MDifferentiableAt.sum_section fun l _ => hmd _ (hV l)), add_apply, ih]
    exact aux Finset.univ
  have hsucc (r : ℕ) (A : (y : M) → TangentSpace (𝓡 n) y)
      (V : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) :
      K (r + 1) (Fin.cons A V) =
        N A (K r V) - fun y => ∑ j, K r (Function.update V j (N A (V j))) y := by
    funext y
    simp only [K, curvatureOnFields_iteratedCovariantDerivative,
      Fin.tail_cons, Fin.cons_zero, Fin.cons_succ, N, Pi.sub_apply]
  have houter (A B : (y : M) → TangentSpace (𝓡 n) y) (hB : S B) :
      N A (K (k + 1) (Fin.cons B Z)) x =
        N A (N B (K k Z)) x -
          ∑ j, N A (K k (Function.update Z j (N B (Z j)))) x := by
    rw [hsucc]
    change D.connection (N B (K k Z) -
      (fun y => ∑ j, K k (Function.update Z j (N B (Z j))) y)) x (A x) = _
    have hh (j : Fin (k + 3)) : S (K k (Function.update Z j (N B (Z j)))) :=
      hK _ (hup Z hZ j _ (hN B _ hB (hZ j)))
    rw [hsub _ _ (hN B _ hB (hK Z hZ)) (ContMDiffOn.sum_section (fun j _ => hh j)),
      hnsum _ hh]
  have hexpand (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) :
      K (k + 2) (Fin.cons A (Fin.cons B Z)) x =
        N A (N B (K k Z)) x -
          (∑ j, N A (K k (Function.update Z j (N B (Z j)))) x) -
          N (N A B) (K k Z) x +
          (∑ j, K k (Function.update Z j (N (N A B) (Z j))) x) -
          (∑ j, N B (K k (Function.update Z j (N A (Z j)))) x) +
          ∑ j, ∑ l, K k (Function.update (Function.update Z j (N A (Z j))) l
            (N B (Function.update Z j (N A (Z j)) l))) x := by
    rw [hsucc (k + 1)]
    simp only [Pi.sub_apply]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ,
      Fin.update_cons_zero, ← Fin.cons_update]
    rw [houter A B hB]
    simp only [hsucc, Pi.sub_apply, Finset.sum_sub_distrib]
    abel
  have hdouble :
      (∑ j, ∑ l, K k (Function.update (Function.update Z j (N P (Z j))) l
        (N Q (Function.update Z j (N P (Z j)) l))) x) -
      (∑ j, ∑ l, K k (Function.update (Function.update Z j (N Q (Z j))) l
        (N P (Function.update Z j (N Q (Z j)) l))) x) =
      ∑ j, (K k (Function.update Z j (N Q (N P (Z j)))) x -
        K k (Function.update Z j (N P (N Q (Z j)))) x) := by
    rw [Finset.sum_comm (f := fun j l => K k
      (Function.update (Function.update Z j (N Q (Z j))) l
        (N P (Function.update Z j (N Q (Z j)) l))) x)]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single j]
    · simp only [Function.update_self, Function.update_idem]
    · intro l _ hlj
      rw [Function.update_of_ne hlj, Function.update_of_ne (Ne.symm hlj),
        Function.update_comm (Ne.symm hlj)]
      exact sub_self _
    · simp
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D k x
  have heval (j : Fin (k + 3)) (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) :
      K k (Function.update Z j A) x = T (Function.update (fun l => Z l x) j (A x)) := by
    change curvatureOnFields_iteratedCovariantDerivative D k (Function.update Z j A) x = _
    rw [← hT hU _ (hup Z hZ j A hA) hx]
    congr 1
    funext l
    by_cases hlj : l = j
    · subst l
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hlj]
  have htors : N P Q x - N Q P x = L P Q x :=
    (D.connection.torsion_eq_zero_iff.mp D.torsion_eq_zero) (hmd P hP) (hmd Q hQ)
  have hdir (A : (y : M) → TangentSpace (𝓡 n) y) :
      N (N P Q) A x - N (N Q P) A x = N (L P Q) A x := by
    change D.connection A x (N P Q x) - D.connection A x (N Q P x) =
      D.connection A x (L P Q x)
    rw [← map_sub, htors]
  have hcurv (A : (y : M) → TangentSpace (𝓡 n) y) :
      R P Q A x = N P (N Q A) x - N Q (N P A) x - N (L P Q) A x := rfl
  have hslot (j : Fin (k + 3)) :
      K k (Function.update Z j (N (N P Q) (Z j))) x -
        K k (Function.update Z j (N (N Q P) (Z j))) x +
        (K k (Function.update Z j (N Q (N P (Z j)))) x -
          K k (Function.update Z j (N P (N Q (Z j)))) x) =
      -K k (Function.update Z j (R P Q (Z j))) x := by
    rw [heval j _ (hN _ _ (hN _ _ hP hQ) (hZ j)),
      heval j _ (hN _ _ (hN _ _ hQ hP) (hZ j)),
      heval j _ (hN _ _ hQ (hN _ _ hP (hZ j))),
      heval j _ (hN _ _ hP (hN _ _ hQ (hZ j))),
      heval j _ (hR _ _ _ hP hQ (hZ j))]
    rw [← T.map_update_sub, hdir, hcurv, T.map_update_sub, T.map_update_sub]
    abel
  change K (k + 2) (Fin.cons P (Fin.cons Q Z)) x -
    K (k + 2) (Fin.cons Q (Fin.cons P Z)) x =
      R P Q (K k Z) x - ∑ j, K k (Function.update Z j (R P Q (Z j))) x
  rw [hexpand P Q hQ, hexpand Q P hP, hcurv]
  have hsumslot := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun j _ => hslot j)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsumslot
  simp only [Finset.sum_sub_distrib] at hdouble
  have hd := hdir (K k Z)
  linear_combination (norm := module) hdouble + hsumslot - hd

theorem curvatureOnFields_iteratedCovariantDerivative_inner_commutator
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (A P Q : (y : M) → TangentSpace (𝓡 n) y)
    (Z : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
    (hA : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hQ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Q) U)
    (hZ : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (Z j)) U)
    {x : M} (hx : x ∈ U) :
    curvatureOnFields_iteratedCovariantDerivative D (k + 3)
        (Fin.cons A (Fin.cons P (Fin.cons Q Z))) x -
      curvatureOnFields_iteratedCovariantDerivative D (k + 3)
        (Fin.cons A (Fin.cons Q (Fin.cons P Z))) x =
      D.curvatureOnFields P Q
        (curvatureOnFields_iteratedCovariantDerivative D (k + 1) (Fin.cons A Z)) x -
      (∑ j : Fin (k + 3), curvatureOnFields_iteratedCovariantDerivative D (k + 1)
        (Fin.cons A (Function.update Z j (fun y => D.curvatureOnFields P Q (Z j) y))) x) +
      curvatureOnFields_iteratedCovariantDerivative D 1
        ![A, P, Q, curvatureOnFields_iteratedCovariantDerivative D k Z] x -
      ∑ j : Fin (k + 3), curvatureOnFields_iteratedCovariantDerivative D k
        (Function.update Z j (curvatureOnFields_iteratedCovariantDerivative D 1 ![A, P, Q, Z j])) x := by
  classical
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let N := fun (B C : (y : M) → TangentSpace (𝓡 n) y) y => D.connection C y (B y)
  let R := fun (B C E : (y : M) → TangentSpace (𝓡 n) y) y => D.curvatureOnFields B C E y
  let K := curvatureOnFields_iteratedCovariantDerivative D
  let G := fun (B C E V : (y : M) → TangentSpace (𝓡 n) y) => K 1 ![B, C, E, V]
  let S := fun B : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U
  let E := fun (B C : (y : M) → TangentSpace (𝓡 n) y)
      (V : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) y =>
    R B C (K k V) y - ∑ j, K k (Function.update V j (R B C (V j))) y
  have hcons {r : ℕ} (B : (y : M) → TangentSpace (𝓡 n) y)
      (V : Fin r → (y : M) → TangentSpace (𝓡 n) y) (hB : S B) (hV : ∀ j, S (V j)) :
      ∀ j : Fin (r + 1), S ((Fin.cons B V :
        Fin (r + 1) → (y : M) → TangentSpace (𝓡 n) y) j) := by
    intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [Fin.cons_zero] using hB
    · simpa only [Fin.cons_succ] using hV l
  have hup {r : ℕ} (V : Fin r → (y : M) → TangentSpace (𝓡 n) y)
      (hV : ∀ j, S (V j)) (j : Fin r)
      (B : (y : M) → TangentSpace (𝓡 n) y) (hB : S B) : ∀ l, S (Function.update V j B l) := by
    intro l
    by_cases hlj : l = j
    · subst l
      simpa only [Function.update_self] using hB
    · simpa only [Function.update_of_ne hlj] using hV l
  have hK (r : ℕ) (V : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hV : ∀ j, S (V j)) : S (K r V) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D hU r V hV
  have hN (B C : (y : M) → TangentSpace (𝓡 n) y) (hB : S B) (hC : S C) : S (N B C) :=
    D.contMDiffOn_connection_apply hU B C hB hC
  have hR (B C V : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (hV : S V) : S (R B C V) :=
    hK 0 ![B, C, V] (hcons B _ hB (hcons C _ hC (hcons V _ hV (fun j => Fin.elim0 j))))
  have hG (B C V W : (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (hV : S V) (hW : S W) : S (G B C V W) :=
    hK 1 ![B, C, V, W]
      (hcons B _ hB (hcons C _ hC (hcons V _ hV (hcons W _ hW (fun j => Fin.elim0 j)))))
  have hE (B C : (y : M) → TangentSpace (𝓡 n) y)
      (V : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (hV : ∀ j, S (V j)) : S (E B C V) :=
    (hR B C _ hB hC (hK k V hV)).sub_section
      (ContMDiffOn.sum_section (fun j _ => hK k _ (hup V hV j _ (hR B C _ hB hC (hV j)))))
  have hmd (B : (y : M) → TangentSpace (𝓡 n) y) (hB : S B) :
      MDifferentiableAt (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (T% B) x :=
    (hB.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hc := D.connection.isCovariantDerivativeOn (s := univ)
  have hsub (B C : (y : M) → TangentSpace (𝓡 n) y) (hB : S B) (hC : S C) :
      N A (B - C) x = N A B x - N A C x := by
    have hh := congrArg (fun f => f (A x)) (hc.add (hmd _ (hB.sub_section hC)) (hmd C hC))
    rw [sub_add_cancel] at hh
    exact eq_sub_iff_add_eq.mpr hh.symm
  have hnsum (V : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hV : ∀ j, S (V j)) : N A (fun y => ∑ j, V j y) x = ∑ j, N A (V j) x := by
    have aux (s : Finset (Fin (k + 3))) :
        D.connection (fun y => ∑ j ∈ s, V j y) x (A x) =
          ∑ j ∈ s, D.connection (V j) x (A x) := by
      induction s using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty]
          change D.connection 0 x (A x) = 0
          rw [hc.zero, zero_apply]
      | @insert j s hj ih =>
          simp only [Finset.sum_insert hj]
          change D.connection (V j + fun y => ∑ l ∈ s, V l y) x (A x) = _
          rw [hc.add (hmd _ (hV j))
            (MDifferentiableAt.sum_section fun l _ => hmd _ (hV l)), add_apply, ih]
    exact aux Finset.univ
  have hsucc (r : ℕ) (B : (y : M) → TangentSpace (𝓡 n) y)
      (V : Fin (r + 3) → (y : M) → TangentSpace (𝓡 n) y) :
      K (r + 1) (Fin.cons B V) = N B (K r V) -
        fun y => ∑ j, K r (Function.update V j (N B (V j))) y := by
    funext y
    simp only [K, curvatureOnFields_iteratedCovariantDerivative,
      Fin.tail_cons, Fin.cons_zero, Fin.cons_succ, N, Pi.sub_apply]
  have hfirst (B C V : (y : M) → TangentSpace (𝓡 n) y) :
      G A B C V x = N A (R B C V) x - R (N A B) C V x -
        R B (N A C) V x - R B C (N A V) x := by
    simp [G, K, curvatureOnFields_iteratedCovariantDerivative, Fin.sum_univ_succ, N, R]
    abel
  have hcomm (B C : (y : M) → TangentSpace (𝓡 n) y)
      (V : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hB : S B) (hC : S C) (hV : ∀ j, S (V j)) {y : M} (hy : y ∈ U) :
      K (k + 2) (Fin.cons B (Fin.cons C V)) y -
        K (k + 2) (Fin.cons C (Fin.cons B V)) y = E B C V y :=
    curvatureOnFields_iteratedCovariantDerivative_outer_commutator D hU k B C V hB hC hV hy
  have hNE :
      N A (K (k + 2) (Fin.cons P (Fin.cons Q Z))) x -
        N A (K (k + 2) (Fin.cons Q (Fin.cons P Z))) x = N A (E P Q Z) x := by
    have hPQ := hK (k + 2) _ (hcons P _ hP (hcons Q Z hQ hZ))
    have hQP := hK (k + 2) _ (hcons Q _ hQ (hcons P Z hP hZ))
    have hh := congrArg (fun f => f (A x))
      ((D.connection.isCovariantDerivativeOn (s := U)).congr_of_eqOn
        (hmd _ (hPQ.sub_section hQP)) (hmd _ (hE P Q Z hP hQ hZ))
        (hU.mem_nhds hx) (fun y hy => hcomm P Q Z hP hQ hZ hy))
    change N A (K (k + 2) (Fin.cons P (Fin.cons Q Z)) -
      K (k + 2) (Fin.cons Q (Fin.cons P Z))) x = N A (E P Q Z) x at hh
    rw [hsub _ _ hPQ hQP] at hh
    exact hh
  have hEouter : N A (E P Q Z) x = N A (R P Q (K k Z)) x -
      ∑ j, N A (K k (Function.update Z j (R P Q (Z j)))) x := by
    change N A (R P Q (K k Z) -
      (fun y => ∑ j, K k (Function.update Z j (R P Q (Z j))) y)) x = _
    have hh (j : Fin (k + 3)) : S (K k (Function.update Z j (R P Q (Z j)))) :=
      hK k _ (hup Z hZ j _ (hR P Q _ hP hQ (hZ j)))
    rw [hsub _ _ (hR P Q _ hP hQ (hK k Z hZ))
      (ContMDiffOn.sum_section fun j _ => hh j), hnsum _ hh]
  have hthird (B C : (y : M) → TangentSpace (𝓡 n) y) :
      K (k + 3) (Fin.cons A (Fin.cons B (Fin.cons C Z))) x =
        N A (K (k + 2) (Fin.cons B (Fin.cons C Z))) x -
        K (k + 2) (Fin.cons (N A B) (Fin.cons C Z)) x -
        K (k + 2) (Fin.cons B (Fin.cons (N A C) Z)) x -
        ∑ j, K (k + 2) (Fin.cons B (Fin.cons C (Function.update Z j (N A (Z j))))) x := by
    rw [hsucc (k + 2)]
    simp only [Pi.sub_apply]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update]
    abel
  have hleft :
      K (k + 3) (Fin.cons A (Fin.cons P (Fin.cons Q Z))) x -
        K (k + 3) (Fin.cons A (Fin.cons Q (Fin.cons P Z))) x =
      N A (E P Q Z) x - E (N A P) Q Z x - E P (N A Q) Z x -
        ∑ j, E P Q (Function.update Z j (N A (Z j))) x := by
    calc
      _ = (N A (K (k + 2) (Fin.cons P (Fin.cons Q Z))) x -
          N A (K (k + 2) (Fin.cons Q (Fin.cons P Z))) x) -
          (K (k + 2) (Fin.cons (N A P) (Fin.cons Q Z)) x -
            K (k + 2) (Fin.cons Q (Fin.cons (N A P) Z)) x) -
          (K (k + 2) (Fin.cons P (Fin.cons (N A Q) Z)) x -
            K (k + 2) (Fin.cons (N A Q) (Fin.cons P Z)) x) -
          ∑ j, (K (k + 2) (Fin.cons P (Fin.cons Q (Function.update Z j (N A (Z j))))) x -
            K (k + 2) (Fin.cons Q (Fin.cons P (Function.update Z j (N A (Z j))))) x) := by
        rw [hthird P Q, hthird Q P]
        simp only [Finset.sum_sub_distrib]
        abel
      _ = _ := by
        rw [hNE, hcomm _ _ _ (hN A P hA hP) hQ hZ hx,
          hcomm _ _ _ hP (hN A Q hA hQ) hZ hx]
        congr 1
        exact Finset.sum_congr rfl (fun j _ =>
          hcomm P Q _ hP hQ (hup Z hZ j _ (hN A _ hA (hZ j))) hx)
  rw [hEouter] at hleft
  dsimp only [E] at hleft
  simp only [Finset.sum_sub_distrib] at hleft
  have hderiv (V : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y) :
      N A (K k V) x = K (k + 1) (Fin.cons A V) x +
        ∑ j, K k (Function.update V j (N A (V j))) x := by
    rw [hsucc]
    change N A (K k V) x = (N A (K k V) x - _) + _
    abel
  have hcorrDeriv :
      (∑ j, N A (K k (Function.update Z j (R P Q (Z j)))) x) =
      (∑ j, K (k + 1) (Fin.cons A (Function.update Z j (R P Q (Z j)))) x) +
        ∑ j, ∑ l, K k (Function.update (Function.update Z j (R P Q (Z j))) l
          (N A (Function.update Z j (R P Q (Z j)) l))) x := by
    simp only [hderiv, Finset.sum_add_distrib]
  have hdouble :
      (∑ j, ∑ l, K k (Function.update (Function.update Z j (N A (Z j))) l
        (R P Q (Function.update Z j (N A (Z j)) l))) x) -
      (∑ j, ∑ l, K k (Function.update (Function.update Z j (R P Q (Z j))) l
        (N A (Function.update Z j (R P Q (Z j)) l))) x) =
      ∑ j, (K k (Function.update Z j (R P Q (N A (Z j)))) x -
        K k (Function.update Z j (N A (R P Q (Z j)))) x) := by
    rw [Finset.sum_comm (f := fun j l => K k
      (Function.update (Function.update Z j (R P Q (Z j))) l
        (N A (Function.update Z j (R P Q (Z j)) l))) x)]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · simp only [Function.update_self, Function.update_idem]
    · intro l _ hlj
      rw [Function.update_of_ne hlj, Function.update_of_ne (Ne.symm hlj),
        Function.update_comm (Ne.symm hlj)]
      exact sub_self _
    · simp
  obtain ⟨T, hT⟩ := exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap D k x
  have hevalK (j : Fin (k + 3)) (B : (y : M) → TangentSpace (𝓡 n) y) (hB : S B) :
      K k (Function.update Z j B) x = T (Function.update (fun l => Z l x) j (B x)) := by
    change curvatureOnFields_iteratedCovariantDerivative D k (Function.update Z j B) x = _
    rw [← hT hU _ (hup Z hZ j B hB) hx]
    congr 1
    funext l
    by_cases hlj : l = j
    · subst l
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hlj]
  have hslot (j : Fin (k + 3)) :
      K k (Function.update Z j (R (N A P) Q (Z j))) x +
        K k (Function.update Z j (R P (N A Q) (Z j))) x +
        (K k (Function.update Z j (R P Q (N A (Z j)))) x -
          K k (Function.update Z j (N A (R P Q (Z j)))) x) =
        -K k (Function.update Z j (G A P Q (Z j))) x := by
    rw [hevalK j _ (hR _ Q _ (hN A P hA hP) hQ (hZ j)),
      hevalK j _ (hR P _ _ hP (hN A Q hA hQ) (hZ j)),
      hevalK j _ (hR P Q _ hP hQ (hN A _ hA (hZ j))),
      hevalK j _ (hN A _ hA (hR P Q _ hP hQ (hZ j))),
      hevalK j _ (hG A P Q _ hA hP hQ (hZ j))]
    rw [hfirst, T.map_update_sub, T.map_update_sub, T.map_update_sub]
    abel
  obtain ⟨B, hB⟩ := exists_curvature_trilinearMap D x
  have hevalR (V W F : (y : M) → TangentSpace (𝓡 n) y)
      (hV : S V) (hW : S W) (hF : S F) : R V W F x = B (V x) (W x) (F x) :=
    ((hB (V x) (W x) (F x)).trans
      (curvature_eq_curvatureOnFields D hU V W F hV hW hF hx)).symm
  have hRsucc : R P Q (K (k + 1) (Fin.cons A Z)) x = R P Q (N A (K k Z)) x -
      ∑ j, R P Q (K k (Function.update Z j (N A (Z j)))) x := by
    rw [hevalR _ _ _ hP hQ (hK (k + 1) _ (hcons A Z hA hZ)),
      hevalR _ _ _ hP hQ (hN A _ hA (hK k Z hZ)), hsucc]
    change B (P x) (Q x) (N A (K k Z) x -
      ∑ j, K k (Function.update Z j (N A (Z j))) x) = _
    rw [map_sub, map_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ =>
      (hevalR P Q _ hP hQ (hK k _ (hup Z hZ j _ (hN A _ hA (hZ j))))).symm)
  have houtput : N A (R P Q (K k Z)) x - R (N A P) Q (K k Z) x -
      R P (N A Q) (K k Z) x - (∑ j, R P Q (K k (Function.update Z j (N A (Z j)))) x) =
      R P Q (K (k + 1) (Fin.cons A Z)) x + G A P Q (K k Z) x := by
    rw [hRsucc, hfirst]
    abel
  have hsumslot := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun j _ => hslot j)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsumslot
  simp only [Finset.sum_sub_distrib] at hdouble
  change K (k + 3) (Fin.cons A (Fin.cons P (Fin.cons Q Z))) x -
    K (k + 3) (Fin.cons A (Fin.cons Q (Fin.cons P Z))) x =
      R P Q (K (k + 1) (Fin.cons A Z)) x -
      (∑ j, K (k + 1) (Fin.cons A (Function.update Z j (R P Q (Z j)))) x) +
      G A P Q (K k Z) x - ∑ j, K k (Function.update Z j (G A P Q (Z j))) x
  linear_combination (norm := module) hleft + houtput - hcorrDeriv + hdouble + hsumslot

theorem curvatureOnFields_iteratedCovariantDerivative_diagonal_interchange
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (P E : (y : M) → TangentSpace (𝓡 n) y)
    (Z : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
    (hP : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% P) U)
    (hE : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% E) U)
    (hZ : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (Z j)) U)
    {x : M} (hx : x ∈ U) :
    curvatureOnFields_iteratedCovariantDerivative D (k + 3)
        (Fin.cons P (Fin.cons E (Fin.cons E Z))) x -
      curvatureOnFields_iteratedCovariantDerivative D (k + 3)
        (Fin.cons E (Fin.cons E (Fin.cons P Z))) x =
      (2 : ℝ) • D.curvatureOnFields P E
        (curvatureOnFields_iteratedCovariantDerivative D (k + 1) (Fin.cons E Z)) x -
      curvatureOnFields_iteratedCovariantDerivative D (k + 1)
        (Fin.cons (fun y => D.curvatureOnFields P E E y) Z) x -
      (2 : ℝ) • (∑ j : Fin (k + 3), curvatureOnFields_iteratedCovariantDerivative D (k + 1)
        (Fin.cons E (Function.update Z j (fun y => D.curvatureOnFields P E (Z j) y))) x) +
      curvatureOnFields_iteratedCovariantDerivative D 1
        ![E, P, E, curvatureOnFields_iteratedCovariantDerivative D k Z] x -
      ∑ j : Fin (k + 3), curvatureOnFields_iteratedCovariantDerivative D k
        (Function.update Z j (curvatureOnFields_iteratedCovariantDerivative D 1 ![E, P, E, Z j])) x := by
  classical
  have hEZ : ∀ j : Fin (k + 4), ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% ((Fin.cons E Z : Fin (k + 4) → (y : M) → TangentSpace (𝓡 n) y) j)) U := by
    intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [Fin.cons_zero] using hE
    · simpa only [Fin.cons_succ] using hZ l
  have houter := curvatureOnFields_iteratedCovariantDerivative_outer_commutator D hU
    (k + 1) P E (Fin.cons E Z) hP hE hEZ hx
  have hinner := curvatureOnFields_iteratedCovariantDerivative_inner_commutator D hU
    k E P E Z hE hP hE hZ hx
  rw [Fin.sum_univ_succ] at houter
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.update_cons_zero, ← Fin.cons_update] at houter
  linear_combination (norm := module) houter + hinner

end PoincareConjecture.Proofs.M03
