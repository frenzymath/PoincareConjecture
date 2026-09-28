import PoincareConjecture.Proofs.M03.MetricPairRegularity
import PoincareConjecture.Proofs.M03.CurvatureFamily
import PoincareConjecture.Proofs.M03.CurvatureExtension
import PoincareConjecture.Proofs.M03.CurvatureTrilinear
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame









set_option autoImplicit false
set_option maxHeartbeats 2400000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Manifold Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiffOn_family_curvature
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (D : (t : ℝ) → LeviCivitaData (g t))
    {U : Set M} (hU : IsOpen U)
    (X Y Z : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) p.2
        ((D p.1).curvature p.2 (X p.2) (Y p.2) (Z p.2))) (J ×ˢ U) := by
  apply contMDiffOn_family_vector_of_metric_pair hg hU
  intro S hS hSU W hW
  have hs := contMDiffOn_family_curvatureOnFields_pair hg D hS X Y Z W
    (hX.mono hSU) (hY.mono hSU) (hZ.mono hSU) hW
  apply hs.congr
  intro p hp
  rw [curvature_eq_curvatureOnFields (D p.1) hS X Y Z
    (hX.mono hSU) (hY.mono hSU) (hZ.mono hSU) hp.2]

noncomputable def curvatureOnFields_iteratedCovariantDerivative
    {g : RiemannianMetric n M} (D : LeviCivitaData g) :
    (k : ℕ) → (Fin (k + 3) → (x : M) → TangentSpace (𝓡 n) x) →
      (x : M) → TangentSpace (𝓡 n) x
  | 0, X => fun x => D.curvatureOnFields (X 0) (X 1) (X 2) x
  | k + 1, X => fun x =>
      D.connection (curvatureOnFields_iteratedCovariantDerivative D k (Fin.tail X)) x
        (X 0 x) -
      ∑ j : Fin (k + 3), curvatureOnFields_iteratedCovariantDerivative D k
        (Function.update (Fin.tail X) j
          (fun y => D.connection (X j.succ) y (X 0 y))) x

theorem contMDiffOn_curvatureOnFields_iteratedCovariantDerivative
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (X : Fin (k + 3) → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j)) U) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (curvatureOnFields_iteratedCovariantDerivative D k X)) U := by
  classical
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let S := fun A : (x : M) → TangentSpace (𝓡 n) x =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  let N := fun (A B : (x : M) → TangentSpace (𝓡 n) x) x =>
    D.connection B x (A x)
  have hN (A B : (x : M) → TangentSpace (𝓡 n) x)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hU A B hA hB
  induction k with
  | zero =>
      have hL : S (VectorField.mlieBracket (𝓡 n) (X 0) (X 1)) := by
        intro x hx
        exact (((hX 0).contMDiffAt (hU.mem_nhds hx)).mlieBracket_vectorField
          ((hX 1).contMDiffAt (hU.mem_nhds hx)) (m := ⊤) (n := ⊤)
          (by simp)).contMDiffWithinAt
      exact ((hN _ _ (hX 0) (hN _ _ (hX 1) (hX 2))).sub_section
        (hN _ _ (hX 1) (hN _ _ (hX 0) (hX 2)))).sub_section
          (hN _ _ hL (hX 2))
  | succ k ih =>
      have htail : S (curvatureOnFields_iteratedCovariantDerivative D k (Fin.tail X)) :=
        ih (Fin.tail X) (fun j => hX j.succ)
      have hcorr (j : Fin (k + 3)) : S (curvatureOnFields_iteratedCovariantDerivative D k
          (Function.update (Fin.tail X) j (N (X 0) (X j.succ)))) := by
        apply ih
        intro i
        by_cases hij : i = j
        · subst i
          simpa only [Function.update_self] using hN _ _ (hX 0) (hX j.succ)
        · simpa only [Function.update_of_ne hij, Fin.tail] using hX i.succ
      exact (hN _ _ (hX 0) htail).sub_section (ContMDiffOn.sum_section (fun j _ => hcorr j))

theorem curvatureOnFields_iteratedCovariantDerivative_congr
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (X Y : Fin (k + 3) → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j)) U)
    (hY : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (Y j)) U)
    (hXY : ∀ j, EqOn (X j) (Y j) U) :
    EqOn (curvatureOnFields_iteratedCovariantDerivative D k X)
      (curvatureOnFields_iteratedCovariantDerivative D k Y) U := by
  classical
  let S := fun A : (x : M) → TangentSpace (𝓡 n) x =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  let N := fun (A B : (x : M) → TangentSpace (𝓡 n) x) x =>
    D.connection B x (A x)
  let K := curvatureOnFields_iteratedCovariantDerivative D
  have hN (A B : (x : M) → TangentSpace (𝓡 n) x)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hU A B hA hB
  have hK (r : ℕ) (Z : Fin (r + 3) → (x : M) → TangentSpace (𝓡 n) x)
      (hZ : ∀ j, S (Z j)) : S (K r Z) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D hU r Z hZ
  have hloc (A B C E : (x : M) → TangentSpace (𝓡 n) x)
      (hB : S B) (hE : S E) (hAC : EqOn A C U) (hBE : EqOn B E U) :
      EqOn (N A B) (N C E) U := by
    intro x hx
    have hb := ((hB.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    have he := ((hE.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    have hh := D.connection.isCovariantDerivativeOn.congr_of_eventuallyEq
      (s := univ) hb he Filter.univ_mem
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hBE)
    dsimp only [N]
    rw [hAC hx]
    exact congrArg (fun L => L (C x)) hh
  have hup (r : ℕ) (Z : Fin (r + 3 + 1) → (x : M) → TangentSpace (𝓡 n) x)
      (hZ : ∀ j, S (Z j)) (j : Fin (r + 3)) :
      ∀ i, S ((Function.update (Fin.tail Z) j (N (Z 0) (Z j.succ))) i) := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using hN _ _ (hZ 0) (hZ j.succ)
    · simpa only [Function.update_of_ne hij, Fin.tail] using hZ i.succ
  induction k with
  | zero =>
      intro x hx
      obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
      have hv (Z : Fin 3 → (x : M) → TangentSpace (𝓡 n) x)
          (hZ : ∀ j, S (Z j)) : K 0 Z x = T (Z 0 x) (Z 1 x) (Z 2 x) :=
        ((hT (Z 0 x) (Z 1 x) (Z 2 x)).trans
          (curvature_eq_curvatureOnFields D hU _ _ _ (hZ 0) (hZ 1) (hZ 2) hx)).symm
      change K 0 X x = K 0 Y x
      rw [hv X hX, hv Y hY, hXY 0 hx, hXY 1 hx, hXY 2 hx]
  | succ k ih =>
      have htail := ih (Fin.tail X) (Fin.tail Y)
        (fun j => hX j.succ) (fun j => hY j.succ) (fun j => hXY j.succ)
      have hhead := hloc _ _ _ _ (hK k _ (fun j => hX j.succ))
        (hK k _ (fun j => hY j.succ)) (hXY 0) htail
      intro x hx
      change N (X 0) (K k (Fin.tail X)) x -
          ∑ j, K k (Function.update (Fin.tail X) j (N (X 0) (X j.succ))) x =
        N (Y 0) (K k (Fin.tail Y)) x -
          ∑ j, K k (Function.update (Fin.tail Y) j (N (Y 0) (Y j.succ))) x
      apply congrArg₂ (fun a b : TangentSpace (𝓡 n) x => a - b)
      · exact hhead hx
      apply Finset.sum_congr rfl
      intro j _
      apply ih _ _ (hup k X hX j) (hup k Y hY j) _ hx
      intro i y hy
      by_cases hij : i = j
      · subst i
        simp only [Function.update_self]
        exact hloc _ _ _ _ (hX j.succ) (hY j.succ) (hXY 0) (hXY j.succ) hy
      · simpa only [Function.update_of_ne hij, Fin.tail] using hXY i.succ hy

theorem curvatureOnFields_iteratedCovariantDerivative_add
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (X : Fin (k + 3) → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j)) U)
    (i : Fin (k + 3)) (A B : (x : M) → TangentSpace (𝓡 n) x)
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U) :
    EqOn (curvatureOnFields_iteratedCovariantDerivative D k (Function.update X i (A + B)))
      (curvatureOnFields_iteratedCovariantDerivative D k (Function.update X i A) +
        curvatureOnFields_iteratedCovariantDerivative D k (Function.update X i B)) U := by
  classical
  let S := fun A : (x : M) → TangentSpace (𝓡 n) x =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  let N := fun (A B : (x : M) → TangentSpace (𝓡 n) x) x =>
    D.connection B x (A x)
  let K := curvatureOnFields_iteratedCovariantDerivative D
  have hN (A B : (x : M) → TangentSpace (𝓡 n) x)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hU A B hA hB
  have hK (r : ℕ) (Z : Fin (r + 3) → (x : M) → TangentSpace (𝓡 n) x)
      (hZ : ∀ j, S (Z j)) : S (K r Z) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D hU r Z hZ
  have hup {r : ℕ} (Z : Fin r → (x : M) → TangentSpace (𝓡 n) x)
      (hZ : ∀ j, S (Z j)) (j : Fin r) (C : (x : M) → TangentSpace (𝓡 n) x)
      (hC : S C) : ∀ i, S (Function.update Z j C i) := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using hC
    · simpa only [Function.update_of_ne hij] using hZ i
  have hcongr (r : ℕ) (Z W : Fin (r + 3) → (x : M) → TangentSpace (𝓡 n) x)
      (hZ : ∀ j, S (Z j)) (hW : ∀ j, S (W j)) (hZW : ∀ j, EqOn (Z j) (W j) U) :
      EqOn (K r Z) (K r W) U :=
    curvatureOnFields_iteratedCovariantDerivative_congr D hU r Z W hZ hW hZW
  have hdir (P Q Z : (x : M) → TangentSpace (𝓡 n) x) :
      N (P + Q) Z = N P Z + N Q Z := by
    funext x
    exact map_add (D.connection Z x) (P x) (Q x)
  have hadd (P Y Z : (x : M) → TangentSpace (𝓡 n) x)
      (hY : S Y) (hZ : S Z) : EqOn (N P (Y + Z)) (N P Y + N P Z) U := by
    intro x hx
    exact congrArg (fun L => L (P x)) (D.connection.isCovariantDerivativeOn.add
      (s := univ)
      ((hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)))
  have hloc (P Y Z : (x : M) → TangentSpace (𝓡 n) x)
      (hY : S Y) (hZ : S Z) (hYZ : EqOn Y Z U) : EqOn (N P Y) (N P Z) U := by
    intro x hx
    have hh := D.connection.isCovariantDerivativeOn.congr_of_eventuallyEq
      (s := univ)
      ((hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      Filter.univ_mem (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hYZ)
    exact congrArg (fun L => L (P x)) hh
  have hsucc (r : ℕ) (P : (x : M) → TangentSpace (𝓡 n) x)
      (Z : Fin (r + 3) → (x : M) → TangentSpace (𝓡 n) x) (x : M) :
      K (r + 1) (Fin.cons P Z) x = N P (K r Z) x -
        ∑ j, K r (Function.update Z j (N P (Z j))) x := by
    simp only [K, curvatureOnFields_iteratedCovariantDerivative, Fin.tail_cons,
      Fin.cons_zero, Fin.cons_succ, N]
  induction k generalizing A B with
  | zero =>
      intro x hx
      obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
      have hv (Z : Fin 3 → (x : M) → TangentSpace (𝓡 n) x)
          (hZ : ∀ j, S (Z j)) : K 0 Z x = T (Z 0 x) (Z 1 x) (Z 2 x) :=
        ((hT (Z 0 x) (Z 1 x) (Z 2 x)).trans
          (curvature_eq_curvatureOnFields D hU _ _ _ (hZ 0) (hZ 1) (hZ 2) hx)).symm
      change K 0 (Function.update X i (A + B)) x =
        K 0 (Function.update X i A) x + K 0 (Function.update X i B) x
      rw [hv _ (hup X hX i _ (hA.add_section hB)), hv _ (hup X hX i A hA),
        hv _ (hup X hX i B hB)]
      fin_cases i <;> simp
  | succ k ih =>
      let Z := Fin.tail X
      let P := X 0
      have hZ : ∀ j, S (Z j) := fun j => hX j.succ
      have hP : S P := hX 0
      have hXeq : X = Fin.cons P Z := (Fin.cons_self_tail X).symm
      change EqOn (K (k + 1) (Function.update X i (A + B)))
        (K (k + 1) (Function.update X i A) + K (k + 1) (Function.update X i B)) U
      rw [hXeq]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.update_cons_zero]
        intro x hx
        change K (k + 1) (Fin.cons (A + B) Z) x =
          K (k + 1) (Fin.cons A Z) x + K (k + 1) (Fin.cons B Z) x
        rw [hsucc, hsucc, hsucc]
        have hc (j : Fin (k + 3)) :
            K k (Function.update Z j (N (A + B) (Z j))) x =
              K k (Function.update Z j (N A (Z j))) x +
                K k (Function.update Z j (N B (Z j))) x := by
          rw [hdir]
          exact ih Z hZ j _ _ (hN _ _ hA (hZ j)) (hN _ _ hB (hZ j)) hx
        simp only [hc, Finset.sum_add_distrib]
        rw [hdir]
        simp only [Pi.add_apply]
        abel
      · simp only [← Fin.cons_update]
        intro x hx
        change K (k + 1) (Fin.cons P (Function.update Z j (A + B))) x =
          K (k + 1) (Fin.cons P (Function.update Z j A)) x +
            K (k + 1) (Fin.cons P (Function.update Z j B)) x
        rw [hsucc, hsucc, hsucc]
        have hinside := ih Z hZ j A B hA hB
        have hhead := hloc P _ _ (hK k _ (hup Z hZ j _ (hA.add_section hB)))
          ((hK k _ (hup Z hZ j A hA)).add_section (hK k _ (hup Z hZ j B hB))) hinside
        have hhead' := hadd P _ _ (hK k _ (hup Z hZ j A hA))
          (hK k _ (hup Z hZ j B hB))
        have hc (l : Fin (k + 3)) :
            K k (Function.update (Function.update Z j (A + B)) l
              (N P (Function.update Z j (A + B) l))) x =
            K k (Function.update (Function.update Z j A) l
              (N P (Function.update Z j A l))) x +
            K k (Function.update (Function.update Z j B) l
              (N P (Function.update Z j B l))) x := by
          by_cases hlj : l = j
          · subst l
            simp only [Function.update_self, Function.update_idem]
            have heq : EqOn
                (K k (Function.update Z j (N P (A + B))))
                (K k (Function.update Z j (N P A + N P B))) U := by
              apply hcongr k _ _
                (hup Z hZ j _ (hN _ _ hP (hA.add_section hB)))
                (hup Z hZ j _ ((hN _ _ hP hA).add_section (hN _ _ hP hB)))
              intro l y hy
              by_cases hlj : l = j
              · subst l
                simpa only [Function.update_self] using hadd P A B hA hB hy
              · simp only [Function.update_of_ne hlj]
                rfl
            exact (heq hx).trans (ih Z hZ j _ _ (hN _ _ hP hA) (hN _ _ hP hB) hx)
          · simp only [Function.update_of_ne hlj]
            rw [Function.update_comm (Ne.symm hlj), Function.update_comm (Ne.symm hlj),
              Function.update_comm (Ne.symm hlj)]
            exact ih (Function.update Z l (N P (Z l)))
              (hup Z hZ l _ (hN _ _ hP (hZ l))) j A B hA hB hx
        have hh := (hhead hx).trans (hhead' hx)
        change N P (K k (Function.update Z j (A + B))) x =
          N P (K k (Function.update Z j A)) x + N P (K k (Function.update Z j B)) x at hh
        rw [hh]
        simp only [hc, Finset.sum_add_distrib]
        abel

theorem curvatureOnFields_iteratedCovariantDerivative_smul
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (X : Fin (k + 3) → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j)) U)
    (i : Fin (k + 3)) (f : M → ℝ) (A : (x : M) → TangentSpace (𝓡 n) x)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% A) U) :
    EqOn (curvatureOnFields_iteratedCovariantDerivative D k (Function.update X i (f • A)))
      (f • curvatureOnFields_iteratedCovariantDerivative D k (Function.update X i A)) U := by
  classical
  let S := fun A : (x : M) → TangentSpace (𝓡 n) x =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) U
  let N := fun (A B : (x : M) → TangentSpace (𝓡 n) x) x =>
    D.connection B x (A x)
  let K := curvatureOnFields_iteratedCovariantDerivative D
  have hN (A B : (x : M) → TangentSpace (𝓡 n) x)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hU A B hA hB
  have hK (r : ℕ) (Z : Fin (r + 3) → (x : M) → TangentSpace (𝓡 n) x)
      (hZ : ∀ j, S (Z j)) : S (K r Z) :=
    contMDiffOn_curvatureOnFields_iteratedCovariantDerivative D hU r Z hZ
  have hup {r : ℕ} (Z : Fin r → (x : M) → TangentSpace (𝓡 n) x)
      (hZ : ∀ j, S (Z j)) (j : Fin r) (C : (x : M) → TangentSpace (𝓡 n) x)
      (hC : S C) : ∀ i, S (Function.update Z j C i) := by
    intro i
    by_cases hij : i = j
    · subst i
      simpa only [Function.update_self] using hC
    · simpa only [Function.update_of_ne hij] using hZ i
  have hcongr (r : ℕ) (Z W : Fin (r + 3) → (x : M) → TangentSpace (𝓡 n) x)
      (hZ : ∀ j, S (Z j)) (hW : ∀ j, S (W j)) (hZW : ∀ j, EqOn (Z j) (W j) U) :
      EqOn (K r Z) (K r W) U :=
    curvatureOnFields_iteratedCovariantDerivative_congr D hU r Z W hZ hW hZW
  have hdir (f : M → ℝ) (P Z : (x : M) → TangentSpace (𝓡 n) x) :
      N (f • P) Z = f • N P Z := by
    funext x
    exact map_smul (D.connection Z x) (f x) (P x)
  have hleib (f : M → ℝ) (P Z : (x : M) → TangentSpace (𝓡 n) x)
      (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) (hZ : S Z) :
      EqOn (N P (f • Z))
        (f • N P Z + (fun y => mvfderiv (𝓡 n) f y (P y)) • Z) U := by
    intro x hx
    change D.connection (f • Z) x (P x) =
      f x • D.connection Z x (P x) + mvfderiv (𝓡 n) f x (P x) • Z x
    exact congrArg (fun L => L (P x)) (D.connection.isCovariantDerivativeOn.leibniz
        (s := univ)
        ((hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
        ((hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)))
  have hloc (P Y Z : (x : M) → TangentSpace (𝓡 n) x)
      (hY : S Y) (hZ : S Z) (hYZ : EqOn Y Z U) : EqOn (N P Y) (N P Z) U := by
    intro x hx
    have hh := D.connection.isCovariantDerivativeOn.congr_of_eventuallyEq
      (s := univ)
      ((hY.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      ((hZ.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
      Filter.univ_mem (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hYZ)
    exact congrArg (fun L => L (P x)) hh
  have hsucc (r : ℕ) (P : (x : M) → TangentSpace (𝓡 n) x)
      (Z : Fin (r + 3) → (x : M) → TangentSpace (𝓡 n) x) (x : M) :
      K (r + 1) (Fin.cons P Z) x = N P (K r Z) x -
        ∑ j, K r (Function.update Z j (N P (Z j))) x := by
    simp only [K, curvatureOnFields_iteratedCovariantDerivative, Fin.tail_cons,
      Fin.cons_zero, Fin.cons_succ, N]
  induction k generalizing f A with
  | zero =>
      intro x hx
      obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
      have hv (Z : Fin 3 → (x : M) → TangentSpace (𝓡 n) x)
          (hZ : ∀ j, S (Z j)) : K 0 Z x = T (Z 0 x) (Z 1 x) (Z 2 x) :=
        ((hT (Z 0 x) (Z 1 x) (Z 2 x)).trans
          (curvature_eq_curvatureOnFields D hU _ _ _ (hZ 0) (hZ 1) (hZ 2) hx)).symm
      change K 0 (Function.update X i (f • A)) x =
        f x • K 0 (Function.update X i A) x
      rw [hv _ (hup X hX i _ (hf.smul_section hA)), hv _ (hup X hX i A hA)]
      fin_cases i <;> simp
  | succ k ih =>
      let Z := Fin.tail X
      let P := X 0
      have hZ : ∀ j, S (Z j) := fun j => hX j.succ
      have hP : S P := hX 0
      have hXeq : X = Fin.cons P Z := (Fin.cons_self_tail X).symm
      change EqOn (K (k + 1) (Function.update X i (f • A)))
        (f • K (k + 1) (Function.update X i A)) U
      rw [hXeq]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.update_cons_zero]
        intro x hx
        change K (k + 1) (Fin.cons (f • A) Z) x =
          f x • K (k + 1) (Fin.cons A Z) x
        rw [hsucc, hsucc]
        have hc (j : Fin (k + 3)) :
            K k (Function.update Z j (N (f • A) (Z j))) x =
              f x • K k (Function.update Z j (N A (Z j))) x := by
          rw [hdir]
          exact ih Z hZ j f _ hf (hN _ _ hA (hZ j)) hx
        simp only [hc, ← Finset.smul_sum]
        rw [hdir]
        exact (smul_sub (f x) _ _).symm
      · simp only [← Fin.cons_update]
        let d : M → ℝ := fun y => mvfderiv (𝓡 n) f y (P y)
        have hd : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ d U := by
          have hh := contMDiffOn_family_spatial_mvfderiv (f := fun _ : ℝ => f)
            hU (hf.comp contMDiffOn_snd (fun _ hp => hp.2)) P hP
              (J := univ)
          exact hh.comp
            (show ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
              (fun y : M => ((0 : ℝ), y)) U from
              contMDiffOn_const.prodMk contMDiffOn_id)
            (fun y hy => ⟨mem_univ (0 : ℝ), hy⟩)
        intro x hx
        change K (k + 1) (Fin.cons P (Function.update Z j (f • A))) x =
          f x • K (k + 1) (Fin.cons P (Function.update Z j A)) x
        rw [hsucc, hsucc]
        have hinside := ih Z hZ j f A hf hA
        have hhead := hloc P _ _ (hK k _ (hup Z hZ j _ (hf.smul_section hA)))
          (hf.smul_section (hK k _ (hup Z hZ j A hA))) hinside
        have hhead' := hleib f P _ hf (hK k _ (hup Z hZ j A hA))
        have hc (l : Fin (k + 3)) :
            K k (Function.update (Function.update Z j (f • A)) l
              (N P (Function.update Z j (f • A) l))) x =
            f x • K k (Function.update (Function.update Z j A) l
              (N P (Function.update Z j A l))) x +
                if l = j then d x • K k (Function.update Z j A) x else 0 := by
          by_cases hlj : l = j
          · subst l
            simp only [Function.update_self, Function.update_idem, ite_true]
            have heq : EqOn
                (K k (Function.update Z j (N P (f • A))))
                (K k (Function.update Z j (f • N P A + d • A))) U := by
              apply hcongr k _ _
                (hup Z hZ j _ (hN _ _ hP (hf.smul_section hA)))
                (hup Z hZ j _ ((hf.smul_section (hN _ _ hP hA)).add_section
                  (hd.smul_section hA)))
              intro l y hy
              by_cases hlj : l = j
              · subst l
                simpa only [Function.update_self] using hleib f P A hf hA hy
              · simp only [Function.update_of_ne hlj]
                rfl
            rw [heq hx]
            have ha := curvatureOnFields_iteratedCovariantDerivative_add D hU k Z hZ j
              (f • N P A) (d • A) (hf.smul_section (hN _ _ hP hA)) (hd.smul_section hA) hx
            change K k (Function.update Z j (f • N P A + d • A)) x =
              K k (Function.update Z j (f • N P A)) x +
                K k (Function.update Z j (d • A)) x at ha
            rw [ha]
            exact congrArg₂ (· + ·) (ih Z hZ j f _ hf (hN _ _ hP hA) hx)
              (ih Z hZ j d A hd hA hx)
          · simp only [Function.update_of_ne hlj, if_neg hlj, add_zero]
            rw [Function.update_comm (Ne.symm hlj), Function.update_comm (Ne.symm hlj)]
            exact ih (Function.update Z l (N P (Z l)))
              (hup Z hZ l _ (hN _ _ hP (hZ l))) j f A hf hA hx
        have hh := (hhead hx).trans (hhead' hx)
        change N P (K k (Function.update Z j (f • A))) x =
          f x • N P (K k (Function.update Z j A)) x +
            d x • K k (Function.update Z j A) x at hh
        rw [hh]
        simp only [hc, Finset.sum_add_distrib, ← Finset.smul_sum]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [smul_sub]
        abel

theorem curvatureOnFields_iteratedCovariantDerivative_congr_at
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (X Y : Fin (k + 3) → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j)) U)
    (hY : ∀ j, ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (Y j)) U)
    {x : M} (hx : x ∈ U) (hXY : ∀ j, X j x = Y j x) :
    curvatureOnFields_iteratedCovariantDerivative D k X x =
      curvatureOnFields_iteratedCovariantDerivative D k Y x := by
  classical
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := e.localFrame b
  let V := U ∩ e.baseSet
  have hV : IsOpen V := hU.inter e.open_baseSet
  have hxV : x ∈ V := ⟨hx, he⟩
  let S := fun A : (x : M) → TangentSpace (𝓡 n) x =>
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% A) V
  let K := curvatureOnFields_iteratedCovariantDerivative D k
  have hE (j : Fin n) : S (E j) :=
    (e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b j).mono inter_subset_right
  have hXV (j : Fin (k + 3)) : S (X j) := (hX j).mono inter_subset_left
  have hYV (j : Fin (k + 3)) : S (Y j) := (hY j).mono inter_subset_left
  let q := fun (j : Fin n) (A : (y : M) → TangentSpace (𝓡 n) y) y =>
    e.localFrameCoeff (𝓡 n) b j y (A y)
  have hq (j : Fin n) (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) :
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q j A) V :=
    contMDiffOn_localFrameCoeff b hV inter_subset_right hA j
  have hsum (Z : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) (i : Fin (k + 3))
      (A : Fin n → (y : M) → TangentSpace (𝓡 n) y) (hA : ∀ j, S (A j))
      (s : Finset (Fin n)) :
      K (Function.update Z i (∑ j ∈ s, A j)) x =
        ∑ j ∈ s, K (Function.update Z i (A j)) x := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        have hh := curvatureOnFields_iteratedCovariantDerivative_smul D hV k Z hZ i
          (fun _ => (0 : ℝ)) (Z i) contMDiffOn_const (hZ i) hxV
        change K (Function.update Z i ((0 : M → ℝ) • Z i)) x =
          ((0 : M → ℝ) • K (Function.update Z i (Z i))) x at hh
        simpa only [zero_smul, Pi.zero_apply] using hh
    | @insert j s hj ih =>
        simp only [Finset.sum_insert hj]
        have hh := curvatureOnFields_iteratedCovariantDerivative_add D hV k Z hZ i
          (A j) (∑ l ∈ s, A l) (hA j)
          (by simpa only [Finset.sum_apply] using
            (ContMDiffOn.sum_section (s := s) (fun l _ => hA l))) hxV
        change K (Function.update Z i (A j + ∑ l ∈ s, A l)) x =
          K (Function.update Z i (A j)) x + K (Function.update Z i (∑ l ∈ s, A l)) x at hh
        exact hh.trans (congrArg (K (Function.update Z i (A j)) x + ·) ih)
  have hframe (Z : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) (i : Fin (k + 3))
      (A : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) :
      K (Function.update Z i A) x = ∑ j, q j A x • K (Function.update Z i (E j)) x := by
    let Q := fun j : Fin n => q j A • E j
    have hQ (j : Fin n) : S (Q j) := (hq j A hA).smul_section (hE j)
    have hup (B : (y : M) → TangentSpace (𝓡 n) y) (hB : S B) :
        ∀ j, S (Function.update Z i B j) := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [Function.update_self] using hB
      · simpa only [Function.update_of_ne hji] using hZ j
    have hh := curvatureOnFields_iteratedCovariantDerivative_congr D hV k
      (Function.update Z i A) (Function.update Z i (∑ j, Q j))
      (hup A hA) (hup _ (by simpa only [S, Finset.sum_apply] using
        (ContMDiffOn.sum_section (s := Finset.univ) (fun j _ => hQ j))))
      (by
        intro j y hy
        by_cases hji : j = i
        · subst j
          rw [Function.update_self, Function.update_self]
          change A y = (∑ j, Q j) y
          rw [Finset.sum_apply]
          exact e.eq_sum_localFrameCoeff_smul (I := 𝓡 n) (b := b) (s := A) hy.2
        · simp only [Function.update_of_ne hji]
          rfl) hxV
    change K (Function.update Z i A) x = K (Function.update Z i (∑ j, Q j)) x at hh
    rw [hh, hsum Z hZ i Q hQ Finset.univ]
    apply Finset.sum_congr rfl
    intro j _
    exact curvatureOnFields_iteratedCovariantDerivative_smul D hV k Z hZ i
      (q j A) (E j) (hq j A hA) (hE j) hxV
  have hslot (Z : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y)
      (hZ : ∀ j, S (Z j)) (i : Fin (k + 3))
      (A B : (y : M) → TangentSpace (𝓡 n) y) (hA : S A) (hB : S B)
      (hAB : A x = B x) : K (Function.update Z i A) x = K (Function.update Z i B) x := by
    rw [hframe Z hZ i A hA, hframe Z hZ i B hB]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [q]
    rw [hAB]
  have hp (s : Finset (Fin (k + 3))) : K (s.piecewise Y X) x = K X x := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.piecewise_empty]
    | @insert i s hi ih =>
        let Z := s.piecewise Y X
        have hZ (j : Fin (k + 3)) : S (Z j) := by
          by_cases hj : j ∈ s
          · simpa only [Z, Finset.piecewise, if_pos hj] using hYV j
          · simpa only [Z, Finset.piecewise, if_neg hj] using hXV j
        rw [Finset.piecewise_insert]
        change K (Function.update Z i (Y i)) x = K X x
        have hh := hslot Z hZ i (Y i) (Z i) (hYV i) (hZ i)
          (by simpa only [Z, Finset.piecewise, if_neg hi] using (hXY i).symm)
        rw [Function.update_eq_self] at hh
        exact hh.trans ih
  simpa only [Finset.piecewise_univ] using (hp Finset.univ).symm

theorem exists_curvatureOnFields_iteratedCovariantDerivative_multilinearMap
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (k : ℕ) (x : M) :
    ∃ L : MultilinearMap ℝ (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x)
        (TangentSpace (𝓡 n) x),
      ∀ {U : Set M}, IsOpen U →
      ∀ (X : Fin (k + 3) → (y : M) → TangentSpace (𝓡 n) y),
        (∀ j, ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j)) U) →
        x ∈ U → L (fun j => X j x) = curvatureOnFields_iteratedCovariantDerivative D k X x := by
  classical
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let b0 := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let b := e.basisAt b0 he
  let E := e.localFrame b0
  let lift : TangentSpace (𝓡 n) x →ₗ[ℝ] ((y : M) → TangentSpace (𝓡 n) y) := b.constr ℝ E
  have hlift (v : TangentSpace (𝓡 n) x) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (lift v)) e.baseSet := by
    rw [show lift v = ∑ j, b.equivFun v j • E j from b.constr_apply_fintype ℝ E v]
    simpa only [Finset.sum_apply] using
      (ContMDiffOn.sum_section (s := Finset.univ) (fun j _ =>
        (e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b0 j).const_smul_section
          (a := b.equivFun v j)))
  have hliftx (v : TangentSpace (𝓡 n) x) : lift v x = v := by
    rw [show lift v = ∑ j, b.equivFun v j • E j from b.constr_apply_fintype ℝ E v]
    simp only [Finset.sum_apply, Pi.smul_apply]
    have hh (j : Fin n) : E j x = b j := e.localFrame_apply_of_mem_baseSet b0 he
    simp only [hh, Module.Basis.equivFun_apply]
    exact b.sum_repr v
  let K := curvatureOnFields_iteratedCovariantDerivative D k
  have hup (v : Fin (k + 3) → TangentSpace (𝓡 n) x) (i : Fin (k + 3))
      (w : TangentSpace (𝓡 n) x) :
      (fun j => lift (Function.update v i w j)) = Function.update (fun j => lift (v j)) i (lift w) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji]
  let L : MultilinearMap ℝ (fun _ : Fin (k + 3) => TangentSpace (𝓡 n) x)
      (TangentSpace (𝓡 n) x) := MultilinearMap.mk'
    (fun v => K (fun j => lift (v j)) x)
    (by
      intro v i a b
      simp only [hup, map_add]
      exact curvatureOnFields_iteratedCovariantDerivative_add D e.open_baseSet k
        (fun j => lift (v j)) (fun j => hlift (v j)) i (lift a) (lift b) (hlift a) (hlift b) he)
    (by
      intro v i c a
      simp only [hup, map_smul]
      exact curvatureOnFields_iteratedCovariantDerivative_smul D e.open_baseSet k
        (fun j => lift (v j)) (fun j => hlift (v j)) i (fun _ => c) (lift a)
        contMDiffOn_const (hlift a) he)
  refine ⟨L, ?_⟩
  intro U hU X hX hx
  change K (fun j => lift (X j x)) x = K X x
  exact curvatureOnFields_iteratedCovariantDerivative_congr_at D (hU.inter e.open_baseSet) k
    (fun j => lift (X j x)) X
    (fun j => (hlift _).mono inter_subset_right)
    (fun j => (hX j).mono inter_subset_left) ⟨hx, he⟩ (fun j => hliftx _)

theorem contMDiffOn_family_curvatureOnFields_iteratedCovariantDerivative
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : RiemannianMetric.IsSmoothFamilyOn g J)
    (D : (t : ℝ) → LeviCivitaData (g t))
    {U : Set M} (hU : IsOpen U) (k : ℕ)
    (X : Fin (k + 3) → ℝ → (x : M) → TangentSpace (𝓡 n) x)
    (hX : ∀ j, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        (X j p.1 p.2)) (J ×ˢ U)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2
        (curvatureOnFields_iteratedCovariantDerivative (D p.1) k
          (fun j => X j p.1) p.2)) (J ×ˢ U) := by
  classical
  let S := fun (V : Set M) (A : ℝ → (x : M) → TangentSpace (𝓡 n) x) =>
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (A p.1 p.2))
      (J ×ˢ V)
  let N := fun (A B : ℝ → (x : M) → TangentSpace (𝓡 n) x) t x =>
    (D t).connection (B t) x (A t x)
  have hpair {V : Set M} (A B : ℝ → (x : M) → TangentSpace (𝓡 n) x)
      (hA : S V A) (hB : S V B) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (g p.1).inner p.2 (A p.1 p.2) (B p.1 p.2)) (J ×ˢ V) := by
    have hh := ContMDiffOn.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n)) (F₃ := ℝ)
      (E₁ := fun y : M => TangentSpace (𝓡 n) y)
      (E₂ := fun y : M => TangentSpace (𝓡 n) y) (E₃ := fun _ : M => ℝ)
      (ψ := fun p : ℝ × M => (g p.1).inner p.2) (b := Prod.snd)
      (hg.mono (Set.prod_mono subset_rfl (subset_univ V))) hA hB
    intro p hp
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (hh p hp)).2
  have hscalar {V : Set M} (hV : IsOpen V) (f : ℝ → M → ℝ)
      (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (Function.uncurry f) (J ×ˢ V))
      (A : ℝ → (x : M) → TangentSpace (𝓡 n) x) (hA : S V A) :
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => mvfderiv (𝓡 n) (f p.1) p.2 (A p.1 p.2)) (J ×ˢ V) := by
    intro p hp
    have hf' : ContMDiffWithinAt
        (((𝓘(ℝ, ℝ)).prod (𝓡 n)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun q : (ℝ × M) × M => f q.1.1 q.2) ((J ×ˢ V) ×ˢ V) (p, p.2) :=
      (hf (p.1, p.2) hp).comp (p, p.2)
        (contMDiffWithinAt_fst.fst.prodMk contMDiffWithinAt_snd)
        (fun (_q : (ℝ × M) × M) (hq : _q ∈ (J ×ˢ V) ×ˢ V) => ⟨hq.1.1, hq.2⟩)
    have hderiv := ContMDiffWithinAt.mfderivWithin
      (n := ∞) (m := ∞) (f := fun q : ℝ × M => f q.1) (g := Prod.snd) hf'
      contMDiffWithinAt_snd hp (fun q hq => hq.2) (by norm_num) hV.uniqueMDiffOn
    have happ := ContMDiffWithinAt.clm_apply_of_inCoordinates
      (b₁ := Prod.snd) (b₂ := fun q : ℝ × M => f q.1 q.2)
      hderiv (hA p hp) (hf p hp)
    have hs : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => mfderivWithin (𝓡 n) 𝓘(ℝ, ℝ)
          (f q.1) V q.2 (A q.1 q.2)) (J ×ˢ V) p := by
      simpa only [trivializationAt_model_space_apply] using
        (Bundle.contMDiffWithinAt_totalSpace.mp happ).2
    apply hs.congr_of_eventuallyEq_of_mem _ hp
    filter_upwards [self_mem_nhdsWithin] with q hq
    rw [mfderivWithin_of_mem_nhds (hV.mem_nhds hq.2)]
    rfl
  have hN (A B : ℝ → (x : M) → TangentSpace (𝓡 n) x)
      (hA : S U A) (hB : S U B) : S U (N A B) := by
    apply contMDiffOn_family_vector_of_metric_pair hg hU
    intro V hV hVU W hW
    have hAV : S V A := hA.mono (Set.prod_mono subset_rfl hVU)
    have hBV : S V B := hB.mono (Set.prod_mono subset_rfl hVU)
    have hWV : S V (fun _ => W) :=
      hW.comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd (fun _ hp => hp.2)
    have hNW : S V (N A (fun _ => W)) :=
      ContMDiffOn.clm_bundle_apply (contMDiffOn_connection_family hg D hV W hW) hAV
    have hd := hscalar hV (fun t y => (g t).inner y (B t y) (W y))
      (hpair B (fun _ => W) hBV hWV) A hAV
    apply (hd.sub (hpair B (N A (fun _ => W)) hBV hNW)).congr
    intro p hp
    have hBt : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (B p.1)) V :=
      hBV.comp (contMDiffOn_const.prodMk contMDiffOn_id) (fun _ hy => ⟨hp.1, hy⟩)
    have hBmd := (hBt.contMDiffAt (hV.mem_nhds hp.2)).mdifferentiableAt (by simp)
    have hWmd := (hW.contMDiffAt (hV.mem_nhds hp.2)).mdifferentiableAt (by simp)
    dsimp only [Function.uncurry, N]
    rw [(D p.1).mvfderiv_inner (A p.1) (B p.1) W hBmd hWmd]
    ring
  have hsub (A B : ℝ → (x : M) → TangentSpace (𝓡 n) x)
      (hA : S U A) (hB : S U B) : S U (fun t y => A t y - B t y) := by
    apply contMDiffOn_family_vector_of_metric_pair hg hU
    intro V hV hVU W hW
    have hWV : S V (fun _ => W) :=
      hW.comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd (fun _ hp => hp.2)
    have hAV := hA.mono (Set.prod_mono subset_rfl hVU)
    have hBV := hB.mono (Set.prod_mono subset_rfl hVU)
    simpa only [map_sub, sub_apply] using
      (hpair A (fun _ => W) hAV hWV).sub (hpair B (fun _ => W) hBV hWV)
  have hsum {r : ℕ} (A : Fin r → ℝ → (x : M) → TangentSpace (𝓡 n) x)
      (hA : ∀ j, S U (A j)) : S U (fun t y => ∑ j, A j t y) := by
    apply contMDiffOn_family_vector_of_metric_pair hg hU
    intro V hV hVU W hW
    have hWV : S V (fun _ => W) :=
      hW.comp (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) contMDiffOn_snd (fun _ hp => hp.2)
    simpa only [map_sum, sum_apply] using
      (contMDiffOn_finsetSum (t := Finset.univ) (fun j _ =>
        hpair (A j) (fun _ => W) ((hA j).mono (Set.prod_mono subset_rfl hVU)) hWV))
  induction k with
  | zero =>
      let A := X 0
      let B := X 1
      let C := X 2
      have hh := hsub
        (fun t y => N A (N B C) t y - N B (N A C) t y)
        (N (fun t y => N A B t y - N B A t y) C)
        (hsub (N A (N B C)) (N B (N A C))
          (hN A (N B C) (hX 0) (hN B C (hX 1) (hX 2)))
          (hN B (N A C) (hX 1) (hN A C (hX 0) (hX 2))))
        (hN (fun t y => N A B t y - N B A t y) C
          (hsub (N A B) (N B A) (hN A B (hX 0) (hX 1)) (hN B A (hX 1) (hX 0)))
          (hX 2))
      apply hh.congr
      intro p hp
      have hslice (j : Fin 3) : ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (X j p.1)) U :=
        (hX j).comp (contMDiffOn_const.prodMk contMDiffOn_id) (fun _ hy => ⟨hp.1, hy⟩)
      have htors := ((D p.1).connection.torsion_eq_zero_iff.mp (D p.1).torsion_eq_zero)
        (((hslice 0).contMDiffAt (hU.mem_nhds hp.2)).mdifferentiableAt (by simp))
        (((hslice 1).contMDiffAt (hU.mem_nhds hp.2)).mdifferentiableAt (by simp))
      apply congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2)
      change (D p.1).curvatureOnFields (A p.1) (B p.1) (C p.1) p.2 =
        N A (N B C) p.1 p.2 - N B (N A C) p.1 p.2 -
          (D p.1).connection (C p.1) p.2 (N A B p.1 p.2 - N B A p.1 p.2)
      rw [htors]
      rfl
  | succ k ih =>
      have htail := ih (fun j => X j.succ) (fun j => hX j.succ)
      have hc (j : Fin (k + 3)) : S U
          (fun t y => curvatureOnFields_iteratedCovariantDerivative (D t) k
            (Function.update (fun i => X i.succ t) j
              (fun z => (D t).connection (X j.succ t) z (X 0 t z))) y) := by
        have hh := ih (Function.update (fun i => X i.succ) j (N (X 0) (X j.succ)))
          (by
            intro i
            by_cases hij : i = j
            · subst i
              simpa only [Function.update_self] using hN _ _ (hX 0) (hX j.succ)
            · simpa only [Function.update_of_ne hij] using hX i.succ)
        apply hh.congr
        intro p hp
        apply congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2)
        apply congrArg (fun Z => curvatureOnFields_iteratedCovariantDerivative (D p.1) k Z p.2)
        funext i
        by_cases hij : i = j
        · subst i
          simp only [Function.update_self]
          rfl
        · simp only [Function.update_of_ne hij]
      exact hsub
        (N (X 0) (fun t y => curvatureOnFields_iteratedCovariantDerivative (D t) k
          (fun j => X j.succ t) y))
        (fun t y => ∑ j : Fin (k + 3), curvatureOnFields_iteratedCovariantDerivative (D t) k
          (Function.update (fun i => X i.succ t) j
            (fun z => (D t).connection (X j.succ t) z (X 0 t z))) y)
        (hN (X 0) (fun t y => curvatureOnFields_iteratedCovariantDerivative (D t) k
          (fun j => X j.succ t) y) (hX 0) htail)
        (hsum (fun j t y => curvatureOnFields_iteratedCovariantDerivative (D t) k
          (Function.update (fun i => X i.succ t) j
            (fun z => (D t).connection (X j.succ t) z (X 0 t z))) y) hc)

end PoincareConjecture.Proofs.M03
