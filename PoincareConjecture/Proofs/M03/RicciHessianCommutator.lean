import PoincareConjecture.Proofs.M03.CurvatureRicciSecondDerivative
import PoincareConjecture.Proofs.M03.CurvatureDerivativeCommutator

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Set

universe u

namespace PoincareConjecture.Proofs.M03

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem ricci_second_covariant_derivative_commutator
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {U : Set M} (hU : IsOpen U)
    (X Y B C : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) U)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hB : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% B) U)
    (hC : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% C) U)
    {x : M} (hx : x ∈ U) :
    let dRic := fun
        (A B C : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      mvfderiv (𝓡 n) (fun z => D.ricci z (B z) (C z)) y (A y) -
        D.ricci y (D.connection B y (A y)) (C y) -
        D.ricci y (B y) (D.connection C y (A y))
    let ddRic := fun
        (P Q A B : (y : M) → TangentSpace (𝓡 n) y) (y : M) =>
      mvfderiv (𝓡 n) (fun z => dRic Q A B z) y (P y) -
        dRic (fun z => D.connection Q z (P z)) A B y -
        dRic Q (fun z => D.connection A z (P z)) B y -
        dRic Q A (fun z => D.connection B z (P z)) y
    ddRic X Y B C x - ddRic Y X B C x =
      -D.ricci x (D.curvatureOnFields X Y B x) (C x) -
        D.ricci x (B x) (D.curvatureOnFields X Y C x) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsManifold (𝓡 n) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡 n) ∞ M)
  let : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  let ι := Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))
  let b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x) := (g.orthonormalBasis x).toBasis
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have he : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let b0 := b.map (e.linearEquivAt (R := ℝ) x he)
  let V := U ∩ e.baseSet
  have hV : IsOpen V := hU.inter e.open_baseSet
  have hxV : x ∈ V := ⟨hx, he⟩
  let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let N := fun (A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.connection B y (A y)
  let L := VectorField.mlieBracket (𝓡 n) (M := M)
  let R := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    D.curvatureOnFields A B C y
  let K := fun (A B C W : (y : M) → TangentSpace (𝓡 n) y) y =>
    N A (R B C W) y - R (N A B) C W y -
      R B (N A C) W y - R B C (N A W) y
  let H := fun (A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    mvfderiv (𝓡 n) (fun z => D.ricci z (B z) (C z)) y (A y) -
      D.ricci y (N A B y) (C y) - D.ricci y (B y) (N A C y)
  let J := fun (P Q A B C : (y : M) → TangentSpace (𝓡 n) y) y =>
    N P (K Q A B C) y - K (N P Q) A B C y -
      K Q (N P A) B C y - K Q A (N P B) C y - K Q A B (N P C) y
  let I2 := fun (P Q A B : (y : M) → TangentSpace (𝓡 n) y) y =>
    mvfderiv (𝓡 n) (H Q A B) y (P y) -
      H (N P Q) A B y - H Q (N P A) B y - H Q A (N P B) y
  let S := fun W : (y : M) → TangentSpace (𝓡 n) y =>
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) V
  have hXV : S X := hX.mono inter_subset_left
  have hYV : S Y := hY.mono inter_subset_left
  have hBV : S B := hB.mono inter_subset_left
  have hCV : S C := hC.mono inter_subset_left
  have hN (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (N A B) :=
    D.contMDiffOn_connection_apply hV A B hA hB
  have hL (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) : S (L A B) := by
    intro y hy
    exact ((hA.contMDiffAt (hV.mem_nhds hy)).mlieBracket_vectorField
      (hB.contMDiffAt (hV.mem_nhds hy)) (m := ⊤) (n := ⊤) (by simp)).contMDiffWithinAt
  have hR (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) : S (R A B C) :=
    ((hN A _ hA (hN B C hB hC)).sub_section
      (hN B _ hB (hN A C hA hC))).sub_section
        (hN _ C (hL A B hA hB) hC)
  have hEvalue (i : ι) {y : M} (hy : y ∈ e.baseSet) :
      E i y = e.basisAt b0 hy i := by
    simp only [E, FiberBundle.extend, Bundle.Trivialization.basisAt, b0,
      Module.Basis.map_apply, Bundle.Trivialization.linearEquivAt_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
    rfl
  have hE (i : ι) : S (E i) := by
    apply ((e.contMDiffOn_localFrame_baseSet (I := 𝓡 n) ∞ b0 i).mono
      (inter_subset_right : V ⊆ e.baseSet)).congr
    intro y hy
    change (⟨y, E i y⟩ : Bundle.TotalSpace (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n))) = ⟨y, e.localFrame b0 i y⟩
    rw [hEvalue i hy.2, e.localFrame_apply_of_mem_baseSet b0 hy.2]
  have hEself (i : ι) : E i x = b i :=
    FiberBundle.extend_apply_self (EuclideanSpace ℝ (Fin n)) (b i)
  let c := b.coord
  have hc (v : TangentSpace (𝓡 n) x) (i : ι) :
      c i v = b.repr v i := rfl
  obtain ⟨T, hT⟩ := exists_curvature_trilinearMap D x
  have heval (A B C : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) (hC : S C) :
      R A B C x = T (A x) (B x) (C x) :=
    ((hT (A x) (B x) (C x)).trans
      (curvature_eq_curvatureOnFields D hV A B C hA hB hC hxV)).symm
  have htrace (A B : (y : M) → TangentSpace (𝓡 n) y)
      (hA : S A) (hB : S B) :
      D.ricci x (A x) (B x) = ∑ i, c i (R (E i) A B x) := by
    rw [ricci_eq_sum_basis_of_curvature_pairing D x (A x) (B x) b]
    apply Finset.sum_congr rfl
    intro i _
    rw [hc]
    apply congrArg (fun v => b.repr v i)
    simpa only [hEself] using
      (curvature_eq_curvatureOnFields D hV (E i) A B (hE i) hA hB hxV)
  have hHXY := ricci_second_covariant_derivative_eq_sum_basis
    D hV X Y B C hXV hYV hBV hCV hxV b
  have hHYX := ricci_second_covariant_derivative_eq_sum_basis
    D hV Y X B C hYV hXV hBV hCV hxV b
  change I2 X Y B C x = ∑ i, c i (J X Y (E i) B C x) at hHXY
  change I2 Y X B C x = ∑ i, c i (J Y X (E i) B C x) at hHYX
  let A0 := T (X x) (Y x)
  let B0 := ((T.flip (B x)).flip (C x))
  have hrow
      (A0 B0 : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x)
      (i : ι) :
      c i (A0 (B0 (b i))) =
        ∑ j, c j (B0 (b i)) * c i (A0 (b j)) := by
    conv_lhs => rw [← b.sum_repr (B0 (b i))]
    simp only [map_sum, map_smul, smul_eq_mul]
    simp only [hc]
  have hcancel
      (A0 B0 : TangentSpace (𝓡 n) x →ₗ[ℝ] TangentSpace (𝓡 n) x) :
      (∑ i, c i (A0 (B0 (b i)))) = ∑ i, c i (B0 (A0 (b i))) := by
    simp_rw [hrow]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have houtput (i : ι) :
      R X Y (R (E i) B C) x = A0 (B0 (b i)) := by
    rw [heval X Y _ hXV hYV (hR _ B C (hE i) hBV hCV),
      heval (E i) B C (hE i) hBV hCV, hEself]
    rfl
  have hinput (i : ι) :
      R (R X Y (E i)) B C x = B0 (A0 (b i)) := by
    rw [heval _ B C (hR X Y _ hXV hYV (hE i)) hBV hCV,
      heval X Y (E i) hXV hYV (hE i), hEself]
    rfl
  have hreact (i : ι) :
      c i (J X Y (E i) B C x - J Y X (E i) B C x) =
        c i (A0 (B0 (b i))) - c i (B0 (A0 (b i))) -
          c i (R (E i) (R X Y B) C x) - c i (R (E i) B (R X Y C) x) := by
    have hh := curvatureOnFields_second_derivative_commutator
      D hV X Y (E i) B C hXV hYV (hE i) hBV hCV hxV
    change J X Y (E i) B C x - J Y X (E i) B C x =
      R X Y (R (E i) B C) x - R (R X Y (E i)) B C x -
        R (E i) (R X Y B) C x - R (E i) B (R X Y C) x at hh
    rw [houtput i, hinput i] at hh
    simpa only [map_sub] using congrArg (c i) hh
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
    rfl (fun i _ => hreact i)
  simp only [map_sub, Finset.sum_sub_distrib] at hsum
  rw [hcancel A0 B0] at hsum
  change I2 X Y B C x - I2 Y X B C x =
    -D.ricci x (R X Y B x) (C x) - D.ricci x (B x) (R X Y C x)
  rw [hHXY, hHYX, htrace (R X Y B) C (hR X Y B hXV hYV hBV) hCV,
    htrace B (R X Y C) hBV (hR X Y C hXV hYV hCV)]
  linarith only [hsum]

end PoincareConjecture.Proofs.M03

section LiteralSuccessorPatterns

set_option maxHeartbeats 4000000

namespace PoincareConjecture.Proofs.M03.CurvatureResidualPattern

def literalRead {V : Type*} {k : ℕ} (P : V) (Z : Fin (k + 3) → V)
    (z : V) (ends : Fin 4 → V) : (Fin (k + 5) ⊕ Fin 4) → V :=
  Sum.elim (Fin.cons P (Fin.snoc Z z)) ends

def co1Slots (k : ℕ) : (Fin 4 ⊕ Fin (k + 5)) ≃ (Fin (k + 5) ⊕ Fin 4) where
  toFun
    | .inl i => ![.inl 0, .inr 0, .inr 2, .inl (Fin.last (k + 4))] i
    | .inr i => (Fin.cons (Sum.inr 1)
        (Fin.snoc (fun j : Fin (k + 3) => Sum.inl j.castSucc.succ) (Sum.inr 3)) :
          Fin (k + 5) → Fin (k + 5) ⊕ Fin 4) i
  invFun
    | .inl i => (Fin.cons (Sum.inl 0)
        (Fin.snoc (fun j : Fin (k + 3) => Sum.inr j.castSucc.succ) (Sum.inl 3)) :
          Fin (k + 5) → Fin 4 ⊕ Fin (k + 5)) i
    | .inr i => ![.inl 1, .inr 0, .inl 2, .inr (Fin.last (k + 4))] i
  left_inv := by
    intro s
    rcases s with i | i
    · fin_cases i <;> simp
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.lastCases ?_ (fun l => ?_) j <;> simp
  right_inv := by
    intro s
    rcases s with i | i
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.lastCases ?_ (fun l => ?_) j <;> simp
    · fin_cases i <;> simp

def co5Slots (k : ℕ) : (Fin 5 ⊕ Fin (k + 4)) ≃ (Fin (k + 5) ⊕ Fin 4) where
  toFun
    | .inl i => ![.inr 0, .inl 0, .inr 1, .inr 2, .inl (Fin.last (k + 4))] i
    | .inr i => (Fin.snoc (fun j : Fin (k + 3) => Sum.inl j.castSucc.succ)
        (Sum.inr 3) : Fin (k + 4) → Fin (k + 5) ⊕ Fin 4) i
  invFun
    | .inl i => (Fin.cons (Sum.inl 1)
        (Fin.snoc (fun j : Fin (k + 3) => Sum.inr j.castSucc) (Sum.inl 4)) :
          Fin (k + 5) → Fin 5 ⊕ Fin (k + 4)) i
    | .inr i => ![.inl 0, .inl 2, .inl 3, .inr (Fin.last (k + 3))] i
  left_inv := by
    intro s
    rcases s with i | i
    · fin_cases i <;> simp
    · refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv := by
    intro s
    rcases s with i | i
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.lastCases ?_ (fun l => ?_) j <;> simp
    · fin_cases i <;> simp

def co2Slots (k : ℕ) : (Fin 4 ⊕ Fin (k + 5)) ≃ (Fin (k + 5) ⊕ Fin 4) :=
  ((Equiv.swap (.inl 2) (.inr 0)).trans
    (Equiv.swap (.inl 3) (.inr (Fin.last (k + 4))))).trans (co1Slots k)

def co3Slots (k : ℕ) : (Fin 4 ⊕ Fin (k + 5)) ≃ (Fin (k + 5) ⊕ Fin 4) :=
  (Equiv.swap (.inl 1) (.inr 0)).trans (co1Slots k)

def co4Slots (k : ℕ) (l : Fin (k + 3)) :
    (Fin 4 ⊕ Fin (k + 5)) ≃ (Fin (k + 5) ⊕ Fin 4) :=
  ((Equiv.swap (.inl 2) (.inr l.castSucc.succ)).trans
    (Equiv.swap (.inl 3) (.inr (Fin.last (k + 4))))).trans (co1Slots k)

def co6Slots (k : ℕ) (l : Fin (k + 3)) :
    (Fin 4 ⊕ Fin (k + 5)) ≃ (Fin (k + 5) ⊕ Fin 4) :=
  ((Equiv.swap (.inl 2) (.inr l.castSucc.succ)).trans
    (Equiv.swap (.inl 3) (.inr (Fin.last (k + 4))))).trans (co3Slots k)

def co7Slots (k : ℕ) (l : Fin (k + 3)) :
    (Fin 5 ⊕ Fin (k + 4)) ≃ (Fin (k + 5) ⊕ Fin 4) :=
  ((Equiv.swap (.inl 3) (.inr l.castSucc)).trans
    (Equiv.swap (.inl 4) (.inr (Fin.last (k + 3))))).trans (co5Slots k)

def bPerm1 : Equiv.Perm (Fin 5) where
  toFun := ![1, 0, 3, 4, 2]
  invFun := ![1, 0, 4, 2, 3]
  left_inv := by intro j; fin_cases j <;> rfl
  right_inv := by intro j; fin_cases j <;> rfl

def bPerm2 : Equiv.Perm (Fin 5) where
  toFun := ![3, 0, 4, 1, 2]
  invFun := ![1, 3, 4, 0, 2]
  left_inv := by intro j; fin_cases j <;> rfl
  right_inv := by intro j; fin_cases j <;> rfl

def bPerm3 : Equiv.Perm (Fin 5) where
  toFun := ![4, 0, 1, 3, 2]
  invFun := ![1, 2, 4, 3, 0]
  left_inv := by intro j; fin_cases j <;> rfl
  right_inv := by intro j; fin_cases j <;> rfl

def permuteLeft {m r k : ℕ} (p : Equiv.Perm (Fin m))
    (e : (Fin m ⊕ Fin r) ≃ (Fin (k + 5) ⊕ Fin 4)) :
    (Fin m ⊕ Fin r) ≃ (Fin (k + 5) ⊕ Fin 4) :=
  (Equiv.sumCongr p (Equiv.refl _)).trans e

def bOut1Slots (k : ℕ) := permuteLeft bPerm1 (co5Slots k)
def bOut2Slots (k : ℕ) := permuteLeft bPerm2 (co5Slots k)
def bOut3Slots (k : ℕ) := permuteLeft bPerm3 (co5Slots k)
def bIn1Slots (k : ℕ) (l : Fin (k + 3)) := permuteLeft bPerm1 (co7Slots k l)
def bIn2Slots (k : ℕ) (l : Fin (k + 3)) := permuteLeft bPerm2 (co7Slots k l)
def bIn3Slots (k : ℕ) (l : Fin (k + 3)) := permuteLeft bPerm3 (co7Slots k l)

def co1 (k : ℕ) : CurvatureResidualPattern (k + 1) := ⟨0, k + 1, 1, co1Slots k⟩
def co2 (k : ℕ) : CurvatureResidualPattern (k + 1) := ⟨0, k + 1, -1, co2Slots k⟩
def co3 (k : ℕ) : CurvatureResidualPattern (k + 1) := ⟨0, k + 1, 1, co3Slots k⟩
def co4 (k : ℕ) (l : Fin (k + 3)) : CurvatureResidualPattern (k + 1) :=
  ⟨0, k + 1, -1, co4Slots k l⟩
def co5 (k : ℕ) : CurvatureResidualPattern (k + 1) := ⟨1, k, 1, co5Slots k⟩
def co6 (k : ℕ) (l : Fin (k + 3)) : CurvatureResidualPattern (k + 1) :=
  ⟨0, k + 1, -1, co6Slots k l⟩
def co7 (k : ℕ) (l : Fin (k + 3)) : CurvatureResidualPattern (k + 1) :=
  ⟨1, k, -1, co7Slots k l⟩
def bOut1 (k : ℕ) : CurvatureResidualPattern (k + 1) := ⟨1, k, -1, bOut1Slots k⟩
def bOut2 (k : ℕ) : CurvatureResidualPattern (k + 1) := ⟨1, k, -1, bOut2Slots k⟩
def bOut3 (k : ℕ) : CurvatureResidualPattern (k + 1) := ⟨1, k, 1, bOut3Slots k⟩
def bIn1 (k : ℕ) (l : Fin (k + 3)) : CurvatureResidualPattern (k + 1) :=
  ⟨1, k, 1, bIn1Slots k l⟩
def bIn2 (k : ℕ) (l : Fin (k + 3)) : CurvatureResidualPattern (k + 1) :=
  ⟨1, k, 1, bIn2Slots k l⟩
def bIn3 (k : ℕ) (l : Fin (k + 3)) : CurvatureResidualPattern (k + 1) :=
  ⟨1, k, -1, bIn3Slots k l⟩

theorem fill_co1 {V : Type*} {k : ℕ} (P : V) (Z : Fin (k + 3) → V)
    (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (co1Slots k (.inl j))) =
      ![P, ends 0, ends 2, z] ∧
    (fun j => literalRead P Z z ends (co1Slots k (.inr j))) =
      Fin.cons (ends 1) (Fin.snoc Z (ends 3)) := by
  constructor
  · funext j
    fin_cases j <;> simp [literalRead, co1Slots]
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [literalRead, co1Slots]
    · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [literalRead, co1Slots]

theorem fill_co2 {V : Type*} {k : ℕ} (P : V) (Z : Fin (k + 3) → V)
    (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (co2Slots k (.inl j))) =
      ![P, ends 0, ends 1, ends 3] ∧
    (fun j => literalRead P Z z ends (co2Slots k (.inr j))) =
      Fin.cons (ends 2) (Fin.snoc Z z) := by
  constructor
  · funext j
    fin_cases j <;> simp [literalRead, co2Slots, co1Slots, Equiv.swap_apply_def]
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [literalRead, co2Slots, co1Slots, Equiv.swap_apply_def]
    · refine Fin.lastCases ?_ (fun j => ?_) j <;>
        simp [literalRead, co2Slots, co1Slots, Equiv.swap_apply_def]

theorem fill_co3 {V : Type*} {k : ℕ} (P : V) (Z : Fin (k + 3) → V)
    (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (co3Slots k (.inl j))) =
      ![P, ends 1, ends 2, z] ∧
    (fun j => literalRead P Z z ends (co3Slots k (.inr j))) =
      Fin.cons (ends 0) (Fin.snoc Z (ends 3)) := by
  constructor
  · funext j
    fin_cases j <;> simp [literalRead, co3Slots, co1Slots, Equiv.swap_apply_def]
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [literalRead, co3Slots, co1Slots]
    · refine Fin.lastCases ?_ (fun j => ?_) j <;>
        simp [literalRead, co3Slots, co1Slots, Equiv.swap_apply_def]

theorem fill_co4 {V : Type*} {k : ℕ} (l : Fin (k + 3)) (P : V)
    (Z : Fin (k + 3) → V) (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (co4Slots k l (.inl j))) =
      ![P, ends 0, Z l, ends 3] ∧
    (fun j => literalRead P Z z ends (co4Slots k l (.inr j))) =
      Fin.cons (ends 1) (Fin.snoc (Function.update Z l (ends 2)) z) := by
  have hlast : (Fin.last (k + 4) : Fin (k + 5)) ≠ l.castSucc.succ := by
    intro h
    exact Fin.castSucc_ne_last l (Fin.succ_inj.mp h.symm)
  constructor
  · funext j
    fin_cases j <;> simp [literalRead, co4Slots, co1Slots, Equiv.swap_apply_def]
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [literalRead, co4Slots, co1Slots, Equiv.swap_apply_def,
        (Fin.succ_ne_zero l.castSucc).symm]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [literalRead, co4Slots, co1Slots, Equiv.swap_apply_def, hlast,
          (Fin.castSucc_ne_last l).symm]
      · by_cases hj : j = l
        · subst j
          simp [literalRead, co4Slots, co1Slots, Equiv.swap_apply_def]
        · simp [literalRead, co4Slots, co1Slots, Equiv.swap_apply_def, hj]

theorem fill_co5 {V : Type*} {k : ℕ} (P : V) (Z : Fin (k + 3) → V)
    (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (co5Slots k (.inl j))) =
      ![ends 0, P, ends 1, ends 2, z] ∧
    (fun j => literalRead P Z z ends (co5Slots k (.inr j))) =
      Fin.snoc Z (ends 3) := by
  constructor
  · funext j
    fin_cases j <;> simp [literalRead, co5Slots]
  · funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [literalRead, co5Slots]

theorem fill_co6 {V : Type*} {k : ℕ} (l : Fin (k + 3)) (P : V)
    (Z : Fin (k + 3) → V) (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (co6Slots k l (.inl j))) =
      ![P, ends 1, Z l, ends 3] ∧
    (fun j => literalRead P Z z ends (co6Slots k l (.inr j))) =
      Fin.cons (ends 0) (Fin.snoc (Function.update Z l (ends 2)) z) := by
  have hlast : (Fin.last (k + 4) : Fin (k + 5)) ≠ l.castSucc.succ := by
    intro h
    exact Fin.castSucc_ne_last l (Fin.succ_inj.mp h.symm)
  constructor
  · funext j
    fin_cases j <;> simp [literalRead, co6Slots, co3Slots, co1Slots, Equiv.swap_apply_def]
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [literalRead, co6Slots, co3Slots, co1Slots, Equiv.swap_apply_def,
        (Fin.succ_ne_zero l.castSucc).symm]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp [literalRead, co6Slots, co3Slots, co1Slots, Equiv.swap_apply_def, hlast,
          (Fin.castSucc_ne_last l).symm]
      · by_cases hj : j = l
        · subst j
          simp [literalRead, co6Slots, co3Slots, co1Slots, Equiv.swap_apply_def]
        · simp [literalRead, co6Slots, co3Slots, co1Slots, Equiv.swap_apply_def, hj]

theorem fill_co7 {V : Type*} {k : ℕ} (l : Fin (k + 3)) (P : V)
    (Z : Fin (k + 3) → V) (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (co7Slots k l (.inl j))) =
      ![ends 0, P, ends 1, Z l, ends 3] ∧
    (fun j => literalRead P Z z ends (co7Slots k l (.inr j))) =
      Fin.snoc (Function.update Z l (ends 2)) z := by
  constructor
  · funext j
    fin_cases j <;> simp [literalRead, co7Slots, co5Slots, Equiv.swap_apply_def]
  · funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [literalRead, co7Slots, co5Slots, Equiv.swap_apply_def,
        (Fin.castSucc_ne_last l).symm]
    · by_cases hj : j = l
      · subst j
        simp [literalRead, co7Slots, co5Slots, Equiv.swap_apply_def]
      · simp [literalRead, co7Slots, co5Slots, Equiv.swap_apply_def, hj]

theorem fill_permuteLeft {V : Type*} {m r k : ℕ} (p : Equiv.Perm (Fin m))
    (e : (Fin m ⊕ Fin r) ≃ (Fin (k + 5) ⊕ Fin 4))
    (f : (Fin (k + 5) ⊕ Fin 4) → V) (L : Fin m → V) (R : Fin r → V)
    (h : (fun j => f (e (.inl j))) = L ∧ (fun j => f (e (.inr j))) = R) :
    (fun j => f (permuteLeft p e (.inl j))) = (fun j => L (p j)) ∧
    (fun j => f (permuteLeft p e (.inr j))) = R :=
  ⟨funext (fun j => congrFun h.1 (p j)), h.2⟩

theorem bPerm1_vec {V : Type*} (a b c d e : V) :
    (fun j => ![a, b, c, d, e] (bPerm1 j)) = ![b, a, d, e, c] := by
  funext j
  fin_cases j <;> rfl

theorem bPerm2_vec {V : Type*} (a b c d e : V) :
    (fun j => ![a, b, c, d, e] (bPerm2 j)) = ![d, a, e, b, c] := by
  funext j
  fin_cases j <;> rfl

theorem bPerm3_vec {V : Type*} (a b c d e : V) :
    (fun j => ![a, b, c, d, e] (bPerm3 j)) = ![e, a, b, d, c] := by
  funext j
  fin_cases j <;> rfl

theorem fill_bOut1 {V : Type*} {k : ℕ} (P : V) (Z : Fin (k + 3) → V)
    (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (bOut1Slots k (.inl j))) =
      ![P, ends 0, ends 2, z, ends 1] ∧
    (fun j => literalRead P Z z ends (bOut1Slots k (.inr j))) = Fin.snoc Z (ends 3) := by
  have h := fill_permuteLeft bPerm1 (co5Slots k) (literalRead P Z z ends) _ _
    (fill_co5 P Z z ends)
  exact ⟨h.1.trans (bPerm1_vec _ _ _ _ _), h.2⟩

theorem fill_bOut2 {V : Type*} {k : ℕ} (P : V) (Z : Fin (k + 3) → V)
    (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (bOut2Slots k (.inl j))) =
      ![ends 2, ends 0, z, P, ends 1] ∧
    (fun j => literalRead P Z z ends (bOut2Slots k (.inr j))) = Fin.snoc Z (ends 3) := by
  have h := fill_permuteLeft bPerm2 (co5Slots k) (literalRead P Z z ends) _ _
    (fill_co5 P Z z ends)
  exact ⟨h.1.trans (bPerm2_vec _ _ _ _ _), h.2⟩

theorem fill_bOut3 {V : Type*} {k : ℕ} (P : V) (Z : Fin (k + 3) → V)
    (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (bOut3Slots k (.inl j))) =
      ![z, ends 0, P, ends 2, ends 1] ∧
    (fun j => literalRead P Z z ends (bOut3Slots k (.inr j))) = Fin.snoc Z (ends 3) := by
  have h := fill_permuteLeft bPerm3 (co5Slots k) (literalRead P Z z ends) _ _
    (fill_co5 P Z z ends)
  exact ⟨h.1.trans (bPerm3_vec _ _ _ _ _), h.2⟩

theorem fill_bIn1 {V : Type*} {k : ℕ} (l : Fin (k + 3)) (P : V)
    (Z : Fin (k + 3) → V) (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (bIn1Slots k l (.inl j))) =
      ![P, ends 0, Z l, ends 3, ends 1] ∧
    (fun j => literalRead P Z z ends (bIn1Slots k l (.inr j))) =
      Fin.snoc (Function.update Z l (ends 2)) z := by
  have h := fill_permuteLeft bPerm1 (co7Slots k l) (literalRead P Z z ends) _ _
    (fill_co7 l P Z z ends)
  exact ⟨h.1.trans (bPerm1_vec _ _ _ _ _), h.2⟩

theorem fill_bIn2 {V : Type*} {k : ℕ} (l : Fin (k + 3)) (P : V)
    (Z : Fin (k + 3) → V) (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (bIn2Slots k l (.inl j))) =
      ![Z l, ends 0, ends 3, P, ends 1] ∧
    (fun j => literalRead P Z z ends (bIn2Slots k l (.inr j))) =
      Fin.snoc (Function.update Z l (ends 2)) z := by
  have h := fill_permuteLeft bPerm2 (co7Slots k l) (literalRead P Z z ends) _ _
    (fill_co7 l P Z z ends)
  exact ⟨h.1.trans (bPerm2_vec _ _ _ _ _), h.2⟩

theorem fill_bIn3 {V : Type*} {k : ℕ} (l : Fin (k + 3)) (P : V)
    (Z : Fin (k + 3) → V) (z : V) (ends : Fin 4 → V) :
    (fun j => literalRead P Z z ends (bIn3Slots k l (.inl j))) =
      ![ends 3, ends 0, P, Z l, ends 1] ∧
    (fun j => literalRead P Z z ends (bIn3Slots k l (.inr j))) =
      Fin.snoc (Function.update Z l (ends 2)) z := by
  have h := fill_permuteLeft bPerm3 (co7Slots k l) (literalRead P Z z ends) _ _
    (fill_co7 l P Z z ends)
  exact ⟨h.1.trans (bPerm3_vec _ _ _ _ _), h.2⟩

theorem evaluate_of_fills {ι V : Type*} [Fintype ι] {p q k : ℕ}
    (c : ℤ) (slots : (Fin (p + 4) ⊕ Fin (q + 4)) ≃ (Fin (k + 4) ⊕ Fin 4))
    (a : ι → ι → ℝ) (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ)
    (E : ι → V) (X : Fin (k + 4) → V)
    (L : (Fin 4 → V) → Fin (p + 4) → V)
    (R : (Fin 4 → V) → Fin (q + 4) → V)
    (hfill : ∀ ends, (fun j => Sum.elim X ends (slots (.inl j))) = L ends ∧
      (fun j => Sum.elim X ends (slots (.inr j))) = R ends) :
    evaluate (⟨p, q, c, slots⟩ : CurvatureResidualPattern k) a low E X =
      (c : ℝ) * ∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low p (L (fun j => E (γ j))) * low q (R (fun j => E (γ j)))) := by
  unfold evaluate
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  rw [(hfill (fun j => E (γ j))).1, (hfill (fun j => E (γ j))).2]

section Evaluation

variable {ι V : Type*} [Fintype ι]
variable (k : ℕ) (a : ι → ι → ℝ)
  (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ) (E : ι → V)
  (P : V) (Z : Fin (k + 3) → V) (z : V)

theorem evaluate_co1 :
    evaluate (co1 k) a low E (Fin.cons P (Fin.snoc Z z)) =
      (∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 0 (![P, E (γ 0), E (γ 2), z]) *
          low (k + 1) (Fin.cons (E (γ 1)) (Fin.snoc Z (E (γ 3)))))) := by
  simpa only [co1, Int.cast_one, one_mul] using
    (evaluate_of_fills (p := 0) (q := k + 1) (k := k + 1)
      (1) (co1Slots k) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![P, ends 0, ends 2, z])
      (fun ends => Fin.cons (ends 1) (Fin.snoc Z (ends 3)))
      (fun ends => fill_co1 P Z z ends))

theorem evaluate_co2 :
    evaluate (co2 k) a low E (Fin.cons P (Fin.snoc Z z)) =
      -(∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 0 (![P, E (γ 0), E (γ 1), E (γ 3)]) *
          low (k + 1) (Fin.cons (E (γ 2)) (Fin.snoc Z z)))) := by
  simpa only [co2, Int.cast_neg, Int.cast_one, neg_one_mul] using
    (evaluate_of_fills (p := 0) (q := k + 1) (k := k + 1)
      (-1) (co2Slots k) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![P, ends 0, ends 1, ends 3])
      (fun ends => Fin.cons (ends 2) (Fin.snoc Z z))
      (fun ends => fill_co2 P Z z ends))

theorem evaluate_co3 :
    evaluate (co3 k) a low E (Fin.cons P (Fin.snoc Z z)) =
      (∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 0 (![P, E (γ 1), E (γ 2), z]) *
          low (k + 1) (Fin.cons (E (γ 0)) (Fin.snoc Z (E (γ 3)))))) := by
  simpa only [co3, Int.cast_one, one_mul] using
    (evaluate_of_fills (p := 0) (q := k + 1) (k := k + 1)
      (1) (co3Slots k) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![P, ends 1, ends 2, z])
      (fun ends => Fin.cons (ends 0) (Fin.snoc Z (ends 3)))
      (fun ends => fill_co3 P Z z ends))

theorem evaluate_co4 (l : Fin (k + 3)) :
    evaluate (co4 k l) a low E (Fin.cons P (Fin.snoc Z z)) =
      -(∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 0 (![P, E (γ 0), Z l, E (γ 3)]) *
          low (k + 1) (Fin.cons (E (γ 1)) (Fin.snoc (Function.update Z l (E (γ 2))) z)))) := by
  simpa only [co4, Int.cast_neg, Int.cast_one, neg_one_mul] using
    (evaluate_of_fills (p := 0) (q := k + 1) (k := k + 1)
      (-1) (co4Slots k l) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![P, ends 0, Z l, ends 3])
      (fun ends => Fin.cons (ends 1) (Fin.snoc (Function.update Z l (ends 2)) z))
      (fun ends => fill_co4 l P Z z ends))

theorem evaluate_co5 :
    evaluate (co5 k) a low E (Fin.cons P (Fin.snoc Z z)) =
      (∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 1 (![E (γ 0), P, E (γ 1), E (γ 2), z]) *
          low (k) (Fin.snoc Z (E (γ 3))))) := by
  simpa only [co5, Int.cast_one, one_mul] using
    (evaluate_of_fills (p := 1) (q := k) (k := k + 1)
      (1) (co5Slots k) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![ends 0, P, ends 1, ends 2, z])
      (fun ends => Fin.snoc Z (ends 3))
      (fun ends => fill_co5 P Z z ends))

theorem evaluate_co6 (l : Fin (k + 3)) :
    evaluate (co6 k l) a low E (Fin.cons P (Fin.snoc Z z)) =
      -(∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 0 (![P, E (γ 1), Z l, E (γ 3)]) *
          low (k + 1) (Fin.cons (E (γ 0)) (Fin.snoc (Function.update Z l (E (γ 2))) z)))) := by
  simpa only [co6, Int.cast_neg, Int.cast_one, neg_one_mul] using
    (evaluate_of_fills (p := 0) (q := k + 1) (k := k + 1)
      (-1) (co6Slots k l) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![P, ends 1, Z l, ends 3])
      (fun ends => Fin.cons (ends 0) (Fin.snoc (Function.update Z l (ends 2)) z))
      (fun ends => fill_co6 l P Z z ends))

theorem evaluate_co7 (l : Fin (k + 3)) :
    evaluate (co7 k l) a low E (Fin.cons P (Fin.snoc Z z)) =
      -(∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 1 (![E (γ 0), P, E (γ 1), Z l, E (γ 3)]) *
          low (k) (Fin.snoc (Function.update Z l (E (γ 2))) z))) := by
  simpa only [co7, Int.cast_neg, Int.cast_one, neg_one_mul] using
    (evaluate_of_fills (p := 1) (q := k) (k := k + 1)
      (-1) (co7Slots k l) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![ends 0, P, ends 1, Z l, ends 3])
      (fun ends => Fin.snoc (Function.update Z l (ends 2)) z)
      (fun ends => fill_co7 l P Z z ends))

theorem evaluate_bOut1 :
    evaluate (bOut1 k) a low E (Fin.cons P (Fin.snoc Z z)) =
      -(∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 1 (![P, E (γ 0), E (γ 2), z, E (γ 1)]) *
          low (k) (Fin.snoc Z (E (γ 3))))) := by
  simpa only [bOut1, Int.cast_neg, Int.cast_one, neg_one_mul] using
    (evaluate_of_fills (p := 1) (q := k) (k := k + 1)
      (-1) (bOut1Slots k) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![P, ends 0, ends 2, z, ends 1])
      (fun ends => Fin.snoc Z (ends 3))
      (fun ends => fill_bOut1 P Z z ends))

theorem evaluate_bOut2 :
    evaluate (bOut2 k) a low E (Fin.cons P (Fin.snoc Z z)) =
      -(∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 1 (![E (γ 2), E (γ 0), z, P, E (γ 1)]) *
          low (k) (Fin.snoc Z (E (γ 3))))) := by
  simpa only [bOut2, Int.cast_neg, Int.cast_one, neg_one_mul] using
    (evaluate_of_fills (p := 1) (q := k) (k := k + 1)
      (-1) (bOut2Slots k) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![ends 2, ends 0, z, P, ends 1])
      (fun ends => Fin.snoc Z (ends 3))
      (fun ends => fill_bOut2 P Z z ends))

theorem evaluate_bOut3 :
    evaluate (bOut3 k) a low E (Fin.cons P (Fin.snoc Z z)) =
      (∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 1 (![z, E (γ 0), P, E (γ 2), E (γ 1)]) *
          low (k) (Fin.snoc Z (E (γ 3))))) := by
  simpa only [bOut3, Int.cast_one, one_mul] using
    (evaluate_of_fills (p := 1) (q := k) (k := k + 1)
      (1) (bOut3Slots k) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![z, ends 0, P, ends 2, ends 1])
      (fun ends => Fin.snoc Z (ends 3))
      (fun ends => fill_bOut3 P Z z ends))

theorem evaluate_bIn1 (l : Fin (k + 3)) :
    evaluate (bIn1 k l) a low E (Fin.cons P (Fin.snoc Z z)) =
      (∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 1 (![P, E (γ 0), Z l, E (γ 3), E (γ 1)]) *
          low (k) (Fin.snoc (Function.update Z l (E (γ 2))) z))) := by
  simpa only [bIn1, Int.cast_one, one_mul] using
    (evaluate_of_fills (p := 1) (q := k) (k := k + 1)
      (1) (bIn1Slots k l) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![P, ends 0, Z l, ends 3, ends 1])
      (fun ends => Fin.snoc (Function.update Z l (ends 2)) z)
      (fun ends => fill_bIn1 l P Z z ends))

theorem evaluate_bIn2 (l : Fin (k + 3)) :
    evaluate (bIn2 k l) a low E (Fin.cons P (Fin.snoc Z z)) =
      (∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 1 (![Z l, E (γ 0), E (γ 3), P, E (γ 1)]) *
          low (k) (Fin.snoc (Function.update Z l (E (γ 2))) z))) := by
  simpa only [bIn2, Int.cast_one, one_mul] using
    (evaluate_of_fills (p := 1) (q := k) (k := k + 1)
      (1) (bIn2Slots k l) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![Z l, ends 0, ends 3, P, ends 1])
      (fun ends => Fin.snoc (Function.update Z l (ends 2)) z)
      (fun ends => fill_bIn2 l P Z z ends))

theorem evaluate_bIn3 (l : Fin (k + 3)) :
    evaluate (bIn3 k l) a low E (Fin.cons P (Fin.snoc Z z)) =
      -(∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
        (low 1 (![E (γ 3), E (γ 0), P, Z l, E (γ 1)]) *
          low (k) (Fin.snoc (Function.update Z l (E (γ 2))) z))) := by
  simpa only [bIn3, Int.cast_neg, Int.cast_one, neg_one_mul] using
    (evaluate_of_fills (p := 1) (q := k) (k := k + 1)
      (-1) (bIn3Slots k l) a low E (Fin.cons P (Fin.snoc Z z))
      (fun ends => ![ends 3, ends 0, P, Z l, ends 1])
      (fun ends => Fin.snoc (Function.update Z l (ends 2)) z)
      (fun ends => fill_bIn3 l P Z z ends))

end Evaluation

def coefficientMass {k : ℕ} (ps : List (CurvatureResidualPattern k)) : ℕ :=
  (ps.map (fun r => r.2.2.1.natAbs)).sum

def spatialPatterns (k : ℕ) : List (CurvatureResidualPattern (k + 1)) :=
  [co1 k, co2 k] ++
    (List.finRange (k + 3)).map (co4 k) ++
    [co5 k, co3 k] ++
    (List.finRange (k + 3)).map (co6 k) ++
    (List.finRange (k + 3)).map (co7 k)

def connectionPatterns (k : ℕ) : List (CurvatureResidualPattern (k + 1)) :=
  [bOut1 k, bOut2 k, bOut3 k] ++
    (List.finRange (k + 3)).flatMap
      (fun l => [bIn1 k l, bIn2 k l, bIn3 k l])

def correctionPatterns (k : ℕ) : List (CurvatureResidualPattern (k + 1)) :=
  connectionPatterns k ++ spatialPatterns k

def derivativePatterns {k : ℕ} (ps : List (CurvatureResidualPattern k)) :
    List (CurvatureResidualPattern (k + 1)) :=
  ps.flatMap (fun r => [differentiateLeft r, differentiateRight r])

def nextPatterns (k : ℕ) (ps : List (CurvatureResidualPattern k)) :
    List (CurvatureResidualPattern (k + 1)) :=
  derivativePatterns ps ++ correctionPatterns k

theorem coefficientMass_append {k : ℕ} (ps qs : List (CurvatureResidualPattern k)) :
    coefficientMass (ps ++ qs) = coefficientMass ps + coefficientMass qs := by
  simp [coefficientMass]

theorem coefficientMass_spatialPatterns (k : ℕ) :
    coefficientMass (spatialPatterns k) = 3 * k + 13 := by
  simp [coefficientMass, spatialPatterns, co1, co2, co3, co4, co5, co6, co7,
    Function.comp_def, List.map_const']
  omega

theorem coefficientMass_connectionPatterns (k : ℕ) :
    coefficientMass (connectionPatterns k) = 3 * k + 12 := by
  have haux (ls : List (Fin (k + 3))) :
      coefficientMass (ls.flatMap (fun l => [bIn1 k l, bIn2 k l, bIn3 k l])) =
        3 * ls.length := by
    induction ls with
    | nil => simp [coefficientMass]
    | cons l ls ih =>
        simp only [List.flatMap_cons, coefficientMass_append, ih, List.length_cons]
        simp [coefficientMass, bIn1, bIn2, bIn3]
        omega
  rw [connectionPatterns, coefficientMass_append, haux]
  simp [coefficientMass, bOut1, bOut2, bOut3]
  omega

theorem coefficientMass_correctionPatterns (k : ℕ) :
    coefficientMass (correctionPatterns k) = 6 * k + 25 := by
  rw [correctionPatterns, coefficientMass_append, coefficientMass_connectionPatterns,
    coefficientMass_spatialPatterns]
  omega

theorem coefficientMass_derivativePatterns {k : ℕ}
    (ps : List (CurvatureResidualPattern k)) :
    coefficientMass (derivativePatterns ps) = 2 * coefficientMass ps := by
  induction ps with
  | nil => simp [derivativePatterns, coefficientMass]
  | cons r rs ih =>
      change coefficientMass
          ([differentiateLeft r, differentiateRight r] ++ derivativePatterns rs) =
        2 * coefficientMass (r :: rs)
      rw [coefficientMass_append, ih]
      simp [coefficientMass, coefficient_differentiateLeft,
        coefficient_differentiateRight]
      omega

theorem coefficientMass_nextPatterns (k : ℕ) (ps : List (CurvatureResidualPattern k)) :
    coefficientMass (nextPatterns k ps) = 2 * coefficientMass ps + 6 * k + 25 := by
  rw [nextPatterns, coefficientMass_append, coefficientMass_derivativePatterns,
    coefficientMass_correctionPatterns]
  omega

theorem sum_spatialPatterns (k : ℕ) (ev : CurvatureResidualPattern (k + 1) → ℝ) :
    ((spatialPatterns k).map ev).sum =
      ev (co1 k) + ev (co2 k) + (∑ l, ev (co4 k l)) +
        ev (co5 k) + ev (co3 k) + (∑ l, ev (co6 k l)) + ∑ l, ev (co7 k l) := by
  simp only [spatialPatterns, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.map_map, Function.comp_def,
    ← Fin.sum_univ_def]
  ring

theorem sum_connectionPatterns (k : ℕ) (ev : CurvatureResidualPattern (k + 1) → ℝ) :
    ((connectionPatterns k).map ev).sum =
      ev (bOut1 k) + ev (bOut2 k) + ev (bOut3 k) +
        ∑ l, (ev (bIn1 k l) + ev (bIn2 k l) + ev (bIn3 k l)) := by
  have haux (ls : List (Fin (k + 3))) :
      ((ls.flatMap (fun l => [bIn1 k l, bIn2 k l, bIn3 k l])).map ev).sum =
        (ls.map (fun l => ev (bIn1 k l) + ev (bIn2 k l) + ev (bIn3 k l))).sum := by
    induction ls with
    | nil => rfl
    | cons l ls ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ih]
        ring
  simp only [connectionPatterns, List.map_append, List.sum_append, haux,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    ← Fin.sum_univ_def]
  ring

end PoincareConjecture.Proofs.M03.CurvatureResidualPattern

end LiteralSuccessorPatterns

section LiteralBasePatterns

set_option maxHeartbeats 4000000

namespace PoincareConjecture.Proofs.M03.CurvatureResidualPattern

private abbrev S4 := Fin 4 ⊕ Fin 4

private noncomputable abbrev baseEquiv
    (left right : Fin 4 → S4)
    (h : Function.Bijective (Sum.elim left right)) : S4 ≃ S4 :=
  Equiv.ofBijective (Sum.elim left right) h

noncomputable abbrev basePattern1 : CurvatureResidualPattern 0 :=
  ⟨0, 0, 1, baseEquiv
    ![.inl 0, .inl 1, .inr 2, .inr 1]
    ![.inr 0, .inr 3, .inl 2, .inl 3] (by decide)⟩

noncomputable abbrev basePattern2 : CurvatureResidualPattern 0 :=
  ⟨0, 0, -2, baseEquiv
    ![.inl 1, .inr 2, .inr 0, .inl 3]
    ![.inr 3, .inl 0, .inl 2, .inr 1] (by decide)⟩

noncomputable abbrev basePattern3 : CurvatureResidualPattern 0 :=
  ⟨0, 0, 2, baseEquiv
    ![.inr 2, .inl 0, .inr 0, .inl 3]
    ![.inl 1, .inr 3, .inl 2, .inr 1] (by decide)⟩

noncomputable abbrev basePattern4 : CurvatureResidualPattern 0 :=
  ⟨0, 0, 1, baseEquiv
    ![.inl 0, .inl 1, .inl 2, .inr 1]
    ![.inr 0, .inr 2, .inr 3, .inl 3] (by decide)⟩

noncomputable abbrev basePattern5 : CurvatureResidualPattern 0 :=
  ⟨0, 0, -1, baseEquiv
    ![.inl 0, .inr 2, .inr 3, .inr 1]
    ![.inr 0, .inl 1, .inl 2, .inl 3] (by decide)⟩

noncomputable abbrev basePattern6 : CurvatureResidualPattern 0 :=
  ⟨0, 0, -1, baseEquiv
    ![.inl 1, .inr 2, .inr 3, .inr 1]
    ![.inl 0, .inr 0, .inl 2, .inl 3] (by decide)⟩

noncomputable abbrev basePattern7 : CurvatureResidualPattern 0 :=
  ⟨0, 0, -1, baseEquiv
    ![.inl 2, .inr 2, .inr 3, .inr 1]
    ![.inl 0, .inl 1, .inr 0, .inl 3] (by decide)⟩

noncomputable def basePatterns : Fin 7 → CurvatureResidualPattern 0
  | 0 => basePattern1
  | 1 => basePattern2
  | 2 => basePattern3
  | 3 => basePattern4
  | 4 => basePattern5
  | 5 => basePattern6
  | 6 => basePattern7

theorem sum_fin_four
    {ι β : Type*} [Fintype ι] [AddCommMonoid β]
    (f : (Fin 4 → ι) → β) :
    (∑ γ : Fin 4 → ι, f γ) =
      ∑ i0 : ι, ∑ i1 : ι, ∑ i2 : ι, ∑ i3 : ι,
        f ![i0, i1, i2, i3] := by
  let e : (ι × (ι × (ι × ι))) ≃ (Fin 4 → ι) :=
    Equiv.ofBijective
      (fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]) (by
        constructor
        · intro x y h
          rcases x with ⟨x0, x1, x2, x3⟩
          rcases y with ⟨y0, y1, y2, y3⟩
          apply Prod.ext
          · exact congrFun h 0
          · apply Prod.ext
            · exact congrFun h 1
            · apply Prod.ext
              · exact congrFun h 2
              · exact congrFun h 3
        · intro f
          exact ⟨(f 0, f 1, f 2, f 3), by
            funext i
            fin_cases i <;> rfl⟩)
  have hs : (∑ p : ι × (ι × (ι × ι)), f ![p.1, p.2.1, p.2.2.1, p.2.2.2]) =
      ∑ γ : Fin 4 → ι, f γ := Fintype.sum_equiv e _ _ (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using hs.symm

def baseReaction
    {ι V : Type*} [Fintype ι]
    (a : ι → ι → ℝ)
    (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ)
    (E : ι → V) (X : Fin 4 → V) : ℝ :=
  ∑ γ : Fin 4 → ι, (a (γ 0) (γ 1) * a (γ 2) (γ 3)) *
    (low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inl 0, .inl 1, .inr 2, .inr 1] j)) *
      low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inr 0, .inr 3, .inl 2, .inl 3] j)) -
    2 * (low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inl 1, .inr 2, .inr 0, .inl 3] j)) *
      low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inr 3, .inl 0, .inl 2, .inr 1] j))) +
    2 * (low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inr 2, .inl 0, .inr 0, .inl 3] j)) *
      low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inl 1, .inr 3, .inl 2, .inr 1] j))) +
    low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inl 0, .inl 1, .inl 2, .inr 1] j)) *
      low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inr 0, .inr 2, .inr 3, .inl 3] j)) -
    low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inl 0, .inr 2, .inr 3, .inr 1] j)) *
      low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inr 0, .inl 1, .inl 2, .inl 3] j)) -
    low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inl 1, .inr 2, .inr 3, .inr 1] j)) *
      low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inl 0, .inr 0, .inl 2, .inl 3] j)) -
    low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inl 2, .inr 2, .inr 3, .inr 1] j)) *
      low 0 (fun j => Sum.elim X (fun s => E (γ s))
        (![.inl 0, .inl 1, .inr 0, .inl 3] j)))

theorem basePatterns_evaluate
    {ι V : Type*} [Fintype ι]
    (a : ι → ι → ℝ) (low : (m : ℕ) → (Fin (m + 4) → V) → ℝ)
    (E : ι → V) (X : Fin 4 → V) :
    evaluate basePattern1 a low E X + evaluate basePattern2 a low E X +
      evaluate basePattern3 a low E X + evaluate basePattern4 a low E X +
      evaluate basePattern5 a low E X + evaluate basePattern6 a low E X +
      evaluate basePattern7 a low E X = baseReaction a low E X := by
  classical
  simp only [baseReaction, evaluate, basePattern1, basePattern2, basePattern3,
    basePattern4, basePattern5, basePattern6, basePattern7, baseEquiv,
    Equiv.coe_fn_mk, Equiv.ofBijective, Sum.elim_inl, Sum.elim_inr,
    Int.cast_neg, Int.cast_one, Int.cast_ofNat, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro γ _
  ring

end PoincareConjecture.Proofs.M03.CurvatureResidualPattern

end LiteralBasePatterns
