import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.ConnectionScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Fields.MetricPairings

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

noncomputable def covariantTensorDerivativeOnFields (D : LeviCivitaData g) {k : ℕ}
    (T : CovariantTensorEvaluation n M k)
    (X : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y) (x : M) : ℝ :=
  mvfderiv (𝓡 n) (fun y ↦ T y (fun i ↦ X i.succ y)) x (X 0 x) -
    ∑ i, T x (Function.update (fun j ↦ X j.succ x) i
      (D.connection (X i.succ) x (X 0 x)))

theorem contMDiffOn_covariantTensorDerivativeOnFields (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {X : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (covariantTensorDerivativeOnFields D T X) U := by
  classical
  let A (i : Fin k) := fun y ↦ D.connection (X i.succ) y (X 0 y)
  have hA (i : Fin k) :
      ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (A i)) U := by
    intro y hy
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_section_of_metric_pairings g (A i)
    intro v
    let t := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    have hy' : y ∈ U ∩ t.baseSet := ⟨hy, FiberBundle.mem_baseSet_trivializationAt' y⟩
    have hs := contMDiffOn_connection_pairing D (hU.inter t.open_baseSet)
      ((hX 0).mono Set.inter_subset_left) ((hX i.succ).mono Set.inter_subset_left)
      ((contMDiffOn_extend_baseSet v).mono Set.inter_subset_right)
    exact hs.contMDiffAt ((hU.inter t.open_baseSet).mem_nhds hy')
  have hF := hT.2 U hU (fun i ↦ X i.succ) (fun i ↦ hX i.succ)
  have hMain := contMDiffOn_directional_derivative hU hF (hX 0)
  have hC (i : Fin k) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y ↦ T y (Function.update (fun j ↦ X j.succ y) i (A i y))) U := by
    let V := Function.update (fun j : Fin k ↦ X j.succ) i (A i)
    have hV (j : Fin k) :
        ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (V j)) U := by
      by_cases hji : j = i
      · subst j
        simpa only [V, Function.update_self] using hA i
      · simpa only [V, Function.update_of_ne hji] using hX j.succ
    apply (hT.2 U hU V hV).congr
    intro y hy
    congr 1
    funext j
    by_cases hji : j = i <;> simp [V, hji]
  simpa only [covariantTensorDerivativeOnFields, A, Pi.sub_apply] using!
    hMain.sub (contMDiffOn_finsetSum (fun i _ ↦ hC i))

theorem covariantTensorDerivativeOnFields_congr (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (_hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {X Y : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U)
    (hY : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (Y i)) U)
    (hXY : ∀ i y, y ∈ U → X i y = Y i y) {x : M} (hx : x ∈ U) :
    covariantTensorDerivativeOnFields D T X x = covariantTensorDerivativeOnFields D T Y x := by
  have hF : (fun y ↦ T y (fun i ↦ X i.succ y)) =ᶠ[𝓝 x]
      (fun y ↦ T y (fun i ↦ Y i.succ y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    congr 1
    funext i
    exact hXY i.succ y hy
  have hD : mvfderiv (𝓡 n) (fun y ↦ T y (fun i ↦ X i.succ y)) x =
      mvfderiv (𝓡 n) (fun y ↦ T y (fun i ↦ Y i.succ y)) x := hF.mfderiv_eq
  have hDX (i : Fin k) : D.connection (X i.succ) x = D.connection (Y i.succ) x :=
    (D.connection.isCovariantDerivativeOn (s := U)).congr_of_eqOn
      (((hX i.succ) x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
      (((hY i.succ) x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp))
      (hU.mem_nhds hx) (hXY i.succ)
  have htail : (fun i : Fin k ↦ X i.succ x) = (fun i ↦ Y i.succ x) :=
    funext fun i ↦ hXY i.succ x hx
  simp only [covariantTensorDerivativeOnFields, hD, hXY 0 x hx, htail, hDX]

set_option backward.isDefEq.respectTransparency false in
theorem covariantTensorDerivativeOnFields_update_add (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {X : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    {A B : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U)
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U)
    (hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% B) U) (i : Fin (k + 1)) {x : M} (hx : x ∈ U) :
    covariantTensorDerivativeOnFields D T (Function.update X i (A + B)) x =
      covariantTensorDerivativeOnFields D T (Function.update X i A) x +
        covariantTensorDerivativeOnFields D T (Function.update X i B) x := by
  classical
  have hAdd (y : M) (v : Fin k → TangentSpace (𝓡 n) y) (j : Fin k)
      (a b : TangentSpace (𝓡 n) y) : T y (Function.update v j (a + b)) =
        T y (Function.update v j a) + T y (Function.update v j b) := by
    obtain ⟨P, hP⟩ := hT.1 y
    simp only [hP, P.map_update_add]
  cases i using Fin.cases with
  | zero =>
    simp only [covariantTensorDerivativeOnFields,
      Function.update_of_ne (Fin.succ_ne_zero _), Function.update_self,
      Pi.add_apply, map_add, hAdd, Finset.sum_add_distrib]
    ring
  | succ j =>
    let v := fun l : Fin k ↦ X l.succ x
    let F := fun (W : (y : M) → TangentSpace (𝓡 n) y) y ↦
      T y (Function.update (fun l : Fin k ↦ X l.succ y) j (W y))
    let C := fun (W : (y : M) → TangentSpace (𝓡 n) y) (l : Fin k) ↦
      T x (Function.update (Function.update v j (W x)) l
        (D.connection (Function.update X j.succ W l.succ) x (X 0 x)))
    have htup (W : (y : M) → TangentSpace (𝓡 n) y) (y : M) :
        (fun l : Fin k ↦ Function.update X j.succ W l.succ y) =
          Function.update (fun l : Fin k ↦ X l.succ y) j (W y) := by
      funext l
      by_cases hl : l = j <;> simp [Function.update, Fin.succ_inj, hl]
    have hFs {W : (y : M) → TangentSpace (𝓡 n) y}
        (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% W) U) : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F W) U := by
      let V := Function.update (fun l : Fin k ↦ X l.succ) j W
      have hV (l : Fin k) :
          ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
            ∞ (T% (V l)) U := by
        by_cases hl : l = j
        · subst l
          simpa only [V, Function.update_self] using hW
        · simpa only [V, Function.update_of_ne hl] using hX l.succ
      apply (hT.2 U hU V hV).congr
      intro y hy
      dsimp only [F]
      congr 1
      funext l
      by_cases hl : l = j <;> simp [V, hl]
    have hFA := ((hFs hA) x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)
    have hFB := ((hFs hB) x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)
    have hFE : F (A + B) = F A + F B := by
      funext y
      exact hAdd y _ j (A y) (B y)
    have hDE : mvfderiv (𝓡 n) (F (A + B)) x =
        mvfderiv (𝓡 n) (F A) x + mvfderiv (𝓡 n) (F B) x := by
      rw [hFE]
      exact mvfderiv_add hFA hFB
    have hAD := (hA x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)
    have hBD := (hB x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)
    have hCE (l : Fin k) : C (A + B) l = C A l + C B l := by
      by_cases hl : l = j
      · subst l
        simp only [C, Function.update_self, Function.update_idem,
          D.connection.isCovariantDerivativeOnUniv.add hAD hBD, add_apply, hAdd]
      · have hls : l.succ ≠ j.succ := fun h ↦ hl (Fin.succ_injective _ h)
        simp only [C, Function.update_of_ne hls, Function.update_comm (Ne.symm hl),
          Pi.add_apply, hAdd]
    simp only [covariantTensorDerivativeOnFields, htup,
      Function.update_of_ne (Fin.succ_ne_zero j).symm]
    change mvfderiv (𝓡 n) (F (A + B)) x (X 0 x) - ∑ l, C (A + B) l =
      (mvfderiv (𝓡 n) (F A) x (X 0 x) - ∑ l, C A l) +
        (mvfderiv (𝓡 n) (F B) x (X 0 x) - ∑ l, C B l)
    rw [hDE]
    simp only [add_apply, hCE, Finset.sum_add_distrib]
    ring

set_option backward.isDefEq.respectTransparency false in
theorem covariantTensorDerivativeOnFields_update_smul (D : LeviCivitaData g) {k : ℕ}
    {T : CovariantTensorEvaluation n M k} (hT : IsSmoothCovariantTensor T)
    {U : Set M} (hU : IsOpen U)
    {X : Fin (k + 1) → (y : M) → TangentSpace (𝓡 n) y}
    {A : (y : M) → TangentSpace (𝓡 n) y} {f : M → ℝ}
    (hX : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% (X i)) U)
    (hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (T% A) U)
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U) (i : Fin (k + 1))
    {x : M} (hx : x ∈ U) :
    covariantTensorDerivativeOnFields D T (Function.update X i (f • A)) x =
      f x * covariantTensorDerivativeOnFields D T (Function.update X i A) x := by
  classical
  have hAdd (y : M) (v : Fin k → TangentSpace (𝓡 n) y) (j : Fin k)
      (a b : TangentSpace (𝓡 n) y) : T y (Function.update v j (a + b)) =
        T y (Function.update v j a) + T y (Function.update v j b) := by
    obtain ⟨P, hP⟩ := hT.1 y
    simp only [hP, P.map_update_add]
  have hSmul (y : M) (v : Fin k → TangentSpace (𝓡 n) y) (j : Fin k)
      (c : ℝ) (a : TangentSpace (𝓡 n) y) : T y (Function.update v j (c • a)) =
        c * T y (Function.update v j a) := by
    obtain ⟨P, hP⟩ := hT.1 y
    simp only [hP, P.map_update_smul, smul_eq_mul]
  cases i using Fin.cases with
  | zero =>
    simp only [covariantTensorDerivativeOnFields,
      Function.update_of_ne (Fin.succ_ne_zero _), Function.update_self,
      Pi.smul_apply', map_smul, hSmul, smul_eq_mul, ← Finset.mul_sum]
    ring
  | succ j =>
    let v := fun l : Fin k ↦ X l.succ x
    let F := fun (W : (y : M) → TangentSpace (𝓡 n) y) y ↦
      T y (Function.update (fun l : Fin k ↦ X l.succ y) j (W y))
    let C := fun (W : (y : M) → TangentSpace (𝓡 n) y) (l : Fin k) ↦
      T x (Function.update (Function.update v j (W x)) l
        (D.connection (Function.update X j.succ W l.succ) x (X 0 x)))
    have htup (W : (y : M) → TangentSpace (𝓡 n) y) (y : M) :
        (fun l : Fin k ↦ Function.update X j.succ W l.succ y) =
          Function.update (fun l : Fin k ↦ X l.succ y) j (W y) := by
      funext l
      by_cases hl : l = j <;> simp [Function.update, Fin.succ_inj, hl]
    have hFs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (F A) U := by
      let V := Function.update (fun l : Fin k ↦ X l.succ) j A
      have hV (l : Fin k) :
          ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
            ∞ (T% (V l)) U := by
        by_cases hl : l = j
        · subst l
          simpa only [V, Function.update_self] using hA
        · simpa only [V, Function.update_of_ne hl] using hX l.succ
      apply (hT.2 U hU V hV).congr
      intro y hy
      dsimp only [F]
      congr 1
      funext l
      by_cases hl : l = j <;> simp [V, hl]
    have hFA := (hFs x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)
    have hfD := (hf x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)
    have hFE : F (f • A) = f * F A := by
      funext y
      exact hSmul y _ j (f y) (A y)
    have hDE : mvfderiv (𝓡 n) (F (f • A)) x =
        f x • mvfderiv (𝓡 n) (F A) x + F A x • mvfderiv (𝓡 n) f x := by
      rw [hFE]
      exact mvfderiv_mul hfD hFA
    have hAD := (hA x hx).contMDiffAt (hU.mem_nhds hx) |>.mdifferentiableAt (by simp)
    let d := mvfderiv (𝓡 n) f x (X 0 x)
    have hCE (l : Fin k) : C (f • A) l =
        f x * C A l + if l = j then d * F A x else 0 := by
      by_cases hl : l = j
      · subst l
        simp only [C, Function.update_self, Function.update_idem,
          D.connection.isCovariantDerivativeOnUniv.leibniz hAD hfD,
          add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
          hAdd, hSmul, d, F, v]
        simp only [ite_true]
      · have hls : l.succ ≠ j.succ := fun h ↦ hl (Fin.succ_injective _ h)
        simp only [C, Function.update_of_ne hls, Function.update_comm (Ne.symm hl),
          Pi.smul_apply', hSmul, if_neg hl, add_zero]
    have hsum : ∑ l, C (f • A) l = f x * (∑ l, C A l) + d * F A x := by
      simp [hCE, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [covariantTensorDerivativeOnFields, htup,
      Function.update_of_ne (Fin.succ_ne_zero j).symm]
    change mvfderiv (𝓡 n) (F (f • A)) x (X 0 x) - ∑ l, C (f • A) l =
      f x * (mvfderiv (𝓡 n) (F A) x (X 0 x) - ∑ l, C A l)
    rw [hDE, hsum]
    simp only [add_apply, smul_apply, smul_eq_mul, d]
    ring

end PoincareConjecture.RicciFlowAnalysis
