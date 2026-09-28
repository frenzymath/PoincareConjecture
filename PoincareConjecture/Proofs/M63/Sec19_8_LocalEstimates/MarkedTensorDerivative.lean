import PoincareConjecture.Proofs.M63.Mathlib.MarkedTensorContraction
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurveTensorLeibniz











set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}


noncomputable def m63MarkedTensorTerm
    (F : RicciFlow n M (Icc a b)) (c : ℝ -> ℝ -> M)
    {k : Nat} (T : CovariantTensorEvaluation n M k)
    (A : MarkedTensorContraction k) (t : ℝ)
    (Z : (y : ℝ) -> TangentSpace (𝓡 n) (c y t)) (x : ℝ) : ℝ :=
  let K : Nat -> TangentSpace (𝓡 n) (c x t) := fun r =>
    match r with
    | 0 => spatialUnitTangent F c t x
    | i + 1 => m63CurvatureJet F c i t x
  (F.connection t).iteratedCovariantTensorDerivative T A.order (c x t)
    (fun i => if i = A.test then Z x else K (A.jet i))


noncomputable def m63MarkedTensorExpression
    (F : RicciFlow n M (Icc a b)) (c : ℝ -> ℝ -> M)
    {k : Nat} (T : CovariantTensorEvaluation n M k)
    (P : List (Int × MarkedTensorContraction k)) (t : ℝ)
    (Z : (y : ℝ) -> TangentSpace (𝓡 n) (c y t)) (x : ℝ) : ℝ :=
  (P.map (fun q => (q.1 : ℝ) * m63MarkedTensorTerm F c T q.2 t Z x)).sum





theorem m63HasDerivAt_markedTensorExpression [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ -> ℝ -> M)
    (hc : M62ShrinkingCurve F c)
    {k : Nat} (T : CovariantTensorEvaluation n M k)
    (hT : IsSmoothCovariantTensor T)
    (P : List (Int × MarkedTensorContraction k))
    (Z : (z : ℝ × ℝ) -> TangentSpace (𝓡 n) (c z.1 z.2))
    (hZ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Z z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let Zt := fun y => Z (y, t)
    let dZt := m62SpatialDerivative F c t Zt
    let f := fun y => m63MarkedTensorExpression F c T P t Zt y
    let Df :=
      m63MarkedTensorExpression F c T (markedTensorExpressionDerivative P) t Zt x +
      m63MarkedTensorExpression F c T P t dZt x
    HasDerivAt f (curveSpeed F c t x * Df) x ∧
      m62ArcDerivative F c t f x = Df := by
  classical
  let D := F.connection t
  let V : (i : Nat) -> (z : ℝ × ℝ) -> TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun i z => match i with
      | 0 => spatialUnitTangent F c z.2 z.1
      | j + 1 => m63CurvatureJet F c j z.2 z.1
  let Zt := fun y => Z (y, t)
  let dZt := m62SpatialDerivative F c t Zt
  have hV (i : Nat) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, V i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    cases i with
    | zero => exact unitTangent_joint_contMDiff F c hc
    | succ i => exact M63.curvatureJet_joint_contMDiff F c hc i
  have hVnext (i : Nat) (y : ℝ) :
      m62SpatialDerivative F c t (fun s => V i (s, t)) y = V (i + 1) (y, t) := by
    cases i <;> rfl
  have hiter (i : Nat) : IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative T i) := by
    induction i with
    | zero => exact hT
    | succ i ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative D ih
  have heval (A : MarkedTensorContraction k)
      (W : (y : ℝ) -> TangentSpace (𝓡 n) (c y t)) (y : ℝ) :
      m63MarkedTensorTerm F c T A t W y =
        D.iteratedCovariantTensorDerivative T A.order (c y t)
          (fun i => if i = A.test then W y else V (A.jet i) (y, t)) := rfl
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun y : ℝ => (y, t)) x :=
    (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c y t) x :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp x hs
  have hv : curveSpeed F c t x ≠ 0 := (speed_pos F c hc (Ioo_subset_Icc_self ht) x).ne'
  have hterm (A : MarkedTensorContraction k) :
      HasDerivAt (fun y => m63MarkedTensorTerm F c T A t Zt y)
        (curveSpeed F c t x *
          ((A.derivativeBranches.map (fun B => m63MarkedTensorTerm F c T B t Zt x)).sum +
            m63MarkedTensorTerm F c T A t dZt x)) x := by
    let U := D.iteratedCovariantTensorDerivative T A.order
    let Y : Fin (k + A.order) -> (z : ℝ × ℝ) -> TangentSpace (𝓡 n) (c z.1 z.2) :=
      fun i z => if i = A.test then Z z else V (A.jet i) z
    have hY (i : Fin (k + A.order)) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
        (fun z => (⟨c z.1 z.2, Y i z⟩ : TangentBundle (𝓡 n) M))
        (univ ×ˢ Ioo a b) := by
      by_cases hi : i = A.test
      · simpa only [Y, hi, if_true] using hZ
      · simpa only [Y, hi, if_false] using hV (A.jet i)
    have hYs (i : Fin (k + A.order)) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
        (fun y => (⟨c y t, Y i (y, t)⟩ : TangentBundle (𝓡 n) M)) x :=
      (((hY i).contMDiffAt (hopen.mem_nhds hmem)).comp x hs).mdifferentiableAt (by simp)
    have hraw := m63HasDerivAt_tensor_pullback D U (hiter A.order) hcurve
      (fun i y => Y i (y, t)) hYs
    have harc := m63ArcDerivative_tensor_pullback F c hc U (hiter A.order) Y hY ht x
    let f := fun y => m63MarkedTensorTerm F c T A t Zt y
    let slot := fun i => U (c x t) (Function.update (fun j => Y j (x, t)) i
      (m62SpatialDerivative F c t (fun y => Y i (y, t)) x))
    have hlead : D.covariantTensorDerivative U (c x t)
        (Fin.cons (spatialUnitTangent F c t x) (fun i => Y i (x, t))) =
        m63MarkedTensorTerm F c T A.tensorStep t Zt x := by
      have htuple :
          Fin.cons (spatialUnitTangent F c t x) (fun i => Y i (x, t)) =
            (fun i : Fin (k + A.order + 1) =>
              if i = A.test.succ then Zt x else
                V ((Fin.cons 0 A.jet : Fin (k + A.order + 1) -> Nat) i) (x, t)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [V, (Fin.succ_ne_zero A.test).symm]
        · simp [Y, Zt]
      simpa only [heval, MarkedTensorContraction.tensorStep,
        LeviCivitaData.iteratedCovariantTensorDerivative, U] using!
        congrArg (D.covariantTensorDerivative U (c x t)) htuple
    have hmark : slot A.test = m63MarkedTensorTerm F c T A t dZt x := by
      rw [heval]
      change U (c x t) (Function.update (fun j => Y j (x, t)) A.test
        (m62SpatialDerivative F c t (fun y => Y A.test (y, t)) x)) = _
      apply congrArg (U (c x t))
      funext i
      by_cases hi : i = A.test
      · subst i
        simp only [Function.update_self, Y, if_true]
        rfl
      · simp only [Function.update_of_ne hi, Y, hi, if_false]
    have hslot (i : Fin (k + A.order)) (hi : i ∈ Finset.univ.erase A.test) :
        slot i = m63MarkedTensorTerm F c T (A.slotStep i) t Zt x := by
      have himark : i ≠ A.test := (Finset.mem_erase.mp hi).1
      have hYi : (fun y => Y i (y, t)) = (fun y => V (A.jet i) (y, t)) := by
        funext y
        simp only [Y, himark, if_false]
      rw [heval]
      simp only [MarkedTensorContraction.slotStep]
      change U (c x t) (Function.update (fun j => Y j (x, t)) i
        (m62SpatialDerivative F c t (fun y => Y i (y, t)) x)) =
        U (c x t) (fun j => if j = A.test then Zt x else
          V (Function.update A.jet i (A.jet i + 1) j) (x, t))
      rw [hYi, hVnext]
      apply congrArg (U (c x t))
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, himark, if_false]
      · simp only [Function.update_of_ne hji]
        by_cases hjmark : j = A.test <;> simp [Y, Zt, hjmark]
    have hsum : (∑ i, slot i) =
        (Finset.sum (Finset.univ.erase A.test)
          (fun i => m63MarkedTensorTerm F c T (A.slotStep i) t Zt x)) +
            m63MarkedTensorTerm F c T A t dZt x := by
      rw [← Finset.sum_erase_add Finset.univ slot (Finset.mem_univ A.test), hmark]
      congr 1
      exact Finset.sum_congr rfl hslot
    have hbranches :
        (A.derivativeBranches.map (fun B => m63MarkedTensorTerm F c T B t Zt x)).sum =
          m63MarkedTensorTerm F c T A.tensorStep t Zt x +
            Finset.sum (Finset.univ.erase A.test)
              (fun i => m63MarkedTensorTerm F c T (A.slotStep i) t Zt x) := by
      simp only [MarkedTensorContraction.derivativeBranches, List.map_cons, List.sum_cons,
        List.map_map, Function.comp_def, Finset.sum_map_toList]
    have harc' : m62ArcDerivative F c t f x =
        (A.derivativeBranches.map (fun B => m63MarkedTensorTerm F c T B t Zt x)).sum +
          m63MarkedTensorTerm F c T A t dZt x := by
      change m62ArcDerivative F c t f x =
        D.covariantTensorDerivative U (c x t)
          (Fin.cons (spatialUnitTangent F c t x) (fun i => Y i (x, t))) +
          ∑ i, slot i at harc
      rw [hlead, hsum] at harc
      rw [hbranches]
      exact harc.trans (add_assoc _ _ _).symm
    have hdiff : DifferentiableAt ℝ f x := hraw.differentiableAt
    apply hdiff.hasDerivAt.congr_deriv
    calc
      deriv f x = curveSpeed F c t x * m62ArcDerivative F c t f x := by
        rw [m62ArcDerivative, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
      _ = _ := by rw [harc']
  have hexpression (Q : List (Int × MarkedTensorContraction k)) :
      HasDerivAt (fun y => m63MarkedTensorExpression F c T Q t Zt y)
        (curveSpeed F c t x *
          (m63MarkedTensorExpression F c T (markedTensorExpressionDerivative Q) t Zt x +
            m63MarkedTensorExpression F c T Q t dZt x)) x := by
    have hrepeat (z : Int) (L : List (MarkedTensorContraction k)) :
        m63MarkedTensorExpression F c T (L.map (fun A => (z, A))) t Zt x =
          (z : ℝ) * (L.map (fun A => m63MarkedTensorTerm F c T A t Zt x)).sum := by
      induction L with
      | nil => simp [m63MarkedTensorExpression]
      | cons A L ih =>
        change (z : ℝ) * m63MarkedTensorTerm F c T A t Zt x +
          m63MarkedTensorExpression F c T (L.map (fun B => (z, B))) t Zt x = _
        rw [ih]
        simp only [List.map_cons, List.sum_cons, mul_add]
    have happend (L R : List (Int × MarkedTensorContraction k)) :
        m63MarkedTensorExpression F c T (L ++ R) t Zt x =
          m63MarkedTensorExpression F c T L t Zt x +
            m63MarkedTensorExpression F c T R t Zt x := by
      simp only [m63MarkedTensorExpression, List.map_append, List.sum_append]
    induction Q with
    | nil => simpa [m63MarkedTensorExpression, markedTensorExpressionDerivative] using
        hasDerivAt_const x (0 : ℝ)
    | cons q Q ih =>
      have hd := ((hterm q.2).const_mul (q.1 : ℝ)).add ih
      apply hd.congr_deriv
      change _ = curveSpeed F c t x *
        (m63MarkedTensorExpression F c T
          (q.2.derivativeBranches.map (fun A => (q.1, A)) ++
            markedTensorExpressionDerivative Q) t Zt x +
          ((q.1 : ℝ) * m63MarkedTensorTerm F c T q.2 t dZt x +
            m63MarkedTensorExpression F c T Q t dZt x))
      rw [happend, hrepeat]
      ring
  refine ⟨hexpression P, ?_⟩
  rw [m62ArcDerivative, (hexpression P).deriv, ← mul_assoc, inv_mul_cancel₀ hv, one_mul]

end PoincareConjecture
