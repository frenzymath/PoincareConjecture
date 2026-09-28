import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetErrorExpressions
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.MarkedTensorDerivative
import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetErrorIdentities

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

set_option maxHeartbeats 800000 in

theorem m63CurvatureJet_diffusionError_expansion_pair [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (m j : Nat)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let D := F.connection t
    let J := fun i y => m63CurvatureJet F c i t y
    let K : Nat → (y : ℝ) → TangentSpace (𝓡 n) (c y t) := fun i =>
      match i with
      | 0 => spatialUnitTangent F c t
      | r + 1 => J r
    let A := fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y
    let Q := rampHorizontalCovariantDerivative D (fun s => c x s)
      (fun s => m63CurvatureJet F c m s x) t - J (m + 2) x
    let E :=
      m63MarkedTensorExpression F c D.riemannEvaluation
        (m63RiemannJetErrorExpression m) t (J j) x +
      m63MarkedTensorExpression F c D.ricciEvaluation
        (m63RicciJetErrorExpression m) t (J j) x
    (F.metric t).inner (c x t) Q (J j x) =
      ∑ r ∈ Finset.range (m + 2),
        ((m + 2).choose (r + 1) : ℝ) *
          ((m62ArcDerivative F c t)^[r]) A x *
          (F.metric t).inner (c x t) (K (m + 1 - r) x) (J j x) + E := by
  classical
  let D := F.connection t
  let J : Nat → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) :=
    fun i z => m63CurvatureJet F c i z.2 z.1
  let K : Nat → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := fun i z =>
    match i with
    | 0 => spatialUnitTangent F c z.2 z.1
    | r + 1 => J r z
  let A := fun y => m62TangentRicci F c t y + m62CurvatureSquared F c t y
  let Ar := fun r => ((m62ArcDerivative F c t)^[r]) A
  let v := curveSpeed F c t
  let T : Nat → (y : ℝ) → TangentSpace (𝓡 n) (c y t) := fun i y =>
    rampHorizontalCovariantDerivative D (fun s => c y s)
      (fun s => J i (y, s)) t
  let Q : Nat → (y : ℝ) → TangentSpace (𝓡 n) (c y t) :=
    fun i y => T i y - J (i + 2) (y, t)
  let P := fun i j y => (F.metric t).inner (c y t) (K i (y, t)) (J j (y, t))
  let E := fun i j y =>
    m63MarkedTensorExpression F c D.riemannEvaluation
      (m63RiemannJetErrorExpression i) t (fun z => J j (z, t)) y +
    m63MarkedTensorExpression F c D.ricciEvaluation
      (m63RicciJetErrorExpression i) t (fun z => J j (z, t)) y
  let Ed := fun i j y =>
    m63MarkedTensorExpression F c D.riemannEvaluation
      (markedTensorExpressionDerivative (m63RiemannJetErrorExpression i))
      t (fun z => J j (z, t)) y +
    m63MarkedTensorExpression F c D.ricciEvaluation
      (markedTensorExpressionDerivative (m63RicciJetErrorExpression i))
      t (fun z => J j (z, t)) y
  let row := fun i j y => ∑ r ∈ Finset.range (i + 2),
    ((i + 2).choose (r + 1) : ℝ) * Ar r y * P (i + 1 - r) j y
  have hv (y : ℝ) : v y ≠ 0 :=
    (speed_pos F c hc (Ioo_subset_Icc_self ht) y).ne'
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) :=
    isOpen_univ.prod isOpen_Ioo
  have hJ (i : Nat) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, J i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := M63.curvatureJet_joint_contMDiff F c hc i
  have hK (i : Nat) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, K i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    cases i with
    | zero => exact unitTangent_joint_contMDiff F c hc
    | succ i => exact hJ i
  have hKnext (i : Nat) (y : ℝ) :
      m62SpatialDerivative F c t (fun z => K i (z, t)) y = K (i + 1) (y, t) := by
    cases i <;> rfl
  have hs (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun z : ℝ => (z, t)) y :=
    (differentiableAt_id.prodMk (differentiableAt_const t)).mdifferentiableAt
  have hcurve (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) (fun z => c z t) y :=
    ((hc.joint_smooth.contMDiffAt (hopen.mem_nhds ⟨mem_univ y, ht⟩)).mdifferentiableAt
      (by simp)).comp y (hs y)
  have hJs (i : Nat) (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun z => (⟨c z t, J i (z, t)⟩ : TangentBundle (𝓡 n) M)) y :=
    (((hJ i).contMDiffAt (hopen.mem_nhds ⟨mem_univ y, ht⟩)).mdifferentiableAt
      (by simp)).comp y (hs y)
  have hKs (i : Nat) (y : ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
      (fun z => (⟨c z t, K i (z, t)⟩ : TangentBundle (𝓡 n) M)) y :=
    (((hK i).contMDiffAt (hopen.mem_nhds ⟨mem_univ y, ht⟩)).mdifferentiableAt
      (by simp)).comp y (hs y)
  have hpair (Y Z : (y : ℝ) → TangentSpace (𝓡 n) (c y t)) (y : ℝ)
      (hY : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
        (fun z => (⟨c z t, Y z⟩ : TangentBundle (𝓡 n) M)) y)
      (hZ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
        (fun z => (⟨c z t, Z z⟩ : TangentBundle (𝓡 n) M)) y) :
      HasDerivAt (fun z => (F.metric t).inner (c z t) (Y z) (Z z))
        (v y * ((F.metric t).inner (c y t) (m62SpatialDerivative F c t Y y) (Z y) +
          (F.metric t).inner (c y t) (Y y) (m62SpatialDerivative F c t Z y))) y := by
    apply (hasDerivAt_metric_pairing D (hcurve y) hY hZ).congr_deriv
    simp only [m62SpatialDerivative, map_smul, smul_apply, smul_eq_mul]
    change _ + _ = v y * ((v y)⁻¹ * _ + (v y)⁻¹ * _)
    dsimp only [D]
    field_simp [hv y]
  have hP (i j : Nat) (y : ℝ) : HasDerivAt (P i j)
      (v y * (P (i + 1) j y + P i (j + 1) y)) y := by
    have h := hpair (fun z => K i (z, t)) (fun z => J j (z, t)) y (hKs i y) (hJs j y)
    rw [hKnext] at h
    exact h
  have hQ (i j : Nat) (y : ℝ) :
      HasDerivAt (fun z => (F.metric t).inner (c z t) (Q i z) (J j (z, t)))
        (v y * ((F.metric t).inner (c y t) (m62SpatialDerivative F c t (Q i) y)
          (J j (y, t)) + (F.metric t).inner (c y t) (Q i y) (J (j + 1) (y, t)))) y := by
    have hTjoint := m63FixedPullback_time_joint_contMDiff D c (J i)
      hopen hc.joint_smooth (hJ i)
    have hTs : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
        (fun z => (⟨c z t, T i z⟩ : TangentBundle (𝓡 n) M)) y :=
      ((hTjoint.contMDiffAt (hopen.mem_nhds ⟨mem_univ y, ht⟩)).mdifferentiableAt
        (by simp)).comp y (hs y)
    have hQs : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
        (fun z => (⟨c z t, Q i z⟩ : TangentBundle (𝓡 n) M)) y := by
      have hJcoord := hJs (i + 2) y
      rw [mdifferentiableAt_totalSpace] at hTs hJcoord ⊢
      refine ⟨hTs.1, ?_⟩
      let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (c y t)
      have hnear : ∀ᶠ z in 𝓝 y, c z t ∈ e.baseSet :=
        hTs.1.continuousAt (e.open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' (c y t)))
      apply (hTs.2.sub hJcoord.2).congr_of_eventuallyEq
      filter_upwards [hnear] with z hz
      change (e ⟨c z t, T i z - J (i + 2) (z, t)⟩).2 =
        (e ⟨c z t, T i z⟩).2 - (e ⟨c z t, J (i + 2) (z, t)⟩).2
      simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hz] using
        (e.continuousLinearMapAt ℝ (c z t)).map_sub (T i z) (J (i + 2) (z, t))
    exact hpair (Q i) (fun z => J j (z, t)) y hQs (hJs j y)
  have hArnext (r : Nat) : Ar (r + 1) = fun y => (v y)⁻¹ * deriv (Ar r) y := by
    funext y
    simp only [Ar, Function.iterate_succ_apply', m62ArcDerivative, v]
  have hAr (r : Nat) : ContDiff ℝ ∞ (Ar r) := by
    have hA : ContDiff ℝ ∞ A :=
      (normalization_coefficient_contDiffOn F c hc).comp_contDiff
        (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
    have hvDiff : ContDiff ℝ ∞ v :=
      (speed_joint_contDiffOn F c hc).comp_contDiff
        (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
    induction r with
    | zero => exact hA
    | succ r ih =>
      rw [hArnext]
      exact (hvDiff.inv hv).mul (contDiff_infty_iff_deriv.mp ih).2
  have hArD (r : Nat) (y : ℝ) : HasDerivAt (Ar r) (v y * Ar (r + 1) y) y := by
    apply (((hAr r).differentiable (by simp)) y).hasDerivAt.congr_deriv
    rw [hArnext]
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ (hv y), one_mul]
  have hED (i j : Nat) (y : ℝ) :
      HasDerivAt (E i j) (v y * (Ed i j y + E i (j + 1) y)) y := by
    have hR := (m63HasDerivAt_markedTensorExpression F c hc D.riemannEvaluation
      (M04.isSmoothCovariantTensor_riemannEvaluation D)
      (m63RiemannJetErrorExpression i) (J j) (hJ j) ht y).1
    have hRic := (m63HasDerivAt_markedTensorExpression F c hc D.ricciEvaluation
      (M04.isSmoothCovariantTensor_ricciEvaluation D)
      (m63RicciJetErrorExpression i) (J j) (hJ j) ht y).1
    have hJnext : m62SpatialDerivative F c t (fun z => J j (z, t)) =
        (fun z => J (j + 1) (z, t)) := rfl
    rw [hJnext] at hR hRic
    apply (hR.add hRic).congr_deriv
    change v y * (_ + _) + v y * (_ + _) = v y * ((_ + _) + (_ + _))
    ring
  have hRm (r j : Nat) (y : ℝ) :
      m63MarkedTensorTerm F c D.riemannEvaluation
        ⟨0, 2, ![1, 0, 0, r]⟩ t (fun z => J j (z, t)) y =
      D.curvatureTensor (c y t) (J 0 (y, t)) (K 0 (y, t))
        (J j (y, t)) (K r (y, t)) := by
    change D.riemannEvaluation (c y t)
      (fun i : Fin 4 => if i = 2 then J j (y, t) else K (![1, 0, 0, r] i) (y, t)) = _
    simp [LeviCivitaData.riemannEvaluation, K]
  have hRicTail (p q j : Nat) (y : ℝ) :
      m63MarkedTensorTerm F c D.ricciEvaluation
        ⟨1, 2, ![p, q, 0]⟩ t (fun z => J j (z, t)) y =
      D.covariantTensorDerivative D.ricciEvaluation (c y t)
        ![K p (y, t), K q (y, t), J j (y, t)] := by
    change D.covariantTensorDerivative D.ricciEvaluation (c y t)
      (fun i : Fin 3 => if i = 2 then J j (y, t) else K (![p, q, 0] i) (y, t)) = _
    congr 1
    funext i
    fin_cases i <;> simp
  have hRicHead (p q j : Nat) (y : ℝ) :
      m63MarkedTensorTerm F c D.ricciEvaluation
        ⟨1, 0, ![0, p, q]⟩ t (fun z => J j (z, t)) y =
      D.covariantTensorDerivative D.ricciEvaluation (c y t)
        ![J j (y, t), K p (y, t), K q (y, t)] := by
    change D.covariantTensorDerivative D.ricciEvaluation (c y t)
      (fun i : Fin 3 => if i = 0 then J j (y, t) else K (![0, p, q] i) (y, t)) = _
    congr 1
    funext i
    fin_cases i <;> simp
  have hEzero (j : Nat) (y : ℝ) : E 0 j y =
      D.curvatureTensor (c y t) (J 0 (y, t)) (K 0 (y, t)) (J j (y, t)) (K 0 (y, t)) -
      2 * D.covariantTensorDerivative D.ricciEvaluation (c y t)
        ![K 0 (y, t), K 0 (y, t), J j (y, t)] +
      D.covariantTensorDerivative D.ricciEvaluation (c y t)
        ![J j (y, t), K 0 (y, t), K 0 (y, t)] := by
    simp only [E, m63RiemannJetErrorExpression, m63RicciJetErrorExpression,
      m63MarkedTensorExpression, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Int.cast_one, Int.cast_neg, Int.cast_ofNat, one_mul, add_zero]
    rw [hRm, hRicTail, hRicHead]
    ring
  have hEsucc (i j : Nat) (y : ℝ) : E (i + 1) j y = Ed i j y +
      D.curvatureTensor (c y t) (J 0 (y, t)) (K 0 (y, t)) (J j (y, t)) (J i (y, t)) -
      D.covariantTensorDerivative D.ricciEvaluation (c y t)
        ![K 0 (y, t), J i (y, t), J j (y, t)] -
      D.covariantTensorDerivative D.ricciEvaluation (c y t)
        ![J i (y, t), K 0 (y, t), J j (y, t)] +
      D.covariantTensorDerivative D.ricciEvaluation (c y t)
        ![J j (y, t), K 0 (y, t), J i (y, t)] := by
    simp only [E, m63RiemannJetErrorExpression, m63RicciJetErrorExpression,
      m63MarkedTensorExpression, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Int.cast_one, Int.cast_neg, one_mul, neg_one_mul, add_zero]
    rw [hRm, hRicTail, hRicTail, hRicHead]
    dsimp only [Ed, m63MarkedTensorExpression, K]
    ring

  have hrow (i : Nat) (U V : Nat → ℝ) :
      (∑ r ∈ Finset.range (i + 2), ((i + 2).choose (r + 1) : ℝ) *
        (U (r + 1) * V (i + 1 - r) + U r * V (i + 2 - r))) +
          U 0 * V (i + 2) =
      ∑ r ∈ Finset.range (i + 3), ((i + 3).choose (r + 1) : ℝ) * U r * V (i + 2 - r) := by
    have hshift :
        (∑ r ∈ Finset.range (i + 2), ((i + 2).choose (r + 1) : ℝ) *
          U (r + 1) * V (i + 1 - r)) + U 0 * V (i + 2) =
        ∑ r ∈ Finset.range (i + 3), ((i + 2).choose r : ℝ) * U r * V (i + 2 - r) := by
      conv_rhs => rw [show i + 3 = (i + 2) + 1 by omega, Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [show i + 2 - (r + 1) = i + 1 - r by omega]
    have hext :
        (∑ r ∈ Finset.range (i + 2), ((i + 2).choose (r + 1) : ℝ) * U r * V (i + 2 - r)) =
        ∑ r ∈ Finset.range (i + 3), ((i + 2).choose (r + 1) : ℝ) * U r * V (i + 2 - r) := by
      conv_rhs => rw [show i + 3 = (i + 2) + 1 by omega, Finset.sum_range_succ]
      simp only [Nat.choose_eq_zero_of_lt (by omega : i + 2 < i + 2 + 1),
        Nat.cast_zero, zero_mul, add_zero]
    calc
      _ = ((∑ r ∈ Finset.range (i + 2), ((i + 2).choose (r + 1) : ℝ) *
          U (r + 1) * V (i + 1 - r)) + U 0 * V (i + 2)) +
          ∑ r ∈ Finset.range (i + 2), ((i + 2).choose (r + 1) : ℝ) * U r * V (i + 2 - r) := by
        simp only [mul_add, ← mul_assoc, Finset.sum_add_distrib]
        ring
      _ = _ := by
        rw [hshift, hext, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r _
        rw [show i + 3 = (i + 2) + 1 by omega,
          Nat.choose_succ_succ' (i + 2) r, Nat.cast_add]
        ring
  have hKslice (i : Nat) (y : ℝ) :
      ((match i with
        | 0 => spatialUnitTangent F c t
        | r + 1 => fun z => m63CurvatureJet F c r t z) y) = K i (y, t) := by
    cases i <;> rfl
  dsimp only
  simp only [hKslice]
  change (F.metric t).inner (c x t) (Q m x) (J j (x, t)) = row m j x + E m j x
  induction m generalizing j x with
  | zero =>
    have hbase := m63CurvatureVector_time_pair F c hc ht x (J j (x, t))
    change (F.metric t).inner (c x t) (T 0 x) (J j (x, t)) =
      (F.metric t).inner (c x t) (J 2 (x, t)) (J j (x, t)) +
      2 * A x * P 1 j x + Ar 1 x * P 0 j x +
      D.curvatureTensor (c x t) (J 0 (x, t)) (K 0 (x, t)) (J j (x, t)) (K 0 (x, t)) -
      2 * D.covariantTensorDerivative D.ricciEvaluation (c x t)
        ![K 0 (x, t), K 0 (x, t), J j (x, t)] +
      D.covariantTensorDerivative D.ricciEvaluation (c x t)
        ![J j (x, t), K 0 (x, t), K 0 (x, t)] at hbase
    rw [hEzero]
    simp only [Q, Nat.zero_add, map_sub, sub_apply]
    rw [hbase]
    norm_num [row, Finset.sum_range_succ, Ar, Function.iterate_zero_apply]
    ring
  | succ m ih =>
    let L : ℝ := (F.metric t).inner (c x t) (m62SpatialDerivative F c t (Q m) x) (J j (x, t))
    let R : ℝ := ∑ r ∈ Finset.range (m + 2), ((m + 2).choose (r + 1) : ℝ) *
      (Ar (r + 1) x * P (m + 1 - r) j x + Ar r x * P (m + 2 - r) j x)
    have hrowD : HasDerivAt (row m j) (v x * (R + row m (j + 1) x)) x := by
      have hsum := HasDerivAt.fun_sum (u := Finset.range (m + 2)) (fun r _ =>
        ((hArD r x).mul (hP (m + 1 - r) j x)).const_mul
          ((m + 2).choose (r + 1) : ℝ))
      have hrowfun : row m j = fun y => ∑ r ∈ Finset.range (m + 2),
          ((m + 2).choose (r + 1) : ℝ) * (Ar r y * P (m + 1 - r) j y) := by
        funext y
        dsimp only [row]
        apply Finset.sum_congr rfl
        intro r _
        exact mul_assoc _ _ _
      simp only [Pi.mul_apply] at hsum
      rw [← hrowfun] at hsum
      apply hsum.congr_deriv
      change (∑ r ∈ Finset.range (m + 2), ((m + 2).choose (r + 1) : ℝ) *
        ((v x * Ar (r + 1) x) * P (m + 1 - r) j x +
          Ar r x * (v x * (P (m + 1 - r + 1) j x + P (m + 1 - r) (j + 1) x)))) = _
      dsimp only [R, row]
      conv_rhs => rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      have hrange := Finset.mem_range.mp hr
      rw [show m + 1 - r + 1 = m + 2 - r by omega]
      ring
    have hright : HasDerivAt (fun y => row m j y + E m j y)
        (v x * (R + row m (j + 1) x + Ed m j x + E m (j + 1) x)) x := by
      apply (hrowD.add (hED m j x)).congr_deriv
      ring
    have hfun : (fun y => (F.metric t).inner (c y t) (Q m y) (J j (y, t))) =
        (fun y => row m j y + E m j y) := funext (ih j)
    have hleft := hQ m j x
    rw [hfun] at hleft
    have hder := hleft.unique hright
    change v x * (L + (F.metric t).inner (c x t) (Q m x) (J (j + 1) (x, t))) =
      v x * (R + row m (j + 1) x + Ed m j x + E m (j + 1) x) at hder
    have hcancel := mul_left_cancel₀ (hv x) hder
    rw [ih (j + 1) x] at hcancel
    have hL : L = R + Ed m j x := by linarith only [hcancel]
    have hnext := m63CurvatureJet_diffusionError_succ_pair F c hc m ht x (J j (x, t))
    change (F.metric t).inner (c x t) (Q (m + 1) x) (J j (x, t)) =
      L + A x * P (m + 2) j x +
      D.curvatureTensor (c x t) (J 0 (x, t)) (K 0 (x, t)) (J j (x, t)) (J m (x, t)) -
      D.covariantTensorDerivative D.ricciEvaluation (c x t)
        ![K 0 (x, t), J m (x, t), J j (x, t)] -
      D.covariantTensorDerivative D.ricciEvaluation (c x t)
        ![J m (x, t), K 0 (x, t), J j (x, t)] +
      D.covariantTensorDerivative D.ricciEvaluation (c x t)
        ![J j (x, t), K 0 (x, t), J m (x, t)] at hnext
    have hbinomial := hrow m (fun r => Ar r x) (fun i => P i j x)
    change R + A x * P (m + 2) j x = row (m + 1) j x at hbinomial
    rw [hnext, hL, hEsucc]
    linarith only [hbinomial]

end PoincareConjecture
