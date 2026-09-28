import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.TangentRicciDerivatives
import PoincareConjecture.Proofs.M62.Cor0_3_PointwiseBounds

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

theorem m63TangentRicci_third_arc_bound [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K : ℝ} (_hK : 0 ≤ K)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hSecond : ∀ v : Fin 4 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            (F.connection t).ricciEvaluation) (c x t) v| ≤ K)
    (hThird : ∀ v : Fin 5 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            ((F.connection t).covariantTensorDerivative
              (F.connection t).ricciEvaluation)) (c x t) v| ≤ K) :
    let g := F.metric t
    let k := g.tangentNorm (c x t) (m63CurvatureJet F c 0 t x)
    let u := g.tangentNorm (c x t) (m63CurvatureJet F c 1 t x)
    let w := g.tangentNorm (c x t) (m63CurvatureJet F c 2 t x)
    let r2 := m62ArcSecondDerivative F c t (m62TangentRicci F c t)
    DifferentiableAt ℝ r2 x ∧
      |m62ArcDerivative F c t r2 x| ≤
        K * (1 + 9 * k + 7 * u + 12 * k ^ 2 + 6 * k * u + 2 * w) := by
  classical
  let D := F.connection t
  let g := F.metric t
  let p := c x t
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let V : ℕ → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2)
    | 0, z => spatialUnitTangent F c z.2 z.1
    | i + 1, z => m63CurvatureJet F c i z.2 z.1
  let N : ℕ → ℝ := fun i => g.tangentNorm p (V i (x, t))
  let k := N 1
  let u := N 2
  let w := N 3
  have hV (i : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, V i z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    cases i with
    | zero => exact unitTangent_joint_contMDiff F c hc
    | succ i => exact M63.curvatureJet_joint_contMDiff F c hc i
  have hrec (i : ℕ) : m62SpatialDerivative F c t (fun y => V i (y, t)) x =
      V (i + 1) (x, t) := by
    cases i <;> rfl
  have hN0 : N 0 = 1 := unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x
  have hN1 : N 1 = k := rfl
  have hN2 : N 2 = u := rfl
  have hN3 : N 3 = w := rfl
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hmem : (x, t) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, ht⟩
  have hs : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun y : ℝ => (y, t)) x :=
    (contDiffAt_id.prodMk contDiffAt_const).contMDiffAt
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun y => c y t) x :=
    (hc.joint_smooth.contMDiffAt (hopen.mem_nhds hmem)).comp x hs
  have htensor {d : ℕ} (Q : CovariantTensorEvaluation n M d)
      (hQ : IsSmoothCovariantTensor Q)
      (hQbound : ∀ v : Fin d → TangentSpace (𝓡 n) p,
        (∀ i, g.tangentNorm p (v i) ≤ 1) → |Q p v| ≤ K)
      (hDQbound : ∀ v : Fin (d + 1) → TangentSpace (𝓡 n) p,
        (∀ i, g.tangentNorm p (v i) ≤ 1) → |D.covariantTensorDerivative Q p v| ≤ K)
      (alpha : Fin d → ℕ) :
      DifferentiableAt ℝ (fun y => Q (c y t) ((fun l => V l (y, t)) ∘ alpha)) x ∧
        |m62ArcDerivative F c t (fun y => Q (c y t)
          ((fun l => V l (y, t)) ∘ alpha)) x| ≤
          K * ((∏ i, N (alpha i)) +
            ∑ i, ∏ l, N (Function.update alpha i (alpha i + 1) l)) := by
    let Y := fun i z => V (alpha i) z
    have hYs (i : Fin d) : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n).tangent
        (fun y => (⟨c y t, Y i (y, t)⟩ : TangentBundle (𝓡 n) M)) x :=
      (((hV (alpha i)).contMDiffAt (hopen.mem_nhds hmem)).comp x hs).mdifferentiableAt
        (by simp)
    refine ⟨(m63HasDerivAt_tensor_pullback D Q hQ hcurve
      (fun i y => Y i (y, t)) hYs).differentiableAt, ?_⟩
    have hslot (i : Fin d) :
        Function.update (fun l => Y l (x, t)) i
            (m62SpatialDerivative F c t (fun y => Y i (y, t)) x) =
          fun l => V (Function.update alpha i (alpha i + 1) l) (x, t) := by
      funext l
      by_cases hli : l = i
      · subst l
        simp only [Function.update_self]
        exact hrec (alpha i)
      · simp only [Function.update_of_ne hli]
        rfl
    have hlead := tensor_abs_le_of_unit_bound g (D.covariantTensorDerivative Q)
      (M04.isSmoothCovariantTensor_covariantTensorDerivative D hQ) p hDQbound
      (Fin.cons (V 0 (x, t)) (fun i => Y i (x, t)))
    have hlead' : |D.covariantTensorDerivative Q p
        (Fin.cons (V 0 (x, t)) (fun i => Y i (x, t)))| ≤
        K * ∏ i, N (alpha i) := by
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] at hlead
      change |D.covariantTensorDerivative Q p
          (Fin.cons (V 0 (x, t)) (fun i => Y i (x, t)))| ≤
        K * (N 0 * ∏ i, N (alpha i)) at hlead
      simpa only [hN0, one_mul] using hlead
    have hslots (i : Fin d) : |Q p
        (fun l => V (Function.update alpha i (alpha i + 1) l) (x, t))| ≤
        K * ∏ l, N (Function.update alpha i (alpha i + 1) l) :=
      tensor_abs_le_of_unit_bound g Q hQ p hQbound _
    have harc := m63ArcDerivative_tensor_pullback F c hc Q hQ Y
      (fun i => hV (alpha i)) ht x
    simp_rw [hslot] at harc
    change m62ArcDerivative F c t (fun y => Q (c y t)
        ((fun l => V l (y, t)) ∘ alpha)) x =
      D.covariantTensorDerivative Q p
        (Fin.cons (V 0 (x, t)) (fun i => Y i (x, t))) +
        ∑ i, Q p (fun l => V (Function.update alpha i (alpha i + 1) l) (x, t)) at harc
    rw [harc]
    calc
      _ ≤ |D.covariantTensorDerivative Q p
          (Fin.cons (V 0 (x, t)) (fun i => Y i (x, t)))| +
          |∑ i, Q p (fun l => V (Function.update alpha i (alpha i + 1) l) (x, t))| :=
        abs_add_le _ _
      _ ≤ K * (∏ i, N (alpha i)) +
          ∑ i, K * ∏ l, N (Function.update alpha i (alpha i + 1) l) :=
        add_le_add hlead' ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => hslots i))
      _ = _ := by rw [← Finset.mul_sum, ← mul_add]
  have hRic := M04.isSmoothCovariantTensor_ricciEvaluation D
  have hT := M04.isSmoothCovariantTensor_covariantTensorDerivative D hRic
  have hU := M04.isSmoothCovariantTensor_covariantTensorDerivative D hT
  have hRicBound (v : Fin 2 → TangentSpace (𝓡 n) p)
      (hv : ∀ i, g.tangentNorm p (v i) ≤ 1) : |D.ricciEvaluation p v| ≤ K :=
    hBounds.ricci t (Ioo_subset_Icc_self ht) p (v 0) (v 1) (hv 0) (hv 1)
  have hTBound := hBounds.ricci_derivative t (Ioo_subset_Icc_self ht) p
  let f0 : ℝ → ℝ := fun y => U (c y t) ((fun l => V l (y, t)) ∘ ![0, 0, 0, 0])
  let f1 : ℝ → ℝ := fun y => T (c y t) ((fun l => V l (y, t)) ∘ ![1, 0, 0])
  let f2 : ℝ → ℝ := fun y => T (c y t) ((fun l => V l (y, t)) ∘ ![0, 1, 0])
  let f3 : ℝ → ℝ := fun y => D.ricciEvaluation (c y t)
    ((fun l => V l (y, t)) ∘ ![2, 0])
  let f4 : ℝ → ℝ := fun y => D.ricciEvaluation (c y t)
    ((fun l => V l (y, t)) ∘ ![1, 1])
  obtain ⟨hd0, hb0⟩ := htensor U hU hSecond hThird ![0, 0, 0, 0]
  obtain ⟨hd1, hb1⟩ := htensor T hT hTBound hSecond ![1, 0, 0]
  obtain ⟨hd2, hb2⟩ := htensor T hT hTBound hSecond ![0, 1, 0]
  obtain ⟨hd3, hb3⟩ := htensor D.ricciEvaluation hRic hRicBound hTBound ![2, 0]
  obtain ⟨hd4, hb4⟩ := htensor D.ricciEvaluation hRic hRicBound hTBound ![1, 1]
  change DifferentiableAt ℝ f0 x at hd0
  change DifferentiableAt ℝ f1 x at hd1
  change DifferentiableAt ℝ f2 x at hd2
  change DifferentiableAt ℝ f3 x at hd3
  change DifferentiableAt ℝ f4 x at hd4
  have h0 : |m62ArcDerivative F c t f0 x| ≤ K * (1 + 4 * k) := by
    convert hb0 using 1
    congr 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1]
    ring
  have h1 : |m62ArcDerivative F c t f1 x| ≤ K * (k + u + 2 * k ^ 2) := by
    convert hb1 using 1
    congr 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hN2]
    ring
  have h2 : |m62ArcDerivative F c t f2 x| ≤ K * (k + u + 2 * k ^ 2) := by
    convert hb2 using 1
    congr 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hN2]
    ring
  have h3 : |m62ArcDerivative F c t f3 x| ≤ K * (u + w + k * u) := by
    convert hb3 using 1
    congr 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hN2, hN3]
    ring
  have h4 : |m62ArcDerivative F c t f4 x| ≤ K * (k ^ 2 + 2 * k * u) := by
    convert hb4 using 1
    congr 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN1, hN2]
    ring
  have heq : m62ArcSecondDerivative F c t (m62TangentRicci F c t) =
      fun y => f0 y + f1 y + 4 * f2 y + 2 * f3 y + 2 * f4 y := by
    funext y
    simpa only [f0, f1, f2, f3, f4, Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq,
      V, LeviCivitaData.ricciEvaluation, Fin.cons_zero, Fin.cons_one]
      using (m63TangentRicci_arc_derivatives F c hc ht y).2
  change DifferentiableAt ℝ (m62ArcSecondDerivative F c t (m62TangentRicci F c t)) x ∧
    |m62ArcDerivative F c t (m62ArcSecondDerivative F c t (m62TangentRicci F c t)) x| ≤
      K * (1 + 9 * k + 7 * u + 12 * k ^ 2 + 6 * k * u + 2 * w)
  rw [heq]
  have hd := (((hd0.hasDerivAt.add hd1.hasDerivAt).add
    (hd2.hasDerivAt.const_mul 4)).add (hd3.hasDerivAt.const_mul 2)).add
      (hd4.hasDerivAt.const_mul 2)
  change HasDerivAt (fun y => f0 y + f1 y + 4 * f2 y + 2 * f3 y + 2 * f4 y)
    (deriv f0 x + deriv f1 x + 4 * deriv f2 x + 2 * deriv f3 x + 2 * deriv f4 x) x at hd
  refine ⟨hd.differentiableAt, ?_⟩
  have hcombine : m62ArcDerivative F c t
      (fun y => f0 y + f1 y + 4 * f2 y + 2 * f3 y + 2 * f4 y) x =
      m62ArcDerivative F c t f0 x + m62ArcDerivative F c t f1 x +
        4 * m62ArcDerivative F c t f2 x + 2 * m62ArcDerivative F c t f3 x +
        2 * m62ArcDerivative F c t f4 x := by
    rw [m62ArcDerivative, hd.deriv]
    dsimp only [m62ArcDerivative]
    ring
  rw [hcombine]
  apply abs_le.mpr
  constructor
  · nlinarith only [(abs_le.mp h0).1, (abs_le.mp h1).1, (abs_le.mp h2).1,
      (abs_le.mp h3).1, (abs_le.mp h4).1]
  · nlinarith only [(abs_le.mp h0).2, (abs_le.mp h1).2, (abs_le.mp h2).2,
      (abs_le.mp h3).2, (abs_le.mp h4).2]

end PoincareConjecture
