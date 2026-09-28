import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurveTensorLeibniz
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





theorem m63FirstJetAmbientPair_jet_derivative_bound [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (j : ℕ) {K : ℝ} (_hK : 0 ≤ K)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ)
    (hRiemann : ∀ v : Fin 5 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          (F.connection t).riemannEvaluation (c x t) v| ≤ K)
    (hRiemannSecond : ∀ v : Fin 6 → TangentSpace (𝓡 n) (c x t),
      (∀ i, (F.metric t).tangentNorm (c x t) (v i) ≤ 1) →
        |(F.connection t).covariantTensorDerivative
          ((F.connection t).covariantTensorDerivative
            (F.connection t).riemannEvaluation) (c x t) v| ≤ K)
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
    let D := F.connection t
    let R := D.riemannEvaluation
    let R1 := D.covariantTensorDerivative R
    let T := D.covariantTensorDerivative D.ricciEvaluation
    let U := D.covariantTensorDerivative T
    let S := spatialUnitTangent F c t
    let H := m63CurvatureJet F c 0 t
    let B := m63CurvatureJet F c 1 t
    let E := fun (i : ℕ) y =>
      let Z := m63CurvatureJet F c i t y
      R1 (c y t) ![S y, H y, S y, Z, S y] +
        R (c y t) ![B y, S y, Z, S y] + 2 * R (c y t) ![H y, S y, Z, H y] -
        2 * U (c y t) ![S y, S y, S y, Z] + U (c y t) ![S y, Z, S y, S y] -
        3 * T (c y t) ![H y, S y, Z] - 3 * T (c y t) ![S y, H y, Z] +
        3 * T (c y t) ![Z, S y, H y]
    let g := F.metric t
    let k := g.tangentNorm (c x t) (H x)
    let u := g.tangentNorm (c x t) (B x)
    let w := g.tangentNorm (c x t) (m63CurvatureJet F c 2 t x)
    DifferentiableAt ℝ (E j) x ∧
      |m62ArcDerivative F c t (E j) x - E (j + 1) x| ≤
        K * (w + 11 * u + 19 * k + 14 * k ^ 2 + 6 * k * u + 2 * k ^ 3 + 3) *
          g.tangentNorm (c x t) (m63CurvatureJet F c j t x) := by
  classical
  let D := F.connection t
  let g := F.metric t
  let p := c x t
  let R := D.riemannEvaluation
  let R1 := D.covariantTensorDerivative R
  let T := D.covariantTensorDerivative D.ricciEvaluation
  let U := D.covariantTensorDerivative T
  let V : ℕ → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2)
    | 0, z => spatialUnitTangent F c z.2 z.1
    | i + 1, z => m63CurvatureJet F c i z.2 z.1
  let N : ℕ → ℝ := fun i => g.tangentNorm p (V i (x, t))
  let k := N 1
  let u := N 2
  let w := N 3
  let z := N (j + 1)
  have hV (i : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun q => (⟨c q.1 q.2, V i q⟩ : TangentBundle (𝓡 n) M))
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
  have hNz : N (j + 1) = z := rfl
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
      (alpha : Fin d → ℕ) (itest : Fin d) :
      DifferentiableAt ℝ (fun y => Q (c y t) ((fun l => V l (y, t)) ∘ alpha)) x ∧
        |m62ArcDerivative F c t (fun y => Q (c y t)
            ((fun l => V l (y, t)) ∘ alpha)) x -
          Q p ((fun l => V l (x, t)) ∘ Function.update alpha itest (alpha itest + 1))| ≤
          K * ((∏ i, N (alpha i)) +
            ∑ i ∈ Finset.univ.erase itest,
              ∏ l, N (Function.update alpha i (alpha i + 1) l)) := by
    let Y := fun i q => V (alpha i) q
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
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin d))
      (fun i => Q p (fun l => V (Function.update alpha i (alpha i + 1) l) (x, t)))
      (Finset.mem_univ itest)
    have hres : m62ArcDerivative F c t (fun y => Q (c y t)
          ((fun l => V l (y, t)) ∘ alpha)) x -
        Q p ((fun l => V l (x, t)) ∘ Function.update alpha itest (alpha itest + 1)) =
        D.covariantTensorDerivative Q p
          (Fin.cons (V 0 (x, t)) (fun i => Y i (x, t))) +
          ∑ i ∈ Finset.univ.erase itest,
            Q p (fun l => V (Function.update alpha i (alpha i + 1) l) (x, t)) := by
      rw [harc, ← hsum]
      simp only [Function.comp_def]
      ring
    rw [hres]
    calc
      _ ≤ |D.covariantTensorDerivative Q p
          (Fin.cons (V 0 (x, t)) (fun i => Y i (x, t)))| +
          |∑ i ∈ Finset.univ.erase itest,
            Q p (fun l => V (Function.update alpha i (alpha i + 1) l) (x, t))| :=
        abs_add_le _ _
      _ ≤ K * (∏ i, N (alpha i)) +
          ∑ i ∈ Finset.univ.erase itest,
            K * ∏ l, N (Function.update alpha i (alpha i + 1) l) :=
        add_le_add hlead' ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => hslots i))
      _ = _ := by rw [← Finset.mul_sum, ← mul_add]
  have hR := M04.isSmoothCovariantTensor_riemannEvaluation D
  have hR1 := M04.isSmoothCovariantTensor_covariantTensorDerivative D hR
  have hT := M04.isSmoothCovariantTensor_covariantTensorDerivative D
    (M04.isSmoothCovariantTensor_ricciEvaluation D)
  have hU := M04.isSmoothCovariantTensor_covariantTensorDerivative D hT
  have hRBound := hBounds.riemann t (Ioo_subset_Icc_self ht) p
  have hTBound := hBounds.ricci_derivative t (Ioo_subset_Icc_self ht) p
  let f0 (i : ℕ) : ℝ → ℝ := fun y => R1 (c y t)
    ((fun l => V l (y, t)) ∘ ![0, 1, 0, i + 1, 0])
  let f1 (i : ℕ) : ℝ → ℝ := fun y => R (c y t)
    ((fun l => V l (y, t)) ∘ ![2, 0, i + 1, 0])
  let f2 (i : ℕ) : ℝ → ℝ := fun y => R (c y t)
    ((fun l => V l (y, t)) ∘ ![1, 0, i + 1, 1])
  let f3 (i : ℕ) : ℝ → ℝ := fun y => U (c y t)
    ((fun l => V l (y, t)) ∘ ![0, 0, 0, i + 1])
  let f4 (i : ℕ) : ℝ → ℝ := fun y => U (c y t)
    ((fun l => V l (y, t)) ∘ ![0, i + 1, 0, 0])
  let f5 (i : ℕ) : ℝ → ℝ := fun y => T (c y t)
    ((fun l => V l (y, t)) ∘ ![1, 0, i + 1])
  let f6 (i : ℕ) : ℝ → ℝ := fun y => T (c y t)
    ((fun l => V l (y, t)) ∘ ![0, 1, i + 1])
  let f7 (i : ℕ) : ℝ → ℝ := fun y => T (c y t)
    ((fun l => V l (y, t)) ∘ ![i + 1, 0, 1])
  obtain ⟨hd0, hb0⟩ := htensor R1 hR1 hRiemann hRiemannSecond ![0, 1, 0, j + 1, 0] 3
  obtain ⟨hd1, hb1⟩ := htensor R hR hRBound hRiemann ![2, 0, j + 1, 0] 2
  obtain ⟨hd2, hb2⟩ := htensor R hR hRBound hRiemann ![1, 0, j + 1, 1] 2
  obtain ⟨hd3, hb3⟩ := htensor U hU hSecond hThird ![0, 0, 0, j + 1] 3
  obtain ⟨hd4, hb4⟩ := htensor U hU hSecond hThird ![0, j + 1, 0, 0] 1
  obtain ⟨hd5, hb5⟩ := htensor T hT hTBound hSecond ![1, 0, j + 1] 2
  obtain ⟨hd6, hb6⟩ := htensor T hT hTBound hSecond ![0, 1, j + 1] 2
  obtain ⟨hd7, hb7⟩ := htensor T hT hTBound hSecond ![j + 1, 0, 1] 0
  have h0 : |m62ArcDerivative F c t (f0 j) x - f0 (j + 1) x| ≤
      K * (k + u + 3 * k ^ 2) * z := by
    have hnext : Function.update (![0, 1, 0, j + 1, 0] : Fin 5 → ℕ) 3
        ((![0, 1, 0, j + 1, 0] : Fin 5 → ℕ) 3 + 1) = ![0, 1, 0, j + 1 + 1, 0] := by
      funext i
      fin_cases i <;> rfl
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] at hb0
    rw [hnext] at hb0
    change |m62ArcDerivative F c t (f0 j) x - f0 (j + 1) x| ≤ _ at hb0
    convert hb0 using 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hN2, hNz]
    ring
  have h1 : |m62ArcDerivative F c t (f1 j) x - f1 (j + 1) x| ≤
      K * (u + w + 2 * k * u) * z := by
    have hnext : Function.update (![2, 0, j + 1, 0] : Fin 4 → ℕ) 2
        ((![2, 0, j + 1, 0] : Fin 4 → ℕ) 2 + 1) = ![2, 0, j + 1 + 1, 0] := by
      funext i
      fin_cases i <;> rfl
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] at hb1
    rw [hnext] at hb1
    change |m62ArcDerivative F c t (f1 j) x - f1 (j + 1) x| ≤ _ at hb1
    convert hb1 using 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hN2, hN3, hNz]
    ring
  have h2 : |m62ArcDerivative F c t (f2 j) x - f2 (j + 1) x| ≤
      K * (k ^ 2 + 2 * k * u + k ^ 3) * z := by
    have hnext : Function.update (![1, 0, j + 1, 1] : Fin 4 → ℕ) 2
        ((![1, 0, j + 1, 1] : Fin 4 → ℕ) 2 + 1) = ![1, 0, j + 1 + 1, 1] := by
      funext i
      fin_cases i <;> rfl
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] at hb2
    rw [hnext] at hb2
    change |m62ArcDerivative F c t (f2 j) x - f2 (j + 1) x| ≤ _ at hb2
    convert hb2 using 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hN2, hNz]
    ring
  have h3 : |m62ArcDerivative F c t (f3 j) x - f3 (j + 1) x| ≤
      K * (1 + 3 * k) * z := by
    have hnext : Function.update (![0, 0, 0, j + 1] : Fin 4 → ℕ) 3
        ((![0, 0, 0, j + 1] : Fin 4 → ℕ) 3 + 1) = ![0, 0, 0, j + 1 + 1] := by
      funext i
      fin_cases i <;> rfl
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] at hb3
    rw [hnext] at hb3
    change |m62ArcDerivative F c t (f3 j) x - f3 (j + 1) x| ≤ _ at hb3
    convert hb3 using 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hNz]
    ring
  have h4 : |m62ArcDerivative F c t (f4 j) x - f4 (j + 1) x| ≤
      K * (1 + 3 * k) * z := by
    have hnext : Function.update (![0, j + 1, 0, 0] : Fin 4 → ℕ) 1
        ((![0, j + 1, 0, 0] : Fin 4 → ℕ) 1 + 1) = ![0, j + 1 + 1, 0, 0] := by
      funext i
      fin_cases i <;> rfl
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] at hb4
    rw [hnext] at hb4
    change |m62ArcDerivative F c t (f4 j) x - f4 (j + 1) x| ≤ _ at hb4
    convert hb4 using 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hNz]
    ring
  have h5 : |m62ArcDerivative F c t (f5 j) x - f5 (j + 1) x| ≤
      K * (k + u + k ^ 2) * z := by
    have hnext : Function.update (![1, 0, j + 1] : Fin 3 → ℕ) 2
        ((![1, 0, j + 1] : Fin 3 → ℕ) 2 + 1) = ![1, 0, j + 1 + 1] := by
      funext i
      fin_cases i <;> rfl
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] at hb5
    rw [hnext] at hb5
    change |m62ArcDerivative F c t (f5 j) x - f5 (j + 1) x| ≤ _ at hb5
    convert hb5 using 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hN2, hNz]
    ring
  have h6 : |m62ArcDerivative F c t (f6 j) x - f6 (j + 1) x| ≤
      K * (k + u + k ^ 2) * z := by
    have hnext : Function.update (![0, 1, j + 1] : Fin 3 → ℕ) 2
        ((![0, 1, j + 1] : Fin 3 → ℕ) 2 + 1) = ![0, 1, j + 1 + 1] := by
      funext i
      fin_cases i <;> rfl
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] at hb6
    rw [hnext] at hb6
    change |m62ArcDerivative F c t (f6 j) x - f6 (j + 1) x| ≤ _ at hb6
    convert hb6 using 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hN2, hNz]
    ring
  have h7 : |m62ArcDerivative F c t (f7 j) x - f7 (j + 1) x| ≤
      K * (k + u + k ^ 2) * z := by
    have hnext : Function.update (![j + 1, 0, 1] : Fin 3 → ℕ) 0
        ((![j + 1, 0, 1] : Fin 3 → ℕ) 0 + 1) = ![j + 1 + 1, 0, 1] := by
      funext i
      fin_cases i <;> rfl
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] at hb7
    rw [hnext] at hb7
    change |m62ArcDerivative F c t (f7 j) x - f7 (j + 1) x| ≤ _ at hb7
    convert hb7 using 1
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, Function.update_apply,
      hN0, hN1, hN2, hNz]
    ring
  let E (i : ℕ) : ℝ → ℝ := fun y => f0 i y + f1 i y + 2 * f2 i y -
    2 * f3 i y + f4 i y - 3 * f5 i y - 3 * f6 i y + 3 * f7 i y
  have hE (i : ℕ) : E i = fun y =>
      R1 (c y t) ![V 0 (y, t), V 1 (y, t), V 0 (y, t), V (i + 1) (y, t), V 0 (y, t)] +
        R (c y t) ![V 2 (y, t), V 0 (y, t), V (i + 1) (y, t), V 0 (y, t)] +
        2 * R (c y t) ![V 1 (y, t), V 0 (y, t), V (i + 1) (y, t), V 1 (y, t)] -
        2 * U (c y t) ![V 0 (y, t), V 0 (y, t), V 0 (y, t), V (i + 1) (y, t)] +
        U (c y t) ![V 0 (y, t), V (i + 1) (y, t), V 0 (y, t), V 0 (y, t)] -
        3 * T (c y t) ![V 1 (y, t), V 0 (y, t), V (i + 1) (y, t)] -
        3 * T (c y t) ![V 0 (y, t), V 1 (y, t), V (i + 1) (y, t)] +
        3 * T (c y t) ![V (i + 1) (y, t), V 0 (y, t), V 1 (y, t)] := by
    simp only [E, f0, f1, f2, f3, f4, f5, f6, f7, Matrix.vecCons,
      Fin.comp_cons, Matrix.empty_eq]
  suffices h : DifferentiableAt ℝ (E j) x ∧
      |m62ArcDerivative F c t (E j) x - E (j + 1) x| ≤
        K * (w + 11 * u + 19 * k + 14 * k ^ 2 + 6 * k * u + 2 * k ^ 3 + 3) * z by
    simpa only [hE, V, D, R, R1, T, U] using h
  have hd := ((((((hd0.hasDerivAt.add hd1.hasDerivAt).add
    (hd2.hasDerivAt.const_mul 2)).sub (hd3.hasDerivAt.const_mul 2)).add
    hd4.hasDerivAt).sub (hd5.hasDerivAt.const_mul 3)).sub
    (hd6.hasDerivAt.const_mul 3)).add (hd7.hasDerivAt.const_mul 3)
  change HasDerivAt (E j)
    (deriv (f0 j) x + deriv (f1 j) x + 2 * deriv (f2 j) x - 2 * deriv (f3 j) x +
      deriv (f4 j) x - 3 * deriv (f5 j) x - 3 * deriv (f6 j) x +
      3 * deriv (f7 j) x) x at hd
  refine ⟨hd.differentiableAt, ?_⟩
  have hcombine : m62ArcDerivative F c t (E j) x =
      m62ArcDerivative F c t (f0 j) x + m62ArcDerivative F c t (f1 j) x +
        2 * m62ArcDerivative F c t (f2 j) x - 2 * m62ArcDerivative F c t (f3 j) x +
        m62ArcDerivative F c t (f4 j) x - 3 * m62ArcDerivative F c t (f5 j) x -
        3 * m62ArcDerivative F c t (f6 j) x + 3 * m62ArcDerivative F c t (f7 j) x := by
    rw [m62ArcDerivative, hd.deriv]
    dsimp only [m62ArcDerivative]
    ring
  rw [hcombine]
  dsimp only [E]
  apply abs_le.mpr
  constructor
  · nlinarith only [(abs_le.mp h0).1, (abs_le.mp h1).1, (abs_le.mp h2).1,
      (abs_le.mp h3).2, (abs_le.mp h4).1, (abs_le.mp h5).2,
      (abs_le.mp h6).2, (abs_le.mp h7).1]
  · nlinarith only [(abs_le.mp h0).2, (abs_le.mp h1).2, (abs_le.mp h2).2,
      (abs_le.mp h3).1, (abs_le.mp h4).2, (abs_le.mp h5).1,
      (abs_le.mp h6).1, (abs_le.mp h7).2]

end PoincareConjecture
