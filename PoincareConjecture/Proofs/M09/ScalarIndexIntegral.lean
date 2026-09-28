import PoincareConjecture.Proofs.M09.AdaptedIndexTrace
import PoincareConjecture.Proofs.M09.HarnackIntegral

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology intervalIntegral BigOperators

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def adaptedScalarIndexDensity {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (α : ℝ → M) (c s : ℝ) : ℝ :=
  let D := F.connection (T - s ^ 2)
  (n : ℝ) / c ^ 2 - 4 * s ^ 2 / c ^ 2 * D.scalarCurvature (α s) +
    s ^ 2 / c ^ 2 * (4 * s ^ 2 * D.ricciNormSq (α s) +
      2 * s ^ 2 * D.laplacian D.scalarCurvature (α s) -
      D.ricci (α s) (curveVelocity α s) (curveVelocity α s))

set_option backward.isDefEq.respectTransparency false in
theorem pointwiseSecondVariationDensity_linear_weight_trace {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (α : ℝ → M) (c : ℝ) (hc : 0 < c) (s : ℝ)
    (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
    ∀ e : OrthonormalBasis (Fin n) ℝ (TangentSpace (𝓡 n) (α s)),
      (∑ i, pointwiseSecondVariationDensity F T (α s) s (curveVelocity α s)
        ((s / c) • e i) ((1 / c : ℝ) • e i - (2 * s * (s / c)) •
          ricciOperator hM04 (F.connection (T - s ^ 2)) (α s) (e i))) =
        adaptedScalarIndexDensity F T α c s := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s ^ 2)).toRiemannianMetric⟩
  intro e
  rw [pointwiseSecondVariationDensity_adapted_trace F hM04 T b hb hwindow
    (α s) s hs (curveVelocity α s) (s / c) (1 / c) e]
  unfold adaptedScalarIndexDensity
  field_simp [hc.ne'] <;> ring

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_adaptedScalarIndex_integral {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    IntervalIntegrable (adaptedScalarIndexDensity F T (A.squareFamily Z) (Real.sqrt b))
        MeasureTheory.volume 0 (Real.sqrt b) ∧
      (∫ s in 0..Real.sqrt b, adaptedScalarIndexDensity F T (A.squareFamily Z) (Real.sqrt b) s) =
        (n : ℝ) / Real.sqrt b - 2 * Real.sqrt b *
          (F.connection (T - (Real.sqrt b) ^ 2)).scalarCurvature (A.squareFamily Z (Real.sqrt b)) -
          reducedHarnackIntegral F T (A.gamma Z)
            (backwardScalarEvolutionAlong F T (A.gamma Z)) b / (Real.sqrt b) ^ 2 := by
  let c := Real.sqrt b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  let U := ((fun s : ℝ ↦ (Z, s)) ⁻¹' A.squareDomain) ∩
    Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax)
  have hU : IsOpen U := (A.square_open.preimage
    (continuous_const.prodMk continuous_id)).inter isOpen_Ioo
  have hKU : Set.Icc 0 c ⊆ U := by
    intro s hs
    have hsmax := hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)
    exact ⟨A.square_contains ⟨Set.mem_univ _, hs.1, hsmax⟩,
      (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1, hsmax⟩
  have hα := (lExponentialFamily_squareSlice_contMDiffOn A Z).mono
    (show U ⊆ (fun s : ℝ ↦ (Z, s)) ⁻¹' A.squareDomain from Set.inter_subset_left)
  let S : ℝ → ℝ := fun s ↦ (F.connection (T - s ^ 2)).scalarCurvature (A.squareFamily Z s)
  let E := regularizedCurveEnergy F T (A.squareFamily Z)
  have hS : ContDiffOn ℝ ∞ S U :=
    ((squareTime_scalar_smooth F hM04 T τmax hτmax hwindow).comp
      (contMDiffOn_id.prodMk hα) (fun _ hs ↦ ⟨hs.2, Set.mem_univ _⟩)).contDiffOn
  have hE : ContDiffOn ℝ ∞ E U := regularizedCurveEnergy_contDiffOn F T τmax hτmax hwindow
    (A.squareFamily Z) U hU hα Set.inter_subset_right
  let Q : ℝ → ℝ := fun s ↦ -(s ^ 3 * S s) + s * E s / 4
  let D : ℝ → ℝ := fun s ↦ 2 * s ^ 2 * S s + (1 / 2 : ℝ) * E s
  have hQ : ContDiffOn ℝ ∞ Q U :=
    ((contDiffOn_id.pow 3).mul hS).neg.add ((contDiffOn_id.mul hE).div_const 4)
  have hD : ContDiffOn ℝ ∞ D U :=
    ((contDiffOn_const.mul (contDiffOn_id.pow 2)).mul hS).add (contDiffOn_const.mul hE)
  have hQi : IntervalIntegrable (deriv Q) MeasureTheory.volume 0 c :=
    ((hQ.deriv_of_isOpen hU (m := ∞) (by simp)).continuousOn.mono hKU).intervalIntegrable_of_Icc
      hc.le
  have hDi : IntervalIntegrable D MeasureTheory.volume 0 c :=
    (hD.continuousOn.mono hKU).intervalIntegrable_of_Icc hc.le
  have hQder (s : ℝ) (hs : s ∈ Set.Ioo 0 c) :
      deriv Q s = -(3 * s ^ 2 * S s + s ^ 3 * deriv S s) +
        (E s + s * deriv E s) / 4 := by
    have hSd := ((hS.contDiffAt (hU.mem_nhds (hKU (Set.Ioo_subset_Icc_self hs)))).differentiableAt
      (by simp)).hasDerivAt
    have hEd := ((hE.contDiffAt (hU.mem_nhds (hKU (Set.Ioo_subset_Icc_self hs)))).differentiableAt
      (by simp)).hasDerivAt
    convert! ((((hasDerivAt_pow 3 s).mul hSd).neg).add
      (((hasDerivAt_id s).mul hEd).div_const 4)).deriv using 1 <;>
      simp only [Q, Nat.cast_ofNat, Nat.reduceSub, one_mul, id_eq]
  let I := adaptedScalarIndexDensity F T (A.squareFamily Z) c
  have hrewrite (s : ℝ) (hs : s ∈ Set.Ioo 0 c) :
      I s = (n : ℝ) / c ^ 2 + (deriv Q s - D s / 2) / c ^ 2 := by
    have hαd := (hα.contMDiffAt (hU.mem_nhds (hKU (Set.Ioo_subset_Icc_self hs)))).mdifferentiableAt
      (by simp)
    have hSd := (squareTime_scalar_along_hasDerivAt F hM04 T τmax b hb hmax hwindow
      (A.squareFamily Z) s hs hαd).deriv
    have hEd := (lExponentialFamily_squareEnergy_hasDerivAt hM04 hτmax hwindow
      A Z b hb hmax s (Set.Ioo_subset_Icc_self hs)).deriv
    rw [hQder s hs]
    dsimp only [S, E, D, I, adaptedScalarIndexDensity]
    rw [hSd, hEd]
    ring
  have hRi : IntervalIntegrable
      (fun s ↦ (n : ℝ) / c ^ 2 + (deriv Q s - D s / 2) / c ^ 2)
      MeasureTheory.volume 0 c := intervalIntegrable_const.add ((hQi.sub (hDi.div_const 2)).div_const _)
  have hIi : IntervalIntegrable I MeasureTheory.volume 0 c := hRi.congr_uIoo (by
    intro s hs
    have hs' : s ∈ Set.Ioo 0 c := by simpa only [Set.uIoo_of_le hc.le] using hs
    exact (hrewrite s hs').symm)
  have hFTC : (∫ s in 0..c, deriv Q s) = Q c - Q 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hQi
    intro s hs
    have hs' : s ∈ Set.Icc 0 c := by simpa only [Set.uIcc_of_le hc.le] using hs
    exact ((hQ.contDiffAt (hU.mem_nhds (hKU hs'))).differentiableAt (by simp)).hasDerivAt
  have hQ0 : Q 0 = 0 := by simp [Q]
  have haction : (∫ s in 0..c, D s) = A.action Z b :=
    (lExponentialFamily_action_square_eq A Z b hb hmax).symm
  refine ⟨hIi, ?_⟩
  change (∫ s in 0..c, I s) = (n : ℝ) / c - 2 * c * S c - _ / c ^ 2
  calc
    (∫ s in 0..c, I s) =
        ∫ s in 0..c, ((n : ℝ) / c ^ 2 + (deriv Q s - D s / 2) / c ^ 2) :=
      intervalIntegral.integral_congr_Ioo_of_le hc.le hrewrite
    _ = c * ((n : ℝ) / c ^ 2) + (Q c - A.action Z b / 2) / c ^ 2 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((hQi.sub (hDi.div_const 2)).div_const _), intervalIntegral.integral_const,
        intervalIntegral.integral_div,
        intervalIntegral.integral_sub hQi (hDi.div_const 2), intervalIntegral.integral_div,
        hFTC, haction, hQ0, sub_zero]
      simp only [sub_zero, smul_eq_mul]
    _ = (n : ℝ) / c - 2 * c * S c -
        reducedHarnackIntegral F T (A.gamma Z)
          (backwardScalarEvolutionAlong F T (A.gamma Z)) b / c ^ 2 := by
      rw [lExponentialFamily_harnack_integral_square_eq hM04 hτmax hwindow A Z b hb hmax]
      dsimp only [Q, S, E, c]
      field_simp [hc.ne']
      ring

end PoincareConjecture.Proofs.M09
