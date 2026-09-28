import PoincareConjecture.Proofs.M47.PositiveHistoryOrdinary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

theorem horizon_cylinder_metric_comparison
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {T a K : ℝ}
    (ha : a < 0) (hK : 0 ≤ K)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hne : (U : Set (F.slice T).carrier).Nonempty)
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc a 0) U)
    (hbased : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x)
    (hcurv : ∀ s hs x, x ∈ U →
      (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤ K)
    {s C : ℝ} (hs : s ∈ Icc a 0)
    (hfactor : Real.exp (6 * K * (-s)) ≤ C ^ 2) :
    ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      (F.metric T).inner x v v ≤ C ^ 2 * e.pullbackInner s hs x v v ∧
        e.pullbackInner s hs x v v ≤ C ^ 2 * (F.metric T).inner x v v := by
  obtain ⟨G, hread⟩ := M47Positive.exists_component_closed_ordinary_history P ha U hne e
  have hterminal (z : U) (v w : TangentSpace (𝓡 3) z) :
      (G.metric T).inner z v w = (F.metric T).inner z.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) z v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice T).carrier) z w) := by
    have hfunctions :
        (⟨T + 0 / 1, fun y : U => e.forward 0 ⟨ha.le, le_rfl⟩ y.val⟩ :
          (t : ℝ) × (U → (F.slice t).carrier)) =
            ⟨T, (Subtype.val : U → (F.slice T).carrier)⟩ := by
      apply Sigma.ext (by simp)
      apply Function.hfunext rfl
      intro y y' hyy
      cases hyy
      exact hbased _ y.val y.property
    have hpull := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
      (F.metric p.1).inner (p.2 z)
        (mfderiv (𝓡 3) (𝓡 3) p.2 z v) (mfderiv (𝓡 3) (𝓡 3) p.2 z w)) hfunctions
    exact (congrArg (fun t => (G.metric t).inner z v w)
      (show T + 0 / 1 = T by simp)).symm.trans
        (((hread 0 ⟨ha.le, le_rfl⟩ z).1 v w).symm.trans hpull)
  have hsG : T + s / 1 ∈ Icc (T + a) T := by
    simp only [div_one]
    constructor <;> linarith only [hs.1, hs.2]
  have hTG : T ∈ Icc (T + a) T := ⟨by linarith only [ha], le_rfl⟩
  have hbound : ∀ t ∈ Icc (T + s / 1) T, ∀ z : U,
      (G.connection t).curvatureTensorNorm z ≤ K := by
    intro t ht z
    have hparam : t - T ∈ Icc a 0 := by
      simp only [div_one] at ht
      constructor <;> linarith only [ht.1, ht.2, hs.1]
    have hc : T + (t - T) / 1 = t := by simp only [div_one, add_sub_cancel]
    have hnorm : (G.connection t).curvatureTensorNorm z =
        (F.connection (T + (t - T) / 1)).curvatureTensorNorm
          (e.forward (t - T) hparam z.val) :=
      (congrArg (fun t => (G.connection t).curvatureTensorNorm z) hc).symm.trans
        (hread (t - T) hparam z).2.2
    exact hnorm.trans_le (hcurv (t - T) hparam z.val z.property)
  intro x hx v
  let z : U := ⟨x, hx⟩
  obtain ⟨w, hw⟩ := ((G.metric T).mfderiv_bijective_of_pullback_eq
    (F.metric T) z (fun v w => (hterminal z v w).symm)).2 v
  have hcomparison := P.m04.metric_comparison 3 U (Icc (T + a) T) G
    (T + s / 1) T K hsG hTG hsG.2 hK hbound z w
  norm_num only [Nat.cast_ofNat] at hcomparison
  have hpositiveFactor : Real.exp (6 * K * (T - (T + s / 1))) =
      Real.exp (6 * K * (-s)) := by
    congr 1
    simp only [div_one]
    ring
  rw [hpositiveFactor] at hcomparison
  have hcancel : Real.exp (6 * K * (-s)) *
      Real.exp (-6 * K * (T - (T + s / 1))) = 1 := by
    rw [← Real.exp_add]
    rw [show 6 * K * (-s) + -6 * K * (T - (T + s / 1)) = 0 by
      simp only [div_one]; ring, Real.exp_zero]
  have hnonneg (t : ℝ) : 0 ≤ (G.metric t).inner z w w := by
    by_cases hw0 : w = 0
    · simp [hw0]
    · exact ((G.metric t).pos z w hw0).le
  have hback := mul_le_mul_of_nonneg_left hcomparison.1
    (Real.exp_pos (6 * K * (-s))).le
  rw [← mul_assoc, hcancel, one_mul] at hback
  have hlower := hcomparison.2.trans
    (mul_le_mul_of_nonneg_right hfactor (hnonneg (T + s / 1)))
  have hupper := hback.trans (mul_le_mul_of_nonneg_right hfactor (hnonneg T))
  have hf := ((e.forward_smooth s hs x hx).contMDiffAt
    (U.isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp z hf
    ((contMDiff_subtype_val (n := ∞) z).mdifferentiableAt (by simp))
  change mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) z = _ at hd
  have hpull := (hread s hs z).1 w w
  rw [hd] at hpull
  simp only [ContinuousLinearMap.comp_apply] at hpull
  rw [hw] at hpull
  have hterminalValue : (G.metric T).inner z w w = (F.metric T).inner x v v := by
    rw [hterminal, hw]
  have hpullValue : e.pullbackInner s hs x v v =
      (G.metric (T + s / 1)).inner z w w := by
    simpa only [SurgeryFlowCylinder.pullbackInner, one_mul] using hpull
  rw [hpullValue, ← hterminalValue]
  exact ⟨hlower, hupper⟩

end PoincareConjecture.Proofs.M47
