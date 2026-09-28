import PoincareConjecture.Proofs.M47.ComponentEstimateStrictHistory
import PoincareConjecture.Proofs.M47.ComponentEstimateFrontierLimits
import PoincareConjecture.Statements.M47ComponentAnalytics
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

theorem component_cylinder_quadratic_le_two
    (P : M47Predecessors.{u}) (PA : M47ComponentAnalyticPredecessors.{u})
    {F : SurgeryFlowData.{u}} {origin a K : ℝ} (ha : a < 0) (hK : 0 ≤ K)
    (U : TopologicalSpace.Opens (F.slice origin).carrier)
    (hne : (U : Set (F.slice origin).carrier).Nonempty)
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc a 0) U)
    (he : ∀ hs x, x ∈ U → HEq (e.forward 0 hs x) x)
    (hshort : 6 * K * (-a) ≤ 1 / 2)
    (hcurvature : ∀ s : ℝ, ∀ hs : s ∈ Ioc a 0, ∀ x ∈ U,
      (F.connection (origin + s / 1)).curvatureTensorNorm
        (e.forward s ⟨hs.1.le, hs.2⟩ x) ≤ K) :
    ∀ s : ℝ, ∀ hs : s ∈ Icc a 0, ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      e.pullbackInner s hs x v v ≤ 2 * (F.metric origin).inner x v v := by
  obtain ⟨G, hread⟩ := exists_component_strict_ordinary_history P ha U hne e
  have hterminal (z : U) (v w : TangentSpace (𝓡 3) z) :
      (G.metric origin).inner z v w = (F.metric origin).inner z.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice origin).carrier) z v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → (F.slice origin).carrier) z w) := by
    have hfunctions :
        (⟨origin + 0 / 1, fun y : U => e.forward 0 ⟨ha.le, le_rfl⟩ y.val⟩ :
          (t : ℝ) × (U → (F.slice t).carrier)) =
            ⟨origin, (Subtype.val : U → (F.slice origin).carrier)⟩ := by
      apply Sigma.ext (by simp)
      apply Function.hfunext rfl
      intro y y' hyy
      cases hyy
      exact he _ y.val y.property
    have hpull := congrArg (fun p : (t : ℝ) × (U → (F.slice t).carrier) =>
      (F.metric p.1).inner (p.2 z)
        (mfderiv (𝓡 3) (𝓡 3) p.2 z v) (mfderiv (𝓡 3) (𝓡 3) p.2 z w)) hfunctions
    exact (congrArg (fun t => (G.metric t).inner z v w)
      (show origin + 0 / 1 = origin by simp)).symm.trans
        ((((hread 0 ⟨ha, le_rfl⟩ z).1 v w).symm).trans hpull)
  have hstrict (s : ℝ) (hs : s ∈ Ioc a 0) (x : (F.slice origin).carrier) (hx : x ∈ U)
      (v : TangentSpace (𝓡 3) x) :
      e.pullbackInner s ⟨hs.1.le, hs.2⟩ x v v ≤ 2 * (F.metric origin).inner x v v := by
    have hstart : origin + s / 1 ∈ Ioc (origin + a) origin := by
      simp only [div_one]
      constructor <;> linarith [hs.1, hs.2]
    have hend : origin ∈ Ioc (origin + a) origin := ⟨by linarith, le_rfl⟩
    have htime : origin + s / 1 ≤ origin := hstart.2
    have hbound : ∀ t ∈ Icc (origin + s / 1) origin, ∀ z : U,
        (G.connection t).curvatureTensorNorm z ≤ K := by
      intro t ht z
      have hparam : t - origin ∈ Ioc a 0 := by
        simp only [div_one] at ht
        constructor <;> linarith [ht.1, ht.2, hs.1]
      have hc : origin + (t - origin) / 1 = t := by simp only [div_one, add_sub_cancel]
      have hnorm : (G.connection t).curvatureTensorNorm z =
          (F.connection (origin + (t - origin) / 1)).curvatureTensorNorm
            (e.forward (t - origin) ⟨hparam.1.le, hparam.2⟩ z.val) :=
        (congrArg (fun u => (G.connection u).curvatureTensorNorm z) hc).symm.trans
          (hread (t - origin) hparam z).2.2
      exact hnorm.trans_le (hcurvature (t - origin) hparam z.val z.property)
    let z : U := ⟨x, hx⟩
    obtain ⟨w, hw⟩ := ((G.metric origin).mfderiv_bijective_of_pullback_eq
      (F.metric origin) z (fun v w => (hterminal z v w).symm)).2 v
    have hcomparison := (PA.metric_comparison U (Ioc (origin + a) origin) G
      (origin + s / 1) origin K hstart hend htime hK hbound z w).1
    let lambda := 6 * K * (origin - (origin + s / 1))
    have hlambda : lambda ≤ 1 / 2 := by
      have h := mul_le_mul_of_nonneg_left (show -s ≤ -a by linarith [hs.1])
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hK)
      dsimp only [lambda]
      simp only [div_one]
      nlinarith [hshort]
    have hexp : Real.exp lambda ≤ 2 := by
      apply (Real.exp_le_exp.mpr hlambda).trans
      have h := Real.exp_bound_div_one_sub_of_interval (x := (1 : ℝ) / 2)
        (by norm_num) (by norm_num)
      norm_num at h ⊢
      exact h
    have hcancel : Real.exp lambda *
        Real.exp (-2 * (3 : ℝ) * K * (origin - (origin + s / 1))) = 1 := by
      rw [← Real.exp_add]
      rw [show lambda + -2 * (3 : ℝ) * K * (origin - (origin + s / 1)) = 0 by
        dsimp only [lambda]; ring, Real.exp_zero]
    have hback := mul_le_mul_of_nonneg_left hcomparison (Real.exp_pos lambda).le
    rw [← mul_assoc, hcancel, one_mul] at hback
    have hnonneg : 0 ≤ (G.metric origin).inner z w w := by
      by_cases hw0 : w = 0
      · simp [hw0]
      · exact ((G.metric origin).pos z w hw0).le
    have hGbound := hback.trans (mul_le_mul_of_nonneg_right hexp hnonneg)
    have hf := ((e.forward_smooth s ⟨hs.1.le, hs.2⟩ x hx).contMDiffAt
      (U.isOpen.mem_nhds hx)).mdifferentiableAt (by simp)
    have hd := mfderiv_comp z hf
      ((contMDiff_subtype_val (n := ∞) z).mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3)
      (fun y : U => e.forward s ⟨hs.1.le, hs.2⟩ y.val) z = _ at hd
    have hpull := (hread s hs z).1 w w
    rw [hd] at hpull
    simp only [ContinuousLinearMap.comp_apply] at hpull
    rw [hw] at hpull
    have hterminalValue : (G.metric origin).inner z w w = (F.metric origin).inner x v v := by
      rw [hterminal, hw]
    have hpullValue : e.pullbackInner s ⟨hs.1.le, hs.2⟩ x v v =
        (G.metric (origin + s / 1)).inner z w w := by
      simpa only [SurgeryFlowCylinder.pullbackInner, one_mul] using hpull
    exact hpullValue.trans_le (hGbound.trans_eq (congrArg (fun r : ℝ => 2 * r) hterminalValue))
  intro s hs x hx v
  rcases lt_or_eq_of_le hs.1 with has | rfl
  · exact hstrict s ⟨has, hs.2⟩ x hx v
  · exact component_cylinder_quadratic_le_at_left e U.isOpen ha hx v
      (fun r hr => hstrict r hr x hx v)

end PoincareConjecture.M47
