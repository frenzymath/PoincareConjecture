import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularSurgeryData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapEmbedding
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryDiscIntersection

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable (a : ℝ → ℝ) (b : E2 → ℝ)
variable (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
variable (ha0 : ∀ z, a z ≠ 0) (hb0 : ∀ x, b x ≠ 0)

theorem surgeryCapMap_mem_retained_iff
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbpos : ∀ x, 0 < b x)
    (hanear : ∀ z, |z| ≤ 1 / 4 → a z = (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbfar : ∀ x, 1 / 2 ≤ ‖x‖ → b x = 1)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData ψ u t)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (sigma : ℝ) (hsigma : |sigma| = 1) {delta r k l M : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta) (hk : 0 < k)
    (hcwidth : k * (1 - r) < D.width)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta →
      x ∈ e.source ∧ e x = D.sourceCollar
        (circleDirection x, sigma * (k * (1 - ‖x‖))))
    (hl : 0 < l) (hlM : l * M < k * (1 - r) / 4)
    (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0)
    (hM : |(surgeryCapModel a b ha hb ha0 hb0 q).2| ≤ M) :
    surgeryCapMap a b ha hb ha0 hb0 D.tube t sigma (k * (1 - r)) l q ∈
        (fun p : UnitTwoSphere => ψ (p, 0)) '' (e '' closedBall 0 r) ↔
      (heightCoordinates (q : E3)).2 = 0 := by
  let c := k * (1 - r)
  let s := c + l * (surgeryCapModel a b ha hb ha0 hb0 q).2
  have hc : 0 < c := mul_pos hk (sub_pos.mpr hr1)
  have hbounds : 3 * c / 4 < s ∧ s ≤ c := by
    have h := surgeryCapCoordinates_south_height_bounds a b ha hb ha0 hb0 hbpos
      t sigma c l M hsigma hl hlM q hq hM
    rw [surgeryCapCoordinates_signed_height a b ha hb ha0 hb0 t sigma c l hsigma q] at h
    exact h
  have hs : 0 < s := lt_trans (by positivity) hbounds.1
  have hband (v : ℝ) (hv : 0 ≤ v) (hvc : v ≤ c) :
      sigma * v ∈ Ioo (-D.width) D.width := by
    apply abs_lt.mp
    rw [abs_mul, hsigma, one_mul, abs_of_nonneg hv]
    exact hvc.trans_lt hcwidth
  have hcentral : Function.Injective (fun p : UnitTwoSphere => ψ (p, 0)) := by
    intro p q hpq
    exact congrArg Prod.fst (hψ.2.1
      (show (p, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1) 1 by simp)
      (show (q, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1) 1 by simp) hpq)
  constructor
  · rintro ⟨p, hp, hpq⟩
    let X := (surgeryCapModel a b ha hb ha0 hb0 q).1
    have hX : X ∈ closedBall (0 : E2) 1 := mem_closedBall_zero_iff.mpr
      (surgeryCapModel_fst_norm_le a b ha hb ha0 hb0 hapos habound q)
    have hz : t + sigma * s ∈ Ioo (t - D.width) (t + D.width) := by
      have h := hband s hs.le hbounds.2
      constructor <;> linarith [h.1, h.2]
    have hXunit : X ∈ sphere (0 : E2) 1 :=
      (D.surface_mem X hX (t + sigma * s) hz).mp ⟨p, hpq⟩
    let theta : UnitCircle := ⟨X, hXunit⟩
    have hrec : ψ (D.sourceCollar (theta, sigma * s), 0) =
        surgeryCapMap a b ha hb ha0 hb0 D.tube t sigma c l q :=
      D.reconstruction theta (sigma * s) (hband s hs.le hbounds.2)
    have hretained : D.sourceCollar (theta, sigma * s) ∈ e '' closedBall 0 r := by
      rw [hcentral (hrec.trans hpq.symm)]
      exact hp
    have hsc : s = c := (sourceDisc_collar_mem_retained_iff e he D.sourceCollar
      sigma hr hr1 hrdelta hk hnear theta hs.le hbounds.2).mp hretained
    have hzero : (surgeryCapModel a b ha hb ha0 hb0 q).2 = 0 := by
      dsimp [s] at hsc
      nlinarith
    apply le_antisymm hq
    by_contra hn
    have hneg := (surgeryCapModel_snd_neg_iff a b ha hb ha0 hb0 hbpos q).mpr
      (lt_of_not_ge hn)
    linarith
  · intro hzero
    let theta := circleDirection (heightCoordinates (q : E3)).1
    have hretained : D.sourceCollar (theta, sigma * c) ∈ e '' closedBall 0 r :=
      (sourceDisc_collar_mem_retained_iff e he D.sourceCollar sigma
        hr hr1 hrdelta hk hnear theta hc.le le_rfl).mpr rfl
    refine ⟨D.sourceCollar (theta, sigma * c), hretained, ?_⟩
    change ψ (D.sourceCollar (theta, sigma * c), 0) =
      surgeryCapMap a b ha hb ha0 hb0 D.tube t sigma c l q
    rw [D.reconstruction theta (sigma * c) (hband c hc.le le_rfl), surgeryCapMap,
      surgeryCapCoordinates_cylinder a b ha hb ha0 hb0 hanear hbfar t sigma c l q
        (by rw [hzero]; norm_num), hzero, mul_zero, add_zero]

end PoincareConjecture.M25.Topology3D
