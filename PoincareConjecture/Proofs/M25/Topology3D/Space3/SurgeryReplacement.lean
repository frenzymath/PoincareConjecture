import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapIntersection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryNorthChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryPasting













set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem surgeryNorthChart_equator_formula
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (Q : UnitCircle × ℝ → UnitTwoSphere) (sigma k : ℝ) {delta r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta)
    (hR : ∀ x ∈ sphere (0 : E2) 1, R x = r • x)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta →
      x ∈ e.source ∧ e x = Q (circleDirection x, sigma * (k * (1 - ‖x‖))))
    (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 = 0) :
    surgeryNorthChart R e q = Q (circleDirection (heightCoordinates (q : E3)).1,
      sigma * (k * (1 - r))) := by
  let x := (heightCoordinates (q : E3)).1
  have hx : ‖x‖ = 1 := by
    have hs := sphere_height_coordinates_sq q
    rw [hq] at hs
    change ‖x‖ ^ 2 + 0 ^ 2 = 1 at hs
    nlinarith [norm_nonneg x]
  let theta : UnitCircle := ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
  have hcoord : northSphereCoordinate q = x := by
    simp only [northSphereCoordinate, hq, add_zero, inv_one, one_smul, x]
  have hnorm : ‖r • x‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hx, mul_one]
  have hdir : circleDirection (r • x) = circleDirection x := by
    exact (circleDirection_smul theta hr).trans (circleDirection_coe_unit theta).symm
  have heq := (hnear (r • x) (by
    rw [hnorm, abs_of_nonpos (sub_nonpos.mpr hr1.le)]
    linarith)).2
  rw [hnorm, hdir] at heq
  rw [surgeryNorthChart_apply, hcoord, hR x (mem_sphere_zero_iff_norm.mpr hx)]
  exact heq

variable (a : ℝ → ℝ) (b : E2 → ℝ)
variable (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
variable (ha0 : ∀ z, a z ≠ 0) (hb0 : ∀ x, b x ≠ 0)



noncomputable def surgeryReplacementMap
    (ψ : UnitTwoSphere × ℝ → E3)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3) (t sigma r k l : ℝ) :
    UnitTwoSphere → E3 :=
  levelPaste (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2)
    (fun q => ψ (surgeryNorthChart R e q, 0))
    (surgeryCapMap a b ha hb ha0 hb0 T t sigma (k * (1 - r)) l)




theorem surgeryReplacementMap_injective
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbpos : ∀ x, 0 < b x)
    (hanear : ∀ z, |z| ≤ 1 / 4 → a z = (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbfar : ∀ x, 1 / 2 ≤ ‖x‖ → b x = 1)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData ψ u t)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (sigma : ℝ) (hsigma : |sigma| = 1) {delta r k l M : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta) (hk : 0 < k)
    (hcwidth : k * (1 - r) < D.width)
    (hRball : R '' closedBall 0 1 = closedBall 0 r)
    (hR : ∀ x ∈ sphere (0 : E2) 1, R x = r • x)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta →
      x ∈ e.source ∧ e x = D.sourceCollar
        (circleDirection x, sigma * (k * (1 - ‖x‖))))
    (hl : 0 < l) (hlM : l * M < k * (1 - r) / 4)
    (hM : ∀ q : UnitTwoSphere, |(surgeryCapModel a b ha hb ha0 hb0 q).2| ≤ M) :
    Function.Injective
      (surgeryReplacementMap a b ha hb ha0 hb0 ψ R e D.tube t sigma r k l) := by
  let N := surgeryNorthChart R e
  let f : UnitTwoSphere → E3 := fun q => ψ (N q, 0)
  let g := surgeryCapMap a b ha hb ha0 hb0 D.tube t sigma (k * (1 - r)) l
  let height : UnitTwoSphere → ℝ := fun q => (heightCoordinates (q : E3)).2
  have hcentral : Function.Injective (fun p : UnitTwoSphere => ψ (p, 0)) := by
    intro p q hpq
    exact congrArg Prod.fst (hψ.2.1
      (show (p, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1) 1 by simp)
      (show (q, (0 : ℝ)) ∈ univ ×ˢ Ioo (-1) 1 by simp) hpq)
  have hN : {q | 0 ≤ height q} ⊆ N.source :=
    surgeryNorthChart_contains_hemisphere R e he hr1.le hRball
  have hf : InjOn f {q | 0 ≤ height q} := by
    intro x hx y hy hxy
    exact N.injOn (hN hx) (hN hy) (hcentral hxy)
  have hsigma0 : sigma ≠ 0 := by
    intro hz
    simp [hz] at hsigma
  have hg : Function.Injective g := surgeryCapMap_injective a b ha hb ha0 hb0
    hapos habound D.tube D.tube_source t sigma (k * (1 - r)) l hsigma0 hl.ne'
  have hjoin : sigma * (k * (1 - r)) ∈ Ioo (-D.width) D.width := by
    apply abs_lt.mp
    rw [abs_mul, hsigma, one_mul, abs_of_pos (mul_pos hk (sub_pos.mpr hr1))]
    exact hcwidth
  have heq (q : UnitTwoSphere) (hq : height q = 0) : f q = g q := by
    change ψ (surgeryNorthChart R e q, 0) =
      surgeryCapMap a b ha hb ha0 hb0 D.tube t sigma (k * (1 - r)) l q
    rw [surgeryNorthChart_equator_formula R e D.sourceCollar sigma k
      hr hr1 hrdelta hR hnear q hq,
      D.reconstruction _ _ hjoin, surgeryCapMap,
      surgeryCapCoordinates_cylinder a b ha hb ha0 hb0 hanear hbfar
        t sigma (k * (1 - r)) l q (by change |height q| ≤ 1 / 4; rw [hq]; norm_num)]
    change D.tube (_, t + sigma * (k * (1 - r))) =
      D.tube (_, t + sigma * (k * (1 - r) + l * height q))
    rw [hq, mul_zero, add_zero]
  apply levelPaste_injective height f g hf hg.injOn
  intro x hx y hy hxy
  have hNx : N x ∈ e '' closedBall 0 r := by
    rw [← surgeryNorthChart_image_hemisphere R e hRball]
    exact ⟨x, hx, rfl⟩
  have hretained : g y ∈ (fun p : UnitTwoSphere => ψ (p, 0)) ''
      (e '' closedBall 0 r) := ⟨N x, hNx, hxy⟩
  have hy0 : height y = 0 := (surgeryCapMap_mem_retained_iff a b ha hb ha0 hb0
    hapos habound hbpos hanear hbfar ψ hψ u t D e he sigma hsigma hr hr1 hrdelta hk
    hcwidth hnear hl hlM y hy (hM y)).mp hretained
  exact hf hx (show 0 ≤ height y by rw [hy0]) (hxy.trans (heq y hy0).symm)

end PoincareConjecture.M25.Topology3D
