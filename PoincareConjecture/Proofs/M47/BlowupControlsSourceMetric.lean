import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderMetric
import PoincareConjecture.Proofs.M47.SeedImageBalls
import PoincareConjecture.Proofs.M04.ShiCarrier
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderMetricComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.M47

open Proofs.M46



theorem normalized_search_metric_comparison
    (P : M44CapPersistencePredecessors.{u}) {F : SurgeryFlowData.{u}}
    (hpinch : SurgeryFlowPinched F) {base Q a K : ℝ}
    {U : Set (F.slice base).carrier}
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0) U)
    (hU : IsOpen U) (ha : a ≤ 0) (hK : 0 ≤ K)
    (hbased : ∀ hs y, y ∈ U → HEq (e.forward 0 hs y) y)
    (hRm : ∀ s (hs : s ∈ Icc a 0), ∀ y ∈ U,
      (F.connection (base + s / Q)).curvatureTensorNorm (e.forward s hs y) ≤ K * Q)
    (hshort : 6 * K * (-a) ≤ 1 / 2) :
    ∀ s (hs : s ∈ Icc a 0), ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      (F.metric base).inner x v v ≤
        2 * (F.metric (base + s / Q)).inner (e.forward s hs x)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) ∧
      (F.metric (base + s / Q)).inner (e.forward s hs x)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) ≤
        2 * (F.metric base).inner x v v := by
  classical
  have hQ := e.scale_pos
  have hmem : MapsTo (fun z : ℝ => Q * z) (Icc (a / Q) 0) (Icc a 0) := by
    intro z hz
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ hQ).mp hz.1,
      mul_nonpos_of_nonneg_of_nonpos hQ.le hz.2⟩
  have hmono : StrictMonoOn (fun z : ℝ => Q * z) (Icc (a / Q) 0) :=
    fun _ _ _ _ h => mul_lt_mul_of_pos_left h hQ
  have hclock (z : ℝ) (_hz : z ∈ Icc (a / Q) 0) :
      base + z / 1 = base + (Q * z) / Q := by
    rw [div_one, mul_div_cancel_left₀ z hQ.ne']
  let f : SurgeryFlowCylinder F (F.slice base) base 1 (Icc (a / Q) 0) U :=
    Proofs.M47.seedCylinderReclock e (by norm_num) ordConnected_Icc
      (fun z => Q * z) hmem hmono hclock
  have hfbase : ∀ hs y, y ∈ U → HEq (f.forward 0 hs y) y := by
    intro hs y hy
    have he := Proofs.M47.seedCylinderReclock_forward_heq e
      (by norm_num) ordConnected_Icc (fun z => Q * z) hmem hmono hclock 0 hs y
    have hzbase (z : ℝ) (hz : z ∈ Icc a 0) (hzero : z = 0) :
        HEq (e.forward z hz y) y := by
      subst z
      exact hbased ⟨ha, le_rfl⟩ y hy
    exact he.trans (hzbase _ _ (mul_zero Q))
  have hfRm (z : ℝ) (hz : z ∈ Icc (a / Q) 0) (x : (F.slice base).carrier)
      (hx : x ∈ U) :
      (F.connection (base + z / 1)).curvatureTensorNorm (f.forward z hz x) ≤ K * Q := by
    exact Proofs.M47.seedCylinderReclock_curvature e (by norm_num) ordConnected_Icc
      (fun z => Q * z) hmem hmono hclock hRm z hz x hx
  intro s hs x hx v
  have hsQ : s / Q ∈ Icc (a / Q) 0 :=
    ⟨div_le_div_of_nonneg_right hs.1 hQ.le, div_nonpos_of_nonpos_of_nonneg hs.2 hQ.le⟩
  have hcancel : Q * (s / Q) = s := mul_div_cancel₀ s hQ.ne'
  let value (z : ℝ) : ℝ := if hz : z ∈ Icc a 0 then e.pullbackInner z hz x v v else 0
  have hread (z : ℝ) (hz : z ∈ Icc (a / Q) 0) :
      cylinderQuadratic f x v z = Q⁻¹ * value (Q * z) := by
    simp only [cylinderQuadratic, dif_pos hz, value, dif_pos (hmem hz)]
    simpa only [one_div] using Proofs.M47.neck_reclock_pullbackInner e
      (by norm_num) ordConnected_Icc (fun z => Q * z) hmem hmono hclock z hz x v v
  have hshort' : 6 * (K * Q) * (-(s / Q)) ≤ 1 / 2 := by
    have htime := (mul_le_mul_of_nonneg_left (neg_le_neg hs.1)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hK)).trans hshort
    have heq : 6 * (K * Q) * (-(s / Q)) = 6 * K * (-s) := by
      field_simp [hQ.ne']
    rw [heq]
    exact htime
  have hmetric : (F.metric base).inner x v v ≤ 2 * cylinderQuadratic f x v (s / Q) ∧
      cylinderQuadratic f x v (s / Q) ≤ 2 * (F.metric base).inner x v v := by
    simpa only [cylinderQuadratic_of_mem f x v (s / Q) hsQ] using
      based_cylinder_metric_comparison_two P hpinch f hU hfbase hx v hsQ hshort'
        (fun z hz => hfRm z hz x hx)
  rw [hread _ hsQ, hcancel] at hmetric
  simpa only [value, dif_pos hs, SurgeryFlowCylinder.pullbackInner,
    ← mul_assoc, inv_mul_cancel₀ hQ.ne', one_mul] using hmetric



theorem normalized_search_image_ball_subset
    {F : SurgeryFlowData.{u}} {base Q a radius : ℝ} (p : (F.slice base).carrier)
    (e : SurgeryFlowCylinder F (F.slice base) base Q (Icc a 0)
      ((F.metric base).ball p radius))
    (s : ℝ) (hs : s ∈ Icc a 0)
    (hmetric : ∀ x ∈ (F.metric base).ball p radius, ∀ v : TangentSpace (𝓡 3) x,
      (F.metric (base + s / Q)).inner (e.forward s hs x)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
          (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) ≤
        2 * (F.metric base).inner x v v) :
    e.forward s hs '' (F.metric base).ball p radius ⊆
      (F.metric (base + s / Q)).ball (e.forward s hs p) (2 * radius) := by
  let chart := M44.cylinderSliceChart e (M04.initial_ball_isOpen _ _ _) s hs
  apply Proofs.M47.seed_image_ball_subset (F.metric base) (F.metric (base + s / Q))
    chart (p := p) (hsource := Subset.refl _)
  intro x hx v
  change (F.metric (base + s / Q)).inner (e.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) ≤
    4 * (F.metric base).inner x v v
  have hn : 0 ≤ (F.metric base).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((F.metric base).pos x v hv).le
  linarith only [hmetric x hx v, hn]

end PoincareConjecture.M47
