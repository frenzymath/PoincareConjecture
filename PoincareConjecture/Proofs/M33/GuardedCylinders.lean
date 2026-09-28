import PoincareConjecture.Definitions.M33RegularHistory










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}

theorem SurgeryFlowCylinder.regular_image_of_earlier
    (e : SurgeryFlowCylinder F C a q J U) {s : ℝ} (hs : s ∈ J)
    (hearlier : ∃ s' ∈ J, s' < s) :
    e.forward s hs '' U ⊆ m33RegularRegion F (a + s / q) := by
  intro y hy hT
  let : Nonempty (F.slice (a + s / q)).carrier := ⟨y⟩
  exact e.retained_at_surgery s hs hT hearlier hy

theorem SurgeryFlowCylinder.regular_image_of_not_surgery
    (e : SurgeryFlowCylinder F C a q J U) {s : ℝ} (hs : s ∈ J)
    (hregular : a + s / q ∉ F.surgery_times) :
    e.forward s hs '' U ⊆ m33RegularRegion F (a + s / q) := by
  intro y _ hT
  exact (hregular hT).elim

theorem SurgeryFlowCylinder.regular_image_Ioc
    {l b : ℝ} (e : SurgeryFlowCylinder F C a q (Ioc l b) U)
    {s : ℝ} (hs : s ∈ Ioc l b) :
    e.forward s hs '' U ⊆ m33RegularRegion F (a + s / q) := by
  apply e.regular_image_of_earlier hs
  exact ⟨(l + s) / 2, ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩,
    by linarith [hs.1]⟩

theorem SurgeryFlowCylinder.regular_image_smaller_closed
    {r rho : ℝ} (hrho : 0 < rho) (hlt : rho < r)
    (e : SurgeryFlowCylinder F C a q (Icc (-r ^ 2) 0) U)
    {s : ℝ} (hs : s ∈ Icc (-rho ^ 2) 0) :
    ∃ hs' : s ∈ Icc (-r ^ 2) 0,
      e.forward s hs' '' U ⊆ m33RegularRegion F (a + s / q) := by
  have hsq : rho ^ 2 < r ^ 2 := by nlinarith
  have hs' : s ∈ Icc (-r ^ 2) 0 := ⟨by linarith [hs.1], hs.2⟩
  refine ⟨hs', e.regular_image_of_earlier hs' ?_⟩
  exact ⟨(-r ^ 2 + s) / 2, ⟨by linarith [hs.1], by nlinarith [hs.2]⟩,
    by linarith [hs.1]⟩



theorem SurgeryFlowCylinder.terminal_ball_regular {t r : ℝ}
    (x : (F.slice t).carrier) (hr : 0 < r)
    (e : SurgeryFlowCylinder F (F.slice t) t 1 (Icc (-r ^ 2) 0)
      ((F.metric t).ball x r))
    (hbase : ∀ h y, y ∈ (F.metric t).ball x r → HEq (e.forward 0 h y) y) :
    (F.metric t).ball x r ⊆ m33RegularRegion F t := by
  have hzero : (0 : ℝ) ∈ Icc (-r ^ 2) 0 := ⟨neg_nonpos.mpr (sq_nonneg r), le_rfl⟩
  have hreg := e.regular_image_of_earlier hzero
    ⟨-r ^ 2, ⟨le_rfl, neg_nonpos.mpr (sq_nonneg r)⟩,
      neg_lt_zero.mpr (sq_pos_of_pos hr)⟩
  intro y hy
  have he : (⟨t + 0 / 1, e.forward 0 hzero y⟩ : Σ s, (F.slice s).carrier) = ⟨t, y⟩ :=
    Sigma.ext (by simp) (hbase hzero y hy)
  exact (congrArg (fun p : Σ s, (F.slice s).carrier =>
    p.2 ∈ m33RegularRegion F p.1) he).mp (hreg ⟨y, hy, rfl⟩)

theorem M33RegularHistoryData.cylinder_from_surgery_of_earlier
    {W : M33RegularHistoryWindow F} (H : M33RegularHistoryData W)
    (hU : IsOpen U) (htime : ∀ s ∈ J, a + s / q ∈ H.generalized.interval)
    (e : SurgeryFlowCylinder F C a q J U)
    (hearlier : ∀ s ∈ J, ∃ s' ∈ J, s' < s) :
    ∃ d : GeneralizedFlowCylinder H.generalized C a q J U,
      (∀ s hs x, x ∈ U → H.history.forward (a + s / q) (htime s hs)
        (d.forward s hs x) = e.forward s hs x) ∧
      (∀ s hs x, x ∈ U → ∀ v w : TangentSpace (𝓡 3) x,
        d.pullbackInner s hs x v w = e.pullbackInner s hs x v w) :=
  H.cylinders_from_surgery C a q J U hU htime e
    (fun s hs => e.regular_image_of_earlier hs (hearlier s hs))

end PoincareConjecture
