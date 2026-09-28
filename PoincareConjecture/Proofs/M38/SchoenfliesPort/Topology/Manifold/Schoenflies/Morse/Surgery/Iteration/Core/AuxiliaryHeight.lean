import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Clock
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.Collars
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.CapHeight

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace SphereSurgeryCoreCap

variable {v : E3} {g : S2 → E3} {B : Set Real}

def heightCorrection (D : SphereSurgeryCoreCap v g B) (K : Real) (p : S2) : Real := by
  classical
  exact if p ∈ D.chart '' ball 0 1 then
    capPhysicalClock D.center D.scale K (inner Real v (g p)) - inner Real v (g p)
  else 0

theorem heightCorrection_eventuallyEq_zero (D : SphereSurgeryCoreCap v g B)
    (hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g) (K : Real)
    {p : S2} (hp : p ∉ D.chart '' ball 0 1) :
    D.heightCorrection K =ᶠ[𝓝 p] 0 := by
  classical
  by_cases hpclosed : p ∈ D.chart '' closedBall 0 1
  · have hpboundary : p ∈ D.chart '' sphere 0 1 :=
      D.closed_disk_diff_open_disk ▸ ⟨hpclosed, hp⟩
    have hheight := D.height_eq_on_boundary p hpboundary
    have hnorm : Continuous (fun q : S2 => (inner Real v (g q) - D.center) / D.scale) :=
      (((innerSL Real v).continuous.comp hg.continuous).sub continuous_const).div_const _
    have hnear : ∀ᶠ q in 𝓝 p, (inner Real v (g q) - D.center) / D.scale < 1 / 4 :=
      hnorm.continuousAt.eventually_lt_const (by
        change (inner Real v (g p) - D.center) / D.scale < 1 / 4
        rw [hheight]
        norm_num)
    filter_upwards [hnear] with q hq
    by_cases hqD : q ∈ D.chart '' ball 0 1
    · simp only [heightCorrection, if_pos hqD,
        capPhysicalClock_eq_self _ _ _ D.scale_ne_zero hq.le, sub_self, Pi.zero_apply]
    · simp only [heightCorrection, if_neg hqD, Pi.zero_apply]
  · have hclosed : IsClosed (D.chart '' closedBall 0 1) :=
      ((isCompact_closedBall 0 1).image_of_continuousOn
        (D.chart.continuousOn.mono D.source)).isClosed
    filter_upwards [hclosed.isOpen_compl.mem_nhds hpclosed] with q hq
    have hqD : q ∉ D.chart '' ball 0 1 := fun h => hq (image_mono ball_subset_closedBall h)
    simp only [heightCorrection, if_neg hqD, Pi.zero_apply]

theorem contMDiff_heightCorrection (D : SphereSurgeryCoreCap v g B)
    (hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g) (K : Real) :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (D.heightCorrection K) := by
  classical
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p => inner Real v (g p)) :=
    (innerSL Real v).contMDiff.comp hg
  intro p
  by_cases hp : p ∈ D.chart '' ball 0 1
  · have hopen := D.chart.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans D.source)
    have hlocal := (((contDiff_capPhysicalClock D.center D.scale K).contMDiff.comp hh).sub hh) p
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hp] with q hq
    simp only [heightCorrection, if_pos hq, Function.comp_apply]
  · exact contMDiffAt_const.congr_of_eventuallyEq (D.heightCorrection_eventuallyEq_zero hg K hp)

private instance : Std.Symm (fun (D E : SphereSurgeryCoreCap v g B) =>
    Disjoint (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) where
  symm _ _ h := h.symm

def adjustedHeight (L : List (SphereSurgeryCoreCap v g B))
    (K : SphereSurgeryCoreCap v g B → Real) (p : S2) : Real := by
  classical
  exact inner Real v (g p) + ∑ D ∈ L.toFinset, D.heightCorrection (K D) p

theorem contMDiff_adjustedHeight (L : List (SphereSurgeryCoreCap v g B))
    (hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g) (K : SphereSurgeryCoreCap v g B → Real) :
    ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (adjustedHeight L K) := by
  classical
  exact ((innerSL Real v).contMDiff.comp hg).add
    (contMDiff_finsetSum (fun D _ => D.contMDiff_heightCorrection hg (K D)))

theorem adjustedHeight_eventuallyEq_on_core
    (L : List (SphereSurgeryCoreCap v g B))
    (hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g) (K : SphereSurgeryCoreCap v g B → Real)
    {C : Set S2} (hC : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    {p : S2} (hp : p ∈ C) :
    adjustedHeight L K =ᶠ[𝓝 p] (fun q => inner Real v (g q)) := by
  classical
  have hnear : ∀ᶠ q in 𝓝 p, ∀ D ∈ L.toFinset, D.heightCorrection (K D) q = 0 := by
    apply (L.toFinset.eventually_all).mpr
    intro D hD
    apply D.heightCorrection_eventuallyEq_zero hg (K D)
    intro hpD
    rw [hC] at hp
    exact hp (mem_iUnion_of_mem D (mem_iUnion_of_mem (List.mem_toFinset.mp hD) hpD))
  filter_upwards [hnear] with q hq
  simp only [adjustedHeight, Finset.sum_eq_zero hq, add_zero]

theorem adjustedHeight_eventuallyEq_on_cap
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hg : ContMDiff (𝓡 2) (𝓡 3) ∞ g) (K : SphereSurgeryCoreCap v g B → Real)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L)
    {p : S2} (hp : p ∈ D.chart '' ball 0 1) :
    adjustedHeight L K =ᶠ[𝓝 p]
      (fun q => capPhysicalClock D.center D.scale (K D) (inner Real v (g q))) := by
  classical
  have hopen := D.chart.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans D.source)
  have hnear : ∀ᶠ q in 𝓝 p, ∀ E ∈ L.toFinset, E ≠ D → E.heightCorrection (K E) q = 0 := by
    apply (L.toFinset.eventually_all).mpr
    intro E hE
    by_cases heq : E = D
    · exact Filter.Eventually.of_forall (fun _ h => (h heq).elim)
    · have hpE : p ∉ E.chart '' ball 0 1 := fun hpE =>
        Set.disjoint_left.mp (hpair.forall hD (List.mem_toFinset.mp hE) (Ne.symm heq))
          (image_mono ball_subset_closedBall hp) (image_mono ball_subset_closedBall hpE)
      exact (E.heightCorrection_eventuallyEq_zero hg (K E) hpE).mono (fun _ h _ => h)
  filter_upwards [hnear, hopen.mem_nhds hp] with q hq hqD
  have hsum : ∑ E ∈ L.toFinset, E.heightCorrection (K E) q = D.heightCorrection (K D) q := by
    apply Finset.sum_eq_single D
    · exact fun E hE hED => hq E hE hED
    · exact fun h => (h (List.mem_toFinset.mpr hD)).elim
  change inner Real v (g q) + ∑ E ∈ L.toFinset, E.heightCorrection (K E) q = _
  rw [hsum, heightCorrection, if_pos hqD]
  ring

private theorem regular_of_normalized_height
    (D : SphereSurgeryCoreCap v g B)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {p : S2} (hp : p ∈ D.chart '' closedBall 0 1)
    (hpos : 0 < (inner Real v (g p) - D.center) / D.scale)
    (hlt : (inner Real v (g p) - D.center) / D.scale < 1) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0 := by
  apply D.regular_on_open_cylindrical_belt hg hp
  have heq : inner Real v (g p) - (D.center + D.scale / 2) =
      D.scale * ((inner Real v (g p) - D.center) / D.scale - 1 / 2) := by
    field_simp [D.scale_ne_zero]
    ring
  rw [heq, abs_mul]
  have habs : |(inner Real v (g p) - D.center) / D.scale - 1 / 2| < 1 / 2 :=
    abs_lt.mpr ⟨by linarith, by linarith⟩
  nlinarith [mul_lt_mul_of_pos_left habs (abs_pos.mpr D.scale_ne_zero)]

private theorem regular_comp_scalar {h : S2 → Real}
    (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    {φ : Real → Real} (hφ : ContDiff Real ∞ φ) {p : S2}
    (hder : deriv φ (h p) ≠ 0)
    (hreg : mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (φ ∘ h) p ≠ 0 := by
  rw [mfderiv_comp p (hφ.contMDiff.mdifferentiable (by simp) (h p))
    (hh.mdifferentiable (by simp) p), mfderiv_eq_fderiv]
  intro hzero
  apply hreg
  ext w
  have hw := congrArg (fun L => L w) hzero
  change (fderiv Real φ (h p)) ((mfderiv (𝓡 2) 𝓘(Real, Real) h p) w) = 0 at hw
  rw [fderiv_eq_deriv_mul] at hw
  exact (mul_eq_zero.mp hw).resolve_left hder

theorem exists_auxiliary_height_preserving_core_critical_points
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {C : Set S2} (hC : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (a b : Real) :
    ∃ h : S2 → Real,
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h ∧
      (∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) ∧
      (∀ p, h p ∈ Icc a b →
        (mfderiv (𝓡 2) 𝓘(Real, Real) h p = 0 ↔ p ∈ C ∧
          mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p = 0)) ∧
      (∀ D ∈ L, ∀ p ∈ D.chart '' ball 0 1,
        (inner Real v (g p) - D.center) / D.scale < 1 / 4 →
          h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) := by
  classical
  choose K hK havoid using fun D : SphereSurgeryCoreCap v g B =>
    exists_cap_clock_avoiding_band a b D.center D.scale_ne_zero
  let h := adjustedHeight L K
  have hh := contMDiff_adjustedHeight L hg.contMDiff K
  have hcore : ∀ {p : S2}, p ∈ C → h =ᶠ[𝓝 p] (fun q => inner Real v (g q)) :=
    fun hp => adjustedHeight_eventuallyEq_on_core L hg.contMDiff K hC hp
  have hheight : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p => inner Real v (g p)) :=
    (innerSL Real v).contMDiff.comp hg.contMDiff
  refine ⟨h, hh, fun p hp => hcore hp, ?_, ?_⟩
  · intro p hp
    by_cases hpC : p ∈ C
    · rw [(hcore hpC).mfderiv_eq]
      simp only [hpC, true_and]
    · have hpcap : p ∈ ⋃ D ∈ L, D.chart '' ball 0 1 := by
        simpa only [hC, mem_compl_iff, not_not] using hpC
      obtain ⟨D, hD, hpD⟩ := mem_iUnion₂.mp hpcap
      have heq := adjustedHeight_eventuallyEq_on_cap L hpair hg.contMDiff K D hD hpD
      have htpos := D.normalized_height_pos_on_open_disk hpD
      have htlt : (inner Real v (g p) - D.center) / D.scale < 1 / 2 := by
        by_contra! hge
        apply havoid D _ hge
        have hnormalize : D.center + D.scale *
            ((inner Real v (g p) - D.center) / D.scale) = inner Real v (g p) := by
          field_simp [D.scale_ne_zero]
          ring
        rw [hnormalize, ← heq.eq_of_nhds]
        exact hp
      simp only [hpC, false_and, iff_false]
      rw [heq.mfderiv_eq]
      exact regular_comp_scalar hheight (contDiff_capPhysicalClock _ _ _)
        (deriv_capPhysicalClock_pos D.center D.scale_ne_zero (hK D) _).ne'
        (regular_of_normalized_height D hg (image_mono ball_subset_closedBall hpD)
          htpos (by linarith))
  · intro D hD p hpD hpt
    have heq := adjustedHeight_eventuallyEq_on_cap L hpair hg.contMDiff K D hD hpD
    have hnorm : Continuous (fun q : S2 => (inner Real v (g q) - D.center) / D.scale) :=
      (hheight.continuous.sub continuous_const).div_const _
    have hnear := hnorm.continuousAt.eventually_lt_const hpt
    filter_upwards [heq, hnear] with q hq hqt
    exact hq.trans (capPhysicalClock_eq_self _ _ _ D.scale_ne_zero hqt.le)

theorem exists_regular_auxiliary_height
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {C : Set S2} (hC : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (a b : Real)
    (hregular : ∀ p ∈ C,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) p ≠ 0) :
    ∃ h : S2 → Real,
      ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h ∧
      (∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) ∧
      (∀ p, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0) ∧
      (∀ D ∈ L, ∀ p ∈ D.chart '' ball 0 1,
        (inner Real v (g p) - D.center) / D.scale < 1 / 4 →
          h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) := by
  obtain ⟨h, hh, hcore, hcrit, hlow⟩ :=
    exists_auxiliary_height_preserving_core_critical_points L hpair hg hC a b
  refine ⟨h, hh, hcore, ?_, hlow⟩
  intro p hp hc
  obtain ⟨hpC, hpc⟩ := (hcrit p hp).mp hc
  exact hregular p hpC hpc

end SphereSurgeryCoreCap

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
