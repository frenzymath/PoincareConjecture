import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.FamilyCellComparison
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.FamilyGoodGridAssembly
import PoincareConjecture.Proofs.M65.Sec19_5_GoodTimes.FamilyProfileTolerance
import Mathlib.Data.Finset.Max











set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff Manifold Bundle BigOperators

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}

set_option maxHeartbeats 1600000 in






theorem m65Family_pointwise_terminal_alternative
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u})
    (compact : IsCompact (univ : Set M)) (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta)
    (E : M64AppliedFamilyEstimates V.flow.geometry C)
    (comparison : M65ImmersedFillingAreaComparison F) (hab : a < b)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ T : ℝ, a ≤ T ∧ T < b ∧
      Real.exp (V.flow.geometry.K2 * (b - T)) < 4 / 3 ∧
      ∀ z : LoopTwoSphere, ∃ cutoff : ℝ, 0 < cutoff ∧
        ∀ circumference (h : 0 < circumference), circumference < 1 → circumference < cutoff →
          fillingArea (F.metric b)
              ((C.solutions circumference h).projected ⟨b, hab.le, le_rfl⟩ z) ≤
            areaComparisonProfile F (fillingArea (F.metric a) (C.approximation.family z)) b +
              eta / 2 ∨
            ∀ t ∈ Icc T b, m62Length (V.flow.geometry.product circumference h).flow
              ((C.solutions circumference h).curve z) t < eta / 2 := by
  classical
  obtain ⟨delta, hdelta, hprofile⟩ :=
    m65FamilyProfileTolerance hM61 hM64 compact V C hab (half_pos heta)
  obtain ⟨B, _hB1, T, hT, hgrowth, r, _hr, _hr1, _hrfloor, _hscale,
    hwindow, n, step, hstep, hend, hwidth, hgrid⟩ :=
    m65Family_exists_fixed_good_grid C E hab hdelta (half_pos heta)
  obtain ⟨error, herror, hcompare⟩ := hprofile (n + 3)
  let floor := (eta / 2) * Real.exp (-V.flow.geometry.K2 * (b - a))
  have hfloor0 : 0 < floor := mul_pos (half_pos heta) (Real.exp_pos _)
  let jets (i : ℕ) := C.derivative_estimates.constant i / (step / 2) ^ (i + 1)
  have hjets0 (i : ℕ) : 0 ≤ jets i :=
    div_nonneg (C.derivative_estimates.constant_nonnegative i) (by positivity)
  have hcell (j : Fin n) :
      Icc (a + (j : ℝ) * step + 3 * step / 2)
        (a + (j : ℝ) * step + 7 * step / 2) ⊆ Ioo a b := by
    have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    have hjmul := mul_le_mul_of_nonneg_right hj hstep.le
    have hj0 : 0 ≤ (j : ℝ) * step := mul_nonneg (Nat.cast_nonneg _) hstep.le
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hstart (j : Fin n) : a + (j : ℝ) * step + 3 * step / 2 ∈ Icc a T := by
    have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    have hjmul := mul_le_mul_of_nonneg_right hj hstep.le
    have hj0 : 0 ≤ (j : ℝ) * step := mul_nonneg (Nat.cast_nonneg _) hstep.le
    constructor <;> linarith
  let time (i : ℕ) : Icc a b := ⟨M65.delayedGridTime a b step n i,
    M65.delayedGridTime_mem hstep.le (hend ▸ hT.2.le) i⟩
  refine ⟨T, hT.1.le, hT.2, hgrowth, ?_⟩
  intro z
  have hcut (j : Fin n) := m65FamilyCell_exists_comparison_cutoff hM64 compact V C comparison z
    (r := a + (j : ℝ) * step + 3 * step / 2)
    (s := a + (j : ℝ) * step + 7 * step / 2)
    (by linarith) (hcell j) hfloor0 jets hjets0
    (u := a + ((j : ℝ) + 2) * step) (v := a + ((j : ℝ) + 3) * step)
    (by linarith) (by intro t ht; constructor <;> linarith [ht.1, ht.2]) herror
  choose cutoff hpositive hnode using hcut
  let bounds : Finset ℝ := insert 1 (Finset.univ.image cutoff)
  have hne : bounds.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hpos : ∀ x ∈ bounds, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_lt_one
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact hpositive j
  refine ⟨bounds.min' hne, hpos _ (Finset.min'_mem _ _), ?_⟩
  intro circumference h hlt hsmall
  have hsmaller (j : Fin n) : circumference < cutoff j :=
    hsmall.trans_le (Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)))
  rcases hgrid circumference h hlt z with hshort | ⟨hlower, good, hgood, href, hgap⟩
  · exact Or.inr hshort
  apply Or.inl
  have hgoodCompare (i : ℕ) (_hi : i < n + 3) (hi : i ∈ good.image (fun j => j + 2)) :
      fillingArea (F.metric (time (i + 1)))
          ((C.solutions circumference h).projected (time (i + 1)) z) ≤
        m65RestartedAreaProfile F (time i)
          (fillingArea (F.metric (time i))
            ((C.solutions circumference h).projected (time i) z)) (time (i + 1)) + error := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have hjn : j < n := Finset.mem_range.mp (hgood hj)
    let jn : Fin n := ⟨j, hjn⟩
    obtain ⟨_sref, _href, _hsT, _hlen, _henergy, _hjordinary, _hcell, hj⟩ := href j hj
    have hbound := hnode jn circumference h hlt (hsmaller jn)
      (hlower _ (hstart jn)) hj
    have hj0 : j + 2 ≤ n + 2 := by omega
    have hj1 : j + 2 + 1 ≤ n + 2 := by omega
    have hc0 : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by norm_num
    have hc1 : ((j + 2 + 1 : ℕ) : ℝ) = (j : ℝ) + 3 := by push_cast; ring
    simpa only [time, M65.delayedGridTime, if_pos hj0, if_pos hj1, hc0, hc1] using hbound
  have hfinal := hcompare circumference h hlt z time (good.image (fun j => j + 2))
    (M65.delayedGridTime_endpoints a b step n).1
    (M65.delayedGridTime_endpoints a b step n).2
    (fun i hi => M65.delayedGridTime_ordered hstep.le (hend ▸ hT.2.le) hi)
    hgoodCompare hgap.le
  have hinitial := (C.solutions circumference h).projected_initial ⟨le_rfl, hab.le⟩
  rw [hinitial] at hfinal
  exact hfinal.le

end PoincareConjecture
