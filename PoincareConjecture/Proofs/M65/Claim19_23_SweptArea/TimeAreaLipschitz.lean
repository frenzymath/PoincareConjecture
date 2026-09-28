import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.FlowFillingScaling
import PoincareConjecture.Proofs.M65.Mathlib.ExpIncrement








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ} {F : RicciFlow 3 M (Icc a b)}
  {Gamma : ContinuousMap LoopTwoSphere (C1FreeLoopSpace (M := M))} {zeta : ℝ}




theorem m65UniformTimeFillingBounds (hM61 : M61RawWidthCore.{u})
    (hM64 : M64ComparisonTheory.{u}) (compact : IsCompact (univ : Set M))
    (V : M64ThreeDimensionalFlowConclusion F)
    (C : M63FamilyConclusion V.flow.geometry Gamma zeta) (hab : a < b) :
    ∃ Amax : ℝ, 0 < Amax ∧ ∃ L : ℝ, 0 < L ∧
      ∀ circumference (h : 0 < circumference), circumference < 1 → ∀ z : LoopTwoSphere,
        (∀ t : Icc a b,
          0 ≤ fillingArea (F.metric t) ((C.solutions circumference h).projected t z) ∧
          fillingArea (F.metric t) ((C.solutions circumference h).projected t z) ≤ Amax) ∧
        (∀ s t : Icc a b,
          |fillingArea (F.metric t) ((C.solutions circumference h).projected t z) -
            fillingArea (F.metric s) ((C.solutions circumference h).projected s z)| ≤
              L * |(t : ℝ) - s|) := by
  let K := V.flow.geometry.K2
  have hK : 0 ≤ K := V.flow.geometry.nonnegative.2.2
  let E := Real.exp ((2 * K) * (b - a))
  let T := E * m65FamilyTotalCurvatureBound C
  have hE : 0 < E := Real.exp_pos _
  have hT : 0 < T := mul_pos hE (m65FamilyTotalCurvatureBound_pos C)
  let W := m61FamilyWidth (F.metric a) C.approximation.family
  have hW := hM61.family (F.metric a) compact C.approximation.family C.approximation.null_family
  have hmember (z : LoopTwoSphere) :
      fillingArea (F.metric a) (C.approximation.family z) ≤ W :=
    le_csSup hW.bounded_above ⟨z, rfl⟩
  let area : ∀ circumference : ℝ, 0 < circumference → LoopTwoSphere → Icc a b → ℝ :=
    fun circumference h z t =>
      fillingArea (F.metric t) ((C.solutions circumference h).projected t z)
  have htime (s t : Icc a b) : |(t : ℝ) - s| ≤ b - a := by
    apply abs_le.mpr
    constructor <;> linarith [s.2.1, s.2.2, t.2.1, t.2.2]
  have hnonneg (circumference : ℝ) (h : 0 < circumference) (z : LoopTwoSphere) (t : Icc a b) :
      0 ≤ area circumference h z t := by
    obtain ⟨D⟩ := m65ProjectedDisk_nonempty hM64 compact (C.solutions circumference h) t z
    exact m60FillingArea_nonneg_of_disk _ _ D
  have huniform (circumference : ℝ) (h : 0 < circumference) (hlt : circumference < 1)
      (z : LoopTwoSphere) (t : Icc a b) : area circumference h z t ≤ E * W + T * (b - a) := by
    have ht := m65VaryingMetricFillingArea_le hM61 hM64 compact V C hab h hlt z
      ⟨a, le_rfl, hab.le⟩ t
    rw [(C.solutions circumference h).projected_initial ⟨le_rfl, hab.le⟩] at ht
    change area circumference h z t ≤ Real.exp ((2 * K) * |(t : ℝ) - a|) *
      fillingArea (F.metric a) (C.approximation.family z) + T * |(t : ℝ) - a| at ht
    rw [abs_of_nonneg (sub_nonneg.mpr t.2.1)] at ht
    have hexp : Real.exp ((2 * K) * ((t : ℝ) - a)) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right t.2.2 a)
        (mul_nonneg (by norm_num) hK))
    have hmul : Real.exp ((2 * K) * ((t : ℝ) - a)) *
        fillingArea (F.metric a) (C.approximation.family z) ≤ E * W :=
      (mul_le_mul_of_nonneg_left (hmember z) (Real.exp_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hexp hW.nonnegative)
    exact ht.trans (add_le_add hmul
      (mul_le_mul_of_nonneg_left (sub_le_sub_right t.2.2 a) hT.le))
  let Amax := |E * W + T * (b - a)| + 1
  have hAmax : 0 < Amax := by dsimp [Amax]; positivity
  have hupper (circumference : ℝ) (h : 0 < circumference) (hlt : circumference < 1)
      (z : LoopTwoSphere) (t : Icc a b) : area circumference h z t ≤ Amax :=
    (huniform circumference h hlt z t).trans
      ((le_abs_self _).trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
  let L := (2 * K) * E * Amax + T
  have hL : 0 < L := by dsimp [L]; positivity
  have hforward (circumference : ℝ) (h : 0 < circumference) (hlt : circumference < 1)
      (z : LoopTwoSphere) (s t : Icc a b) :
      area circumference h z t - area circumference h z s ≤ L * |(t : ℝ) - s| := by
    have ht := m65VaryingMetricFillingArea_le hM61 hM64 compact V C hab h hlt z s t
    change area circumference h z t ≤ Real.exp ((2 * K) * |(t : ℝ) - s|) *
      area circumference h z s + T * |(t : ℝ) - s| at ht
    have hx : 0 ≤ (2 * K) * |(t : ℝ) - s| := mul_nonneg (mul_nonneg (by norm_num) hK) (abs_nonneg _)
    have hincr := Real.exp_sub_one_le_mul_exp hx
      (mul_le_mul_of_nonneg_left (htime s t) (mul_nonneg (by norm_num) hK))
    change Real.exp ((2 * K) * |(t : ℝ) - s|) - 1 ≤ (2 * K) * |(t : ℝ) - s| * E at hincr
    have hmul := (mul_le_mul_of_nonneg_right hincr (hnonneg circumference h z s)).trans
      (mul_le_mul_of_nonneg_left (hupper circumference h hlt z s) (mul_nonneg hx hE.le))
    calc
      _ ≤ (Real.exp ((2 * K) * |(t : ℝ) - s|) - 1) * area circumference h z s +
          T * |(t : ℝ) - s| := by linarith
      _ ≤ ((2 * K) * |(t : ℝ) - s| * E) * Amax + T * |(t : ℝ) - s| :=
        add_le_add hmul le_rfl
      _ = L * |(t : ℝ) - s| := by dsimp [L]; ring
  refine ⟨Amax, hAmax, L, hL, ?_⟩
  intro circumference h hlt z
  refine ⟨fun t => ⟨hnonneg circumference h z t, hupper circumference h hlt z t⟩, ?_⟩
  intro s t
  apply abs_le.mpr
  constructor
  · have hreverse := hforward circumference h hlt z t s
    rw [abs_sub_comm] at hreverse
    change -(L * |(t : ℝ) - s|) ≤ area circumference h z t - area circumference h z s
    linarith
  · exact hforward circumference h hlt z s t

end PoincareConjecture
