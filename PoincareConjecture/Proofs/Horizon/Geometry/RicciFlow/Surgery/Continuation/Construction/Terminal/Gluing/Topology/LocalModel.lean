import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Topology.Polar
import Mathlib.Topology.Piecewise

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

def capNeckCoordinates (_R : MetricSurgeryResult g₀ I)
    (q : UnitTwoSphere × Ico (0 : ℝ) 1) : NeckDomain I.neck.epsilon :=
  (q.1, ⟨I.neck.epsilon⁻¹ * q.2.val, by
    have he := inv_pos.mpr I.neck.epsilon_pos
    constructor
    · exact (neg_lt_zero.mpr he).trans_le (mul_nonneg he.le q.2.property.1)
    · simpa only [mul_one] using mul_lt_mul_of_pos_left q.2.property.2 he⟩)

def neckCapCoordinates (_R : MetricSurgeryResult g₀ I)
    (z : NeckDomain I.neck.epsilon) (hz : 0 ≤ z.2.val) :
    UnitTwoSphere × Ico (0 : ℝ) 1 :=
  (z.1, ⟨I.neck.epsilon * z.2.val, mul_nonneg I.neck.epsilon_pos.le hz, by
    simpa only [mul_inv_cancel₀ I.neck.epsilon_pos.ne'] using
      mul_lt_mul_of_pos_left z.2.property.2 I.neck.epsilon_pos⟩)

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
theorem capNeckCoordinates_continuous : Continuous R.capNeckCoordinates := by
  apply Continuous.prodMk continuous_fst
  exact (continuous_const.mul (continuous_subtype_val.comp continuous_snd)).subtype_mk _

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
@[simp] theorem neckCapCoordinates_capNeckCoordinates (q : UnitTwoSphere × Ico (0 : ℝ) 1) :
    R.neckCapCoordinates (R.capNeckCoordinates q)
      (mul_nonneg (inv_nonneg.mpr I.neck.epsilon_pos.le) q.2.property.1) = q := by
  refine Prod.ext ?_ ?_
  · rfl
  apply Subtype.ext
  change I.neck.epsilon * (I.neck.epsilon⁻¹ * q.2.val) = q.2.val
  rw [← mul_assoc, mul_inv_cancel₀ I.neck.epsilon_pos.ne', one_mul]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] in
@[simp] theorem capNeckCoordinates_neckCapCoordinates
    (z : NeckDomain I.neck.epsilon) (hz : 0 ≤ z.2.val) :
    R.capNeckCoordinates (R.neckCapCoordinates z hz) = z := by
  refine Prod.ext ?_ ?_
  · rfl
  apply Subtype.ext
  change I.neck.epsilon⁻¹ * (I.neck.epsilon * z.2.val) = z.2.val
  rw [← mul_assoc, inv_mul_cancel₀ I.neck.epsilon_pos.ne', one_mul]

def neckFill (z : NeckDomain I.neck.epsilon) : R.output.carrier :=
  if hz : z.2.val < 0 then R.collapse (I.neck.coordinate z)
  else (R.puncturedClosedCapPolar.symm (R.neckCapCoordinates z (le_of_not_gt hz))).val.val

theorem neckFill_of_negative (z : NeckDomain I.neck.epsilon) (hz : z.2.val < 0) :
    R.neckFill z = R.collapse (I.neck.coordinate z) := dif_pos hz

theorem neckFill_of_nonnegative (z : NeckDomain I.neck.epsilon) (hz : 0 ≤ z.2.val) :
    R.neckFill z = (R.puncturedClosedCapPolar.symm (R.neckCapCoordinates z hz)).val.val :=
  dif_neg (not_lt.mpr hz)

theorem neckFill_of_zero (z : NeckDomain I.neck.epsilon) (hz : z.2.val = 0) :
    R.neckFill z = R.collapse (I.neck.coordinate z) := by
  rw [R.neckFill_of_nonnegative z hz.ge]
  have hcoord : R.neckCapCoordinates z hz.ge = (z.1, ⟨0, by constructor <;> norm_num⟩) := by
    refine Prod.ext ?_ ?_
    · rfl
    apply Subtype.ext
    change I.neck.epsilon * z.2.val = 0
    rw [hz, mul_zero]
  rw [hcoord, R.puncturedClosedCapPolar_symm_zero, I.neck.coordinate_map_eq]
  rw [hz]

theorem neckFill_of_nonpositive (z : NeckDomain I.neck.epsilon) (hz : z.2.val ≤ 0) :
    R.neckFill z = R.collapse (I.neck.coordinate z) := by
  rcases hz.eq_or_lt with hz | hz
  · exact R.neckFill_of_zero z hz
  · exact R.neckFill_of_negative z hz

theorem neckFill_ne_tip (z : NeckDomain I.neck.epsilon) : R.neckFill z ≠ R.tip := by
  by_cases hz : z.2.val < 0
  · rw [R.neckFill_of_negative z hz]
    apply R.collapse_negative_ne_tip
    change (I.neck.coordinate z).val ∈ I.neck.region (-I.neck.epsilon⁻¹) 0
    exact ⟨(I.neck.coordinate z).property, by
      rw [I.neck.coordinate_inverse_left]
      exact ⟨z.2.property.1, hz⟩⟩
  · rw [R.neckFill_of_nonnegative z (le_of_not_gt hz)]
    exact (R.puncturedClosedCapPolar.symm _).property

theorem neckFill_continuous : Continuous R.neckFill := by
  let A : Set (NeckDomain I.neck.epsilon) := {z | z.2.val ≤ 0}
  let B : Set (NeckDomain I.neck.epsilon) := {z | 0 ≤ z.2.val}
  have hA : IsClosed A := isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const
  have hB : IsClosed B := isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)
  have hneg : ContinuousOn R.neckFill A := by
    apply (R.collapse_continuous.comp_continuous
      (continuous_subtype_val.comp I.neck.coordinate.continuous)
      (fun z => (I.neck.coordinate z).property)).continuousOn.congr
    exact fun z hz => R.neckFill_of_nonpositive z hz
  have hpos : ContinuousOn R.neckFill B := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcoords : Continuous (fun z : B => R.neckCapCoordinates z.val z.property) := by
      apply Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
      apply Continuous.subtype_mk
      exact continuous_const.mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
    apply ((continuous_subtype_val.comp continuous_subtype_val).comp
      (R.puncturedClosedCapPolar.symm.continuous.comp hcoords)).congr
    intro z
    exact (R.neckFill_of_nonnegative z.val z.property).symm
  rw [← continuousOn_univ]
  have hcover : A ∪ B = univ := by
    ext z
    exact iff_true_intro (le_total z.2.val 0)
  rw [← hcover]
  exact hneg.union_of_isClosed hpos hA hB

end PoincareConjecture.MetricSurgeryResult
