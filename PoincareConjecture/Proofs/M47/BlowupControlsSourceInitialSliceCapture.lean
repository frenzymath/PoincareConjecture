import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialSliceSpeed
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets
import PoincareConjecture.Proofs.M44.Mathlib.FirstExit
import PoincareConjecture.Proofs.M34.Standard.NeckHeightControlPath
import PoincareConjecture.Proofs.M36.MetricComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology Bundle ENNReal NNReal

universe u

namespace PoincareConjecture.M47

open M44 M45

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
  {origin scale : ℝ} {I : Set ℝ}
  (e : SurgeryFlowCylinder F C origin scale I N.carrier)

theorem source_neck_slice_axial_path_length
    (hsmall : N.epsilon ≤ 1 / 2) (s : ℝ) (hs : s ∈ I) (hs0 : s ≤ 0)
    (hclose : RoundCylinderClose N.epsilon s (surgeryCylinderPullback e N.coordinate_map s))
    (gamma : ℝ → (F.slice (origin + s / scale)).carrier)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 1))
    (himage : MapsTo gamma (Icc (0 : ℝ) 1) (e.forward s hs '' N.carrier)) :
    edist (N.coordinate_inverse (e.inverse s hs (gamma 0))).2
        (N.coordinate_inverse (e.inverse s hs (gamma 1))).2 ≤
      ENNReal.ofReal (2 * Real.sqrt scale) *
        (F.metric (origin + s / scale)).pathELength gamma 0 1 := by
  let physical := F.metric (origin + s / scale)
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : (F.slice (origin + s / scale)).carrier → Type _) :=
    ⟨physical.toRiemannianMetric⟩
  have hnorm (x : (F.slice (origin + s / scale)).carrier)
      (v : TangentSpace (𝓡 3) x) : ‖v‖ = physical.tangentNorm x v := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hbound (x : (F.slice (origin + s / scale)).carrier)
      (hx : x ∈ e.forward s hs '' N.carrier) :
      ‖mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse (e.inverse s hs y)).2) x‖ₑ ≤
        ENNReal.ofReal (2 * Real.sqrt scale) := by
    apply ContinuousLinearMap.opENorm_le_bound
    intro v
    have h := ENNReal.ofReal_le_ofReal
      (source_neck_slice_axial_derivative N e hsmall s hs hs0 hclose hx v)
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.sqrt scale)] at h
    simpa only [← ofReal_norm, hnorm, Real.norm_eq_abs] using h
  exact Poincare.edist_le_mul_pathELength_of_mfderiv_le
    (M := (F.slice (origin + s / scale)).carrier) (E := EuclideanSpace ℝ (Fin 3)) (F := ℝ)
    (I := 𝓡 3) (f := fun y => (N.coordinate_inverse (e.inverse s hs y)).2)
    (s := e.forward s hs '' N.carrier) (K := Real.toNNReal (2 * Real.sqrt scale))
    (fun x hx => (source_neck_slice_axial_smooth N e s hs hx).of_le (by simp))
    (fun x hx => by exact hbound x hx) hgamma himage

theorem source_neck_slice_path_capture
    (hsmall : N.epsilon ≤ 1 / 2) (s : ℝ) (hs : s ∈ I) (hs0 : s ≤ 0)
    (hclose : RoundCylinderClose N.epsilon s (surgeryCylinderPullback e N.coordinate_map s))
    {a R ell : ℝ} (ha : a < N.epsilon⁻¹) (hRa : R < a)
    (hbudget : (2 * Real.sqrt scale) * ell ≤ a - R)
    (gamma : ℝ → (F.slice (origin + s / scale)).carrier)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc 0 1))
    {x : C.carrier} (hx : x ∈ N.region (-R) R)
    (hstart : gamma 0 = e.forward s hs x)
    (hlength : (F.metric (origin + s / scale)).pathELength gamma 0 1 < ENNReal.ofReal ell) :
    MapsTo gamma (Icc (0 : ℝ) 1) (e.forward s hs '' N.region (-a) a) := by
  let chart := cylinderSliceChart e N.carrier_open s hs
  let U := e.forward s hs '' N.region (-a) a
  let K0 := N.coordinate_map '' (univ ×ˢ Icc (-a) a)
  let K := e.forward s hs '' K0
  let height := fun y => (N.coordinate_inverse (e.inverse s hs y)).2
  let physical := F.metric (origin + s / scale)
  have haLeft : -N.epsilon⁻¹ < -a := neg_lt_neg ha
  have hK0N : K0 ⊆ N.carrier := N.image_closed_axial_interval_subset_carrier haLeft ha
  have hKN : K ⊆ e.forward s hs '' N.carrier := image_mono hK0N
  have hU : IsOpen U := chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (N.region_isOpen (-a) a)
    (fun _ hy => hy.1)
  have hK : IsClosed K := ((N.isCompact_image_closed_axial_interval haLeft ha).image_of_continuousOn
    ((e.forward_smooth s hs).continuousOn.mono hK0N)).isClosed
  have hUK : U ⊆ K := by
    apply image_mono
    intro y hy
    exact ⟨N.coordinate_inverse y, ⟨mem_univ _, hy.2.1.le, hy.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hy.1⟩
  have hclosure : closure U ⊆ K := closure_minimal hUK hK
  have hheightK (y : (F.slice (origin + s / scale)).carrier) (hy : y ∈ K) :
      |height y| ≤ a := by
    obtain ⟨z, ⟨w, hw, rfl⟩, rfl⟩ := hy
    have hwN : w.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
      ⟨haLeft.trans_le hw.2.1, hw.2.2.trans_lt ha⟩
    change |(N.coordinate_inverse (e.inverse s hs (e.forward s hs (N.coordinate_map w)))).2| ≤ a
    rw [e.left_inverse s hs (N.coordinate_map_mem_of_axial_mem hwN),
      N.coordinate_inverse_coordinate_map_of_axial_mem hwN]
    exact abs_le.mpr hw.2
  have hexit (y : (F.slice (origin + s / scale)).carrier) (hy : y ∈ K) (hout : y ∉ U) :
      |height y| = a := by
    apply le_antisymm (hheightK y hy)
    by_contra h
    have hlt : |height y| < a := lt_of_not_ge h
    have hyN := chart.map_target (hKN hy)
    exact hout ⟨e.inverse s hs y, ⟨hyN, abs_lt.mp hlt⟩,
      e.right_inverse s hs (hKN hy)⟩
  have hstartU : gamma 0 ∈ U := by
    rw [hstart]
    exact mem_image_of_mem _ ⟨hx.1, by linarith only [hx.2.1, hRa], hx.2.2.trans hRa⟩
  have hheight0 : |height (gamma 0)| < R := by
    rw [hstart]
    change |(N.coordinate_inverse (e.inverse s hs (e.forward s hs x))).2| < R
    rw [e.left_inverse s hs hx.1]
    exact abs_lt.mpr hx.2
  intro t ht
  by_contra hout
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
  obtain ⟨r, hr, hfrontier, _, hbefore⟩ :=
    (hgamma.mono hsub).continuousOn.exists_first_frontier_time ht.1 hU hstartU hout
  have hrOne : r ≤ 1 := hr.2.trans ht.2
  have hendK : gamma r ∈ K := hclosure (frontier_subset_closure hfrontier)
  have hendout : gamma r ∉ U := by simpa only [hU.interior_eq] using hfrontier.2
  have hheightR := hexit (gamma r) hendK hendout
  have hprefix : MapsTo gamma (Icc (0 : ℝ) r) (e.forward s hs '' N.carrier) :=
    fun z hz => hKN (hclosure (hbefore hz))
  let clock : ℝ → ℝ := fun z => r * z
  let path := gamma ∘ clock
  have hclock : ContDiff ℝ 1 clock := contDiff_const.mul contDiff_id
  have hclockmap : MapsTo clock (Icc (0 : ℝ) 1) (Icc 0 r) := by
    intro z hz
    exact ⟨mul_nonneg hr.1.le hz.1,
      (mul_le_mul_of_nonneg_left hz.2 hr.1.le).trans_eq (mul_one r)⟩
  have hsmallInterval : Icc (0 : ℝ) r ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hrOne
  have hpath : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 path (Icc 0 1) :=
    (hgamma.mono hsmallInterval).comp hclock.contMDiff.contMDiffOn hclockmap
  have himage : MapsTo path (Icc (0 : ℝ) 1) (e.forward s hs '' N.carrier) :=
    fun z hz => hprefix (hclockmap hz)
  have hparam : physical.pathELength path 0 1 = physical.pathELength gamma 0 r := by
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (F.slice (origin + s / scale)).carrier → Type _) :=
      ⟨physical.toRiemannianMetric⟩
    have hd : MDifferentiableOn 𝓘(ℝ, ℝ) (𝓡 3) gamma (Icc (clock 0) (clock 1)) := by
      simpa only [clock, mul_zero, mul_one] using
        (hgamma.mono hsmallInterval).mdifferentiableOn one_ne_zero
    have heq := Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 3) zero_le_one
      (show MonotoneOn clock (Icc (0 : ℝ) 1) from
        fun _ _ _ _ hab => mul_le_mul_of_nonneg_left hab hr.1.le)
      (hclock.differentiable one_ne_zero).differentiableOn hd
    convert! heq using 1
    simp only [clock, mul_zero, mul_one]
    rfl
  have hlenle : physical.pathELength path 0 1 ≤ physical.pathELength gamma 0 1 :=
    hparam.le.trans (M36.metric_pathELength_mono _ _ le_rfl hrOne)
  have haxis := source_neck_slice_axial_path_length N e hsmall s hs hs0 hclose path hpath himage
  change edist (height (path 0)) (height (path 1)) ≤ _ at haxis
  simp only [path, Function.comp_apply, clock, mul_zero, mul_one, edist_dist, Real.dist_eq] at haxis
  have htriangle : |height (gamma r)| ≤
      |height (gamma 0) - height (gamma r)| + |height (gamma 0)| := by
    calc
      _ = |(height (gamma r) - height (gamma 0)) + height (gamma 0)| := by congr 1; ring
      _ ≤ |height (gamma r) - height (gamma 0)| + |height (gamma 0)| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (height (gamma r)) (height (gamma 0))]
  have hdisplacement : a - R < |height (gamma 0) - height (gamma r)| := by
    rw [hheightR] at htriangle
    linarith only [htriangle, hheight0]
  have hfactor : 0 < 2 * Real.sqrt scale := mul_pos (by norm_num) (Real.sqrt_pos.mpr e.scale_pos)
  have hstrict : ENNReal.ofReal (2 * Real.sqrt scale) * physical.pathELength path 0 1 <
      ENNReal.ofReal |height (gamma 0) - height (gamma r)| := by
    calc
      _ ≤ ENNReal.ofReal (2 * Real.sqrt scale) * physical.pathELength gamma 0 1 :=
        mul_le_mul_right hlenle _
      _ < ENNReal.ofReal (2 * Real.sqrt scale) * ENNReal.ofReal ell :=
        ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr hfactor))
          ENNReal.ofReal_ne_top hlength
      _ = ENNReal.ofReal ((2 * Real.sqrt scale) * ell) := (ENNReal.ofReal_mul hfactor.le).symm
      _ < _ := (ENNReal.ofReal_lt_ofReal_iff (by linarith only [hdisplacement, hRa])).mpr
        (hbudget.trans_lt hdisplacement)
  exact not_lt_of_ge haxis hstrict

end PoincareConjecture.M47
