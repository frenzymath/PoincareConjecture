import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MetricInteriorFan













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory MeasureTheory.Measure InnerProductGeometry
open scoped ENNReal Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem positive_cone_convex (x y : ℂ) :
    Convex ℝ {z : ℂ | ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • x + c • y} := by
  let L : (ℝ × ℝ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight x +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight y
  have heq : {z : ℂ | ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • x + c • y} =
      L '' (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    ext z
    constructor
    · rintro ⟨a, c, ha, hc, hz⟩
      exact ⟨(a, c), ⟨ha, hc⟩, hz.symm⟩
    · rintro ⟨⟨a, c⟩, ⟨ha, hc⟩, hz⟩
      exact ⟨a, c, ha, hc, hz.symm⟩
  rw [heq]
  exact ((convex_Ioi (0 : ℝ)).prod (convex_Ioi (0 : ℝ))).linear_image L.toLinearMap

private theorem complex_sector_angle_sum
    {I : Type*} [Fintype I] (x y : I → ℂ) (u v : ℂ)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hangle : ∀ i, angle (x i) (y i) ∈ Ioo (0 : ℝ) Real.pi)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : angle u v ∈ Ioo (0 : ℝ) Real.pi)
    (hpartition : ∀ᵐ z : ℂ,
      ((∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • u + c • v) →
        ∃! i, ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • x i + c • y i) ∧
      (∀ i, (∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • x i + c • y i) →
        ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • u + c • v)) :
    (∑ i, angle (x i) (y i)) = angle u v := by
  classical
  let C (x y : ℂ) : Set ℂ := {z | ‖z‖ < 1 ∧
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • x + c • y}
  have hconv (x y : ℂ) : Convex ℝ (C x y) := by
    have heq : C x y = Metric.ball (0 : ℂ) 1 ∩
        {z | ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • x + c • y} := by
      ext z
      simp only [C, mem_ofPred_eq, mem_inter_iff, Metric.mem_ball, dist_zero_right]
    rw [heq]
    exact (convex_ball (0 : ℂ) 1).inter (positive_cone_convex x y)
  have hdisj : Pairwise (fun i j => AEDisjoint volume (C (x i) (y i)) (C (x j) (y j))) := by
    intro i j hij
    rw [AEDisjoint]
    apply measure_mono_null_ae
    · filter_upwards [hpartition] with z hz hboth
      obtain ⟨k, _, hk⟩ := hz.1 (hz.2 i hboth.1.2)
      exact (hij ((hk i hboth.1.2).trans (hk j hboth.2.2).symm)).elim
    · exact measure_empty
  have hcover : (⋃ i, C (x i) (y i)) =ᵐ[volume] C u v := by
    filter_upwards [hpartition] with z hz
    apply propext
    constructor
    · intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact ⟨hi.1, hz.2 i hi.2⟩
    · intro h
      obtain ⟨i, hi, _⟩ := hz.1 h.2
      exact mem_iUnion.mpr ⟨i, h.1, hi⟩
  have hsum : (∑ i, volume (C (x i) (y i))) = volume (C u v) := by
    calc
      _ = volume (⋃ i, C (x i) (y i)) := by
        symm
        simpa only [tsum_fintype] using measure_iUnion₀ hdisj
          (fun i => (hconv (x i) (y i)).nullMeasurableSet volume)
      _ = _ := measure_congr hcover
  have harea (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
      (hxy : angle x y ∈ Ioo (0 : ℝ) Real.pi) :
      volume (C x y) = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (angle x y) := by
    simpa only [one_pow] using m64Intrinsic_complex_corner_cone_volume
      (by norm_num : (0 : ℝ) < 1) hx hy hxy
  simp_rw [harea _ _ (hx _) (hy _) (hangle _)] at hsum
  rw [harea u v hu hv huv, ← Finset.mul_sum,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hangle i).1.le)] at hsum
  have hreal := congrArg ENNReal.toReal hsum
  have hnonneg : 0 ≤ ∑ i, angle (x i) (y i) :=
    Finset.sum_nonneg (fun i _ => (hangle i).1.le)
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal huv.1.le] at hreal
  linarith






theorem m64Intrinsic_metric_sector_fan_angle_sum
    {I : Type*} [Fintype I]
    (g : RiemannianMetric 2 AnnulusCoordinates) (q : AnnulusCoordinates)
    (x y : I → AnnulusCoordinates) (u v : AnnulusCoordinates)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hangle : ∀ i, g.cornerAngle q (x i) (y i) ∈ Ioo (0 : ℝ) Real.pi)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : g.cornerAngle q u v ∈ Ioo (0 : ℝ) Real.pi)
    (hpartition : ∀ᵐ w : AnnulusCoordinates,
      ((∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • u + c • v) →
        ∃! i, ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • x i + c • y i) ∧
      (∀ i, (∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • x i + c • y i) →
        ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • u + c • v)) :
    (∑ i, g.cornerAngle q (x i) (y i)) = g.cornerAngle q u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) q) = 2 := finrank_euclideanSpace_fin
  let B := (g.orthonormalBasis q).reindex (finCongr hd)
  let J := B.repr.trans Complex.orthonormalBasisOneI.repr.symm
  let L : AnnulusCoordinates ≃ₗ[ℝ] ℂ := J.toLinearEquiv
  have hangleL (v w : AnnulusCoordinates) : angle (L v) (L w) = g.cornerAngle q v w :=
    (J.toLinearIsometry.angle_map v w).trans (cornerAngle_eq_innerProduct_angle g q v w).symm
  let E : AnnulusCoordinates ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let T : ℂ ≃L[ℝ] ℂ := L.symm.toContinuousLinearEquiv.trans E.toContinuousLinearEquiv
  have hT : QuasiMeasurePreserving T volume volume :=
    LinearMap.quasiMeasurePreserving volume T.toLinearEquiv.toLinearMap
      T.toLinearEquiv.isUnit_det'.ne_zero
  have hpreserve : QuasiMeasurePreserving (fun z : ℂ => L.symm z) volume volume := by
    have hE : MeasurePreserving E.symm volume volume :=
      Complex.orthonormalBasisOneI.measurePreserving_repr
    have h := hE.quasiMeasurePreserving.comp hT
    have heq : E.symm ∘ T = fun z : ℂ => L.symm z := by
      funext z
      exact E.symm_apply_apply (L.symm z)
    rw [heq] at h
    convert h using 1
  have hcone (z : ℂ) (v w : AnnulusCoordinates) :
      (∃ a c : ℝ, 0 < a ∧ 0 < c ∧ L.symm z = a • v + c • w) ↔
        ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ z = a • L v + c • L w := by
    constructor
    · rintro ⟨a, c, ha, hc, heq⟩
      refine ⟨a, c, ha, hc, ?_⟩
      simpa only [L.apply_symm_apply, map_add, map_smul] using congrArg L heq
    · rintro ⟨a, c, ha, hc, heq⟩
      refine ⟨a, c, ha, hc, ?_⟩
      rw [heq, map_add, map_smul, map_smul, L.symm_apply_apply, L.symm_apply_apply]
  have hcomplex := hpreserve.ae hpartition
  simp only [hcone] at hcomplex
  have hne {w : AnnulusCoordinates} (hw : w ≠ 0) : L w ≠ 0 :=
    fun h => hw (L.injective (h.trans L.map_zero.symm))
  have hsum := complex_sector_angle_sum (fun i => L (x i)) (fun i => L (y i)) (L u) (L v)
    (fun i => hne (hx i)) (fun i => hne (hy i))
    (fun i => by simpa only [hangleL] using hangle i)
    (hne hu) (hne hv) (by simpa only [hangleL] using huv) hcomplex
  simpa only [hangleL] using hsum





theorem m64Intrinsic_metric_reflex_fan_angle_sum
    {I : Type*} [Fintype I]
    (g : RiemannianMetric 2 AnnulusCoordinates) (q : AnnulusCoordinates)
    (x y : I → AnnulusCoordinates) (u v : AnnulusCoordinates)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (hangle : ∀ i, g.cornerAngle q (x i) (y i) ∈ Ioo (0 : ℝ) Real.pi)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : g.cornerAngle q u v ∈ Ioo (0 : ℝ) Real.pi)
    (hpartition : ∀ᵐ w : AnnulusCoordinates,
      ((¬ ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • u + c • v) →
        ∃! i, ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • x i + c • y i) ∧
      (∀ i, (∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • x i + c • y i) →
        ¬ ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • u + c • v)) :
    (∑ i, g.cornerAngle q (x i) (y i)) = 2 * Real.pi - g.cornerAngle q u v := by
  classical
  let X : I ⊕ Unit → AnnulusCoordinates := Sum.elim x (fun _ => u)
  let Y : I ⊕ Unit → AnnulusCoordinates := Sum.elim y (fun _ => v)
  have hfull : ∀ᵐ w : AnnulusCoordinates, ∃! i, ∃ a c : ℝ,
      0 < a ∧ 0 < c ∧ w = a • X i + c • Y i := by
    filter_upwards [hpartition] with w hw
    by_cases hcone : ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ w = a • u + c • v
    · refine ⟨Sum.inr (), hcone, ?_⟩
      intro j hj
      cases j with
      | inl j => exact False.elim (hw.2 j hj hcone)
      | inr j => cases j; rfl
    · obtain ⟨i, hi, huniq⟩ := hw.1 hcone
      refine ⟨Sum.inl i, hi, ?_⟩
      intro j hj
      cases j with
      | inl j => exact congrArg Sum.inl (huniq j hj)
      | inr j => exact False.elim (hcone hj)
  have hsum := m64Intrinsic_metric_fan_angle_sum g q X Y
    (fun i => by cases i with | inl i => exact hx i | inr _ => exact hu)
    (fun i => by cases i with | inl i => exact hy i | inr _ => exact hv)
    (fun i => by cases i with | inl i => exact hangle i | inr _ => exact huv) hfull
  simp only [Fintype.sum_sum_type, X, Y, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique] at hsum
  linarith

end PoincareConjecture
