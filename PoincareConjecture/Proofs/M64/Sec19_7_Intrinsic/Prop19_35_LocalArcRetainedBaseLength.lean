import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LocalArcLossBounds










noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory

namespace PoincareConjecture




theorem m64Intrinsic_local_retained_short_base_length_lower
    (N : IntrinsicAnnulus) {l u : ℝ} (hlu : l ≤ u) {alpha R : ℝ} {E : Set ℝ}
    (hE : MeasurableSet E) (hEsub : E ⊆ Icc l u)
    {height : ℝ → ℝ} (hh : Measurable height) :
    let X := Ioo l u ∩ {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}
    let S := X \ E
    intrinsicBoundaryLength N.metric 1 l u -
        m64IntrinsicLocalHighCurvatureLength N alpha l u -
        (∫ s in E, intrinsicBoundarySpeed N.metric 1 s) -
        m64IntrinsicLongFiberLength N S height R ≤
      ∫ s in S ∩ {s | height s < R}, intrinsicBoundarySpeed N.metric 1 s := by
  let speed := intrinsicBoundarySpeed N.metric 1
  let B := Ioo l u
  let Y := {s | alpha < intrinsicGeodesicCurvature N.metric N.connection 1 s}
  let X := B ∩ {s | intrinsicGeodesicCurvature N.metric N.connection 1 s ≤ alpha}
  let S := X \ E
  have hspeed : Continuous speed :=
    (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have hY : MeasurableSet Y := (isOpen_lt continuous_const
    (m64Intrinsic_continuous_geodesicCurvature N (by norm_num : (1 : ℝ) ≠ 0))).measurableSet
  have hXB : X ⊆ B := inter_subset_left
  have hBI : B ⊆ Icc l u := Ioo_subset_Icc_self
  have hXeq : B \ Y = X := by
    ext s
    simp only [Y, X, Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_lt]
  have hhigh : (∫ s in B ∩ Y, speed s) =
      m64IntrinsicLocalHighCurvatureLength N alpha l u := rfl
  have hfull : (∫ s in B, speed s) = intrinsicBoundaryLength N.metric 1 l u := by
    change (∫ s in Ioo l u, speed s) = ∫ s in l..u, speed s
    rw [intervalIntegral.integral_of_le hlu, integral_Ioc_eq_integral_Ioo]
  have hsplitX := integral_inter_add_sdiff (μ := volume) (s := B) hY
    (hspeed.integrableOn_Icc.mono_set hBI)
  rw [hXeq, hhigh, hfull] at hsplitX
  have hsplitS := integral_inter_add_sdiff (μ := volume) (s := X) hE
    (hspeed.integrableOn_Icc.mono_set (hXB.trans hBI))
  have hremove : (∫ s in X ∩ E, speed s) ≤ ∫ s in E, speed s := by
    apply setIntegral_mono_set (hspeed.integrableOn_Icc.mono_set hEsub)
      (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
    exact Eventually.of_forall (fun _ hs => hs.2)
  have hlong : MeasurableSet {s | R ≤ height s} := measurableSet_le measurable_const hh
  have hsplitZ := integral_inter_add_sdiff (μ := volume) (s := S) hlong
    (hspeed.integrableOn_Icc.mono_set (sdiff_subset.trans (hXB.trans hBI)))
  have hZeq : S \ {s | R ≤ height s} = S ∩ {s | height s < R} := by
    ext s
    simp only [Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_le]
  change (∫ s in S ∩ {s | R ≤ height s}, speed s) +
    (∫ s in S \ {s | R ≤ height s}, speed s) = ∫ s in S, speed s at hsplitZ
  rw [hZeq] at hsplitZ
  change m64IntrinsicLongFiberLength N S height R +
    (∫ s in S ∩ {s | height s < R}, speed s) = ∫ s in S, speed s at hsplitZ
  change intrinsicBoundaryLength N.metric 1 l u -
      m64IntrinsicLocalHighCurvatureLength N alpha l u - (∫ s in E, speed s) -
      m64IntrinsicLongFiberLength N S height R ≤ ∫ s in S ∩ {s | height s < R}, speed s
  linarith

end PoincareConjecture
