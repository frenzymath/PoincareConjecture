import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Set Filter Topology
open scoped intervalIntegral ContDiff

namespace PoincareConjecture.ReducedLengthMinimum.Variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable local instance dualNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance dualNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance bilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance bilinearNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance trilinearNormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup

theorem affine_chart_density_hasDerivAt
    (G : E → E →L[ℝ] E →L[ℝ] ℝ) (V : E → ℝ)
    (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (DV : E →L[ℝ] ℝ)
    (x η v ν : E) (ε : ℝ)
    (hG : HasFDerivAt G DG (x + ε • η))
    (hV : HasFDerivAt V DV (x + ε • η))
    (hsym : ∀ z z' : E, G (x + ε • η) z z' = G (x + ε • η) z' z) :
    HasDerivAt
      (fun e : ℝ => G (x + e • η) (v + e • ν) (v + e • ν) / 2 +
        V (x + e • η))
      (DG η (v + ε • ν) (v + ε • ν) / 2 +
        G (x + ε • η) (v + ε • ν) ν + DV η) ε := by
  have hx : HasDerivAt (fun e : ℝ => x + e • η) η ε := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id ε).smul_const η).const_add x
  have hv : HasDerivAt (fun e : ℝ => v + e • ν) ν ε := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id ε).smul_const ν).const_add v
  have hGc : HasDerivAt (fun e : ℝ ↦ G (x + e • η)) (DG η) ε :=
    by simpa only [Function.comp_def] using
      HasFDerivAt.comp_hasDerivAt ε (l := G) (l' := DG) hG hx
  have hGvv := (hGc.clm_apply hv).clm_apply hv
  have hpot : HasDerivAt (fun e : ℝ ↦ V (x + e • η)) (DV η) ε :=
    HasFDerivAt.comp_hasDerivAt ε (l := V) (l' := DV) hV hx
  have hcalc := (hGvv.div_const 2).add hpot
  convert hcalc using 1 <;> try rfl
  show DG η (v + ε • ν) (v + ε • ν) / 2 +
      G (x + ε • η) (v + ε • ν) ν + DV η =
    (DG η (v + ε • ν) (v + ε • ν) + G (x + ε • η) ν (v + ε • ν) +
      G (x + ε • η) (v + ε • ν) ν) / 2 + DV η
  rw [hsym ν (v + ε • ν)]
  ring

theorem affine_chart_domination_polynomial {x D : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D) :
    (x + D) ^ 2 / 2 + (x + D) + 1 ≤ (D ^ 2 + D + 3) * (1 + x ^ 2) := by
  nlinarith [sq_nonneg (x - D), sq_nonneg (x - 1),
    mul_nonneg hD (sq_nonneg x), mul_nonneg (sq_nonneg D) (sq_nonneg x)]

theorem affine_chart_density_deriv_bound
    (G : E →L[ℝ] E →L[ℝ] ℝ) (DG : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : E →L[ℝ] ℝ) (v η ν : E) {ε C D : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hε : |ε| ≤ 1)
    (hG : ‖G‖ ≤ C) (hDG : ‖DG‖ ≤ C) (hDV : ‖DV‖ ≤ C)
    (hη : ‖η‖ ≤ D) (hν : ‖ν‖ ≤ D) :
    ‖DG η (v + ε • ν) (v + ε • ν) / 2 + G (v + ε • ν) ν + DV η‖ ≤
      C * D * (D ^ 2 + D + 3) * (1 + ‖v‖ ^ 2) := by
  let W := ‖v‖ + D
  have hW : 0 ≤ W := add_nonneg (norm_nonneg v) hD
  have hv : ‖v + ε • ν‖ ≤ W := by
    calc
      ‖v + ε • ν‖ ≤ ‖v‖ + ‖ε • ν‖ := norm_add_le _ _
      _ = ‖v‖ + |ε| * ‖ν‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ ‖v‖ + 1 * D := by gcongr
      _ = W := by rw [one_mul]
  have hDGη : ‖DG η‖ ≤ C * D :=
    (DG.le_opNorm η).trans (mul_le_mul hDG hη (norm_nonneg η) hC)
  have ht : ‖DG η (v + ε • ν) (v + ε • ν)‖ ≤ C * D * W ^ 2 := by
    calc
      _ ≤ ‖DG η‖ * ‖v + ε • ν‖ * ‖v + ε • ν‖ := (DG η).le_opNorm₂ _ _
      _ ≤ (C * D) * W * W := by gcongr
      _ = C * D * W ^ 2 := by ring
  have hg : ‖G (v + ε • ν) ν‖ ≤ C * W * D := by
    calc
      _ ≤ ‖G‖ * ‖v + ε • ν‖ * ‖ν‖ := G.le_opNorm₂ _ _
      _ ≤ C * W * D := by gcongr
  have hdv : ‖DV η‖ ≤ C * D :=
    (DV.le_opNorm η).trans (mul_le_mul hDV hη (norm_nonneg η) hC)
  calc
    _ ≤ (‖DG η (v + ε • ν) (v + ε • ν) / 2‖ + ‖G (v + ε • ν) ν‖) +
        ‖DV η‖ := (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (C * D * W ^ 2 / 2 + C * W * D) + C * D := by
      rw [norm_div, Real.norm_ofNat]
      gcongr
    _ = C * D * (W ^ 2 / 2 + W + 1) := by ring
    _ ≤ C * D * ((D ^ 2 + D + 3) * (1 + ‖v‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (affine_chart_domination_polynomial (norm_nonneg v) hD)
        (mul_nonneg hC hD)
    _ = _ := by ring

theorem affine_chart_action_hasDerivAt {a b δ C D : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (K : Set E) (u w η ν : ℝ → E)
    (hu : ContinuousOn u (Icc a b)) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (hη : ContinuousOn η (Icc a b)) (hν : ContinuousOn ν (Icc a b))
    (G : ℝ → E → E →L[ℝ] E →L[ℝ] ℝ) (V : ℝ → E → ℝ)
    (DG : ℝ → E → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (DV : ℝ → E → E →L[ℝ] ℝ)
    (hGcont : ContinuousOn (fun p : ℝ × E ↦ G p.1 p.2) (Icc a b ×ˢ K))
    (hVcont : ContinuousOn (fun p : ℝ × E ↦ V p.1 p.2) (Icc a b ×ˢ K))
    (hDGcont : ContinuousOn (fun p : ℝ × E ↦ DG p.1 p.2) (Icc a b ×ˢ K))
    (hDVcont : ContinuousOn (fun p : ℝ × E ↦ DV p.1 p.2) (Icc a b ×ˢ K))
    (hmem : ∀ e ∈ Ioo (-δ) δ, ∀ s ∈ Icc a b, u s + e • η s ∈ K)
    (hGderiv : ∀ s ∈ Icc a b, ∀ x ∈ K, HasFDerivAt (G s) (DG s x) x)
    (hVderiv : ∀ s ∈ Icc a b, ∀ x ∈ K, HasFDerivAt (V s) (DV s x) x)
    (hsym : ∀ s ∈ Icc a b, ∀ x ∈ K, ∀ v v' : E, G s x v v' = G s x v' v)
    (hcoeff : ∀ s ∈ Icc a b, ∀ x ∈ K,
      ‖G s x‖ ≤ C ∧ ‖DG s x‖ ≤ C ∧ ‖DV s x‖ ≤ C)
    (hdir : ∀ s ∈ Icc a b, ‖η s‖ ≤ D ∧ ‖ν s‖ ≤ D) :
    IntervalIntegrable
      (fun s ↦ DG s (u s) (η s) (w s) (w s) / 2 + G s (u s) (w s) (ν s) +
        DV s (u s) (η s)) volume a b ∧
    HasDerivAt
      (fun e : ℝ ↦ ∫ s in a..b,
        G s (u s + e • η s) (w s + e • ν s) (w s + e • ν s) / 2 +
          V s (u s + e • η s))
      (∫ s in a..b,
        DG s (u s) (η s) (w s) (w s) / 2 + G s (u s) (w s) (ν s) +
          DV s (u s) (η s)) 0 := by
  let μ := volume.restrict (Icc a b)
  let f (e s : ℝ) :=
    G s (u s + e • η s) (w s + e • ν s) (w s + e • ν s) / 2 +
      V s (u s + e • η s)
  let f' (e s : ℝ) :=
    DG s (u s + e • η s) (η s) (w s + e • ν s) (w s + e • ν s) / 2 +
      G s (u s + e • η s) (w s + e • ν s) (ν s) + DV s (u s + e • η s) (η s)
  let bound (s : ℝ) := C * D * (D ^ 2 + D + 3) * (1 + ‖w s‖ ^ 2)
  have hzero : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hnhds : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds hzero.1 hzero.2
  have huK (s : ℝ) (hs : s ∈ Icc a b) : u s ∈ K := by
    simpa only [zero_smul, add_zero] using hmem 0 hzero s hs
  have hsub : uIoc a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]
    exact Ioc_subset_Icc_self
  have hΓ (e : ℝ) : ContinuousOn (fun s ↦ (s, u s + e • η s)) (Icc a b) :=
    continuousOn_id.prodMk (hu.add (continuousOn_const.smul hη))
  have hΓmem (e : ℝ) (he : e ∈ Ioo (-δ) δ) :
      MapsTo (fun s ↦ (s, u s + e • η s)) (Icc a b) (Icc a b ×ˢ K) :=
    fun s hs ↦ ⟨hs, hmem e he s hs⟩
  have hGε (e : ℝ) (he : e ∈ Ioo (-δ) δ) :
      ContinuousOn (fun s ↦ G s (u s + e • η s)) (Icc a b) :=
    hGcont.comp (hΓ e) (hΓmem e he)
  have hVε (e : ℝ) (he : e ∈ Ioo (-δ) δ) :
      ContinuousOn (fun s ↦ V s (u s + e • η s)) (Icc a b) :=
    hVcont.comp (hΓ e) (hΓmem e he)
  have hG0 : ContinuousOn (fun s ↦ G s (u s)) (Icc a b) := by
    simpa only [zero_smul, add_zero] using hGε 0 hzero
  have hV0 : ContinuousOn (fun s ↦ V s (u s)) (Icc a b) := by
    simpa only [zero_smul, add_zero] using hVε 0 hzero
  have hDG0 : ContinuousOn (fun s ↦ DG s (u s)) (Icc a b) := by
    simpa only [zero_smul, add_zero, Function.comp_def] using hDGcont.comp (hΓ 0) (hΓmem 0 hzero)
  have hDV0 : ContinuousOn (fun s ↦ DV s (u s)) (Icc a b) := by
    simpa only [zero_smul, add_zero, Function.comp_def] using hDVcont.comp (hΓ 0) (hΓmem 0 hzero)
  have hwm : AEStronglyMeasurable w μ := hw.aestronglyMeasurable
  have hηm : AEStronglyMeasurable η μ := hη.aestronglyMeasurable measurableSet_Icc
  have hνm : AEStronglyMeasurable ν μ := hν.aestronglyMeasurable measurableSet_Icc
  have hfm (e : ℝ) (he : e ∈ Ioo (-δ) δ) : AEStronglyMeasurable (f e) μ := by
    have hgm : AEStronglyMeasurable (fun s ↦ G s (u s + e • η s)) μ :=
      (hGε e he).aestronglyMeasurable measurableSet_Icc
    have hvm := hwm.add (hνm.const_smul e)
    have hgw := (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
      hgm hvm
    have hgwv := (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂ hgw hvm
    exact (hgwv.div₀ aestronglyMeasurable_const).add
      ((hVε e he).aestronglyMeasurable measurableSet_Icc)
  have hkmeas : AEStronglyMeasurable (fun s ↦ G s (u s) (w s) (w s)) μ := by
    have hgw := (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
      (hG0.aestronglyMeasurable measurableSet_Icc) hwm
    exact (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂ hgw hwm
  have hwSq : Integrable (fun s ↦ ‖w s‖ ^ 2) μ := hw.norm.integrable_sq
  have hkint : Integrable (fun s ↦ G s (u s) (w s) (w s)) μ := by
    apply (hwSq.const_mul C).mono' hkmeas
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    calc
      _ ≤ ‖G s (u s)‖ * ‖w s‖ * ‖w s‖ := (G s (u s)).le_opNorm₂ _ _
      _ ≤ C * ‖w s‖ * ‖w s‖ := by gcongr; exact (hcoeff s hs (u s) (huK s hs)).1
      _ = C * ‖w s‖ ^ 2 := by ring
  have hfint : IntervalIntegrable (f 0) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    simp only [f, zero_smul, add_zero]
    convert (hkint.div_const 2).add hV0.integrableOn_Icc using 1 <;> rfl
  have hf'm : AEStronglyMeasurable (f' 0) μ := by
    have hDη := hDG0.clm_apply hη
    have hDηm : AEStronglyMeasurable (fun s ↦ DG s (u s) (η s)) μ :=
      hDη.aestronglyMeasurable measurableSet_Icc
    have hDηw := (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
      hDηm hwm
    have hDηww := (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂ hDηw hwm
    have hGw := (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
      (hG0.aestronglyMeasurable measurableSet_Icc) hwm
    have hGwν := (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂ hGw hνm
    have hDVη : AEStronglyMeasurable (fun s ↦ DV s (u s) (η s)) μ :=
      (hDV0.clm_apply hη).aestronglyMeasurable measurableSet_Icc
    simp only [f', zero_smul, add_zero]
    convert ((hDηww.div₀ aestronglyMeasurable_const).add hGwν).add hDVη using 1 <;> rfl
  have hboundint : IntervalIntegrable bound volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact ((integrable_const (1 : ℝ)).add hwSq).const_mul (C * D * (D ^ 2 + D + 3))
  have hdifferentiation := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := f) (F' := f') (bound := bound) hnhds
    (by
      filter_upwards [hnhds] with e he
      exact (hfm e he).mono_measure (Measure.restrict_mono hsub le_rfl)) hfint
    (hf'm.mono_measure (Measure.restrict_mono hsub le_rfl))
    (by
      filter_upwards with s hs e he
      have hcs := hcoeff s (hsub hs) _ (hmem e he s (hsub hs))
      exact affine_chart_density_deriv_bound _ _ _ (w s) (η s) (ν s) hC hD
        ((abs_lt.mpr he).le.trans hδ1) hcs.1 hcs.2.1 hcs.2.2
        (hdir s (hsub hs)).1 (hdir s (hsub hs)).2)
    hboundint
    (by
      filter_upwards with s hs e he
      exact affine_chart_density_hasDerivAt (G s) (V s) _ _ (u s) (η s) (w s) (ν s) e
        (hGderiv s (hsub hs) _ (hmem e he s (hsub hs)))
        (hVderiv s (hsub hs) _ (hmem e he s (hsub hs)))
        (hsym s (hsub hs) _ (hmem e he s (hsub hs))))
  simpa only [f, f', zero_smul, add_zero] using hdifferentiation

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def chartMomentumVector (G : F →L[ℝ] F →L[ℝ] ℝ) (w : F) : F :=
  (InnerProductSpace.toDual ℝ F).symm (G w)

noncomputable def chartForceVector (DG : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (DV : F →L[ℝ] ℝ) (w : F) : F :=
  (InnerProductSpace.toDual ℝ F).symm
    ((1 / 2 : ℝ) • ((DG.flip w).flip w) + DV)

theorem chartMomentumVector_inner (G : F →L[ℝ] F →L[ℝ] ℝ) (w z : F) :
    inner ℝ z (chartMomentumVector G w) = G w z := by
  rw [real_inner_comm, chartMomentumVector, InnerProductSpace.toDual_symm_apply]

theorem chartForceVector_inner (DG : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (DV : F →L[ℝ] ℝ) (w z : F) :
    inner ℝ z (chartForceVector DG DV w) = DG z w w / 2 + DV z := by
  rw [real_inner_comm, chartForceVector, InnerProductSpace.toDual_symm_apply]
  simp only [add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply,
    smul_eq_mul]
  ring

theorem chartMomentumVector_norm_le (G : F →L[ℝ] F →L[ℝ] ℝ) (w : F) :
    ‖chartMomentumVector G w‖ ≤ ‖G‖ * ‖w‖ := by
  rw [chartMomentumVector, (InnerProductSpace.toDual ℝ F).symm.norm_map]
  exact G.le_opNorm w

theorem chartForceVector_norm_le (DG : F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)
    (DV : F →L[ℝ] ℝ) (w : F) :
    ‖chartForceVector DG DV w‖ ≤ ‖DG‖ * ‖w‖ ^ 2 / 2 + ‖DV‖ := by
  have hL : ‖(DG.flip w).flip w‖ ≤ ‖DG‖ * ‖w‖ ^ 2 := by
    calc
      _ ≤ ‖(DG.flip w).flip‖ * ‖w‖ := ((DG.flip w).flip).le_opNorm w
      _ = ‖DG.flip w‖ * ‖w‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (‖DG.flip‖ * ‖w‖) * ‖w‖ := by
        gcongr
        exact DG.flip.le_opNorm w
      _ = ‖DG‖ * ‖w‖ ^ 2 := by rw [ContinuousLinearMap.opNorm_flip]; ring
  rw [chartForceVector, (InnerProductSpace.toDual ℝ F).symm.norm_map]
  calc
    _ ≤ ‖(1 / 2 : ℝ) • ((DG.flip w).flip w)‖ + ‖DV‖ := norm_add_le _ _
    _ = ‖(DG.flip w).flip w‖ / 2 + ‖DV‖ := by rw [norm_smul]; norm_num; ring
    _ ≤ _ := by gcongr

theorem chart_momentum_force_intervalIntegrable {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (w : ℝ → F) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (G : ℝ → F →L[ℝ] F →L[ℝ] ℝ)
    (DG : ℝ → F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (DV : ℝ → F →L[ℝ] ℝ)
    (hG : ContinuousOn G (Icc a b)) (hDG : ContinuousOn DG (Icc a b))
    (hDV : ContinuousOn DV (Icc a b))
    (hbound : ∀ s ∈ Icc a b, ‖G s‖ ≤ C ∧ ‖DG s‖ ≤ C ∧ ‖DV s‖ ≤ C) :
    IntervalIntegrable (fun s ↦ chartMomentumVector (G s) (w s)) volume a b ∧
      IntervalIntegrable (fun s ↦ chartForceVector (DG s) (DV s) (w s)) volume a b := by
  let μ := volume.restrict (Icc a b)
  have hwm : AEStronglyMeasurable w μ := hw.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G μ := hG.aestronglyMeasurable measurableSet_Icc
  have hDGm : AEStronglyMeasurable DG μ := hDG.aestronglyMeasurable measurableSet_Icc
  have hDVm : AEStronglyMeasurable DV μ := hDV.aestronglyMeasurable measurableSet_Icc
  have hGw := (ContinuousLinearMap.id ℝ (F →L[ℝ] F →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
    (𝕜 := ℝ) hGm hwm
  have hPm : AEStronglyMeasurable (fun s ↦ chartMomentumVector (G s) (w s)) μ :=
    (InnerProductSpace.toDual ℝ F).symm.continuous.comp_aestronglyMeasurable hGw
  have hDf : AEStronglyMeasurable (fun s ↦ (DG s).flip) μ :=
    (ContinuousLinearMap.flipₗᵢ ℝ F F (F →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable hDGm
  have hDfw := (ContinuousLinearMap.id ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
    (𝕜 := ℝ) hDf hwm
  have hDfwf : AEStronglyMeasurable (fun s ↦ ((DG s).flip (w s)).flip) μ :=
    (ContinuousLinearMap.flipₗᵢ ℝ F F ℝ).continuous.comp_aestronglyMeasurable hDfw
  have hL := (ContinuousLinearMap.id ℝ (F →L[ℝ] F →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
    (𝕜 := ℝ) hDfwf hwm
  have hQm : AEStronglyMeasurable (fun s ↦ chartForceVector (DG s) (DV s) (w s)) μ :=
    (InnerProductSpace.toDual ℝ F).symm.continuous.comp_aestronglyMeasurable
      ((hL.const_smul (1 / 2 : ℝ)).add hDVm)
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    apply ((MemLp.integrable (by norm_num) hw).norm.const_mul C).mono' hPm
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (chartMomentumVector_norm_le (G s) (w s)).trans
      (mul_le_mul_of_nonneg_right (hbound s hs).1 (norm_nonneg _))
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    have hi : Integrable (fun s ↦ C * ‖w s‖ ^ 2 / 2 + C) μ :=
      ((hw.norm.integrable_sq.const_mul C).div_const 2).add (integrable_const C)
    apply hi.mono' hQm
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    apply (chartForceVector_norm_le (DG s) (DV s) (w s)).trans
    gcongr
    · exact (hbound s hs).2.1
    · exact (hbound s hs).2.2

theorem weak_momentum_of_scalar_stationarity {a b : ℝ}
    (P Q : ℝ → F) (hP : IntervalIntegrable P volume a b)
    (hQ : IntervalIntegrable Q volume a b) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hstationary : ∀ z : F,
      (∫ s in a..b, deriv φ s * inner ℝ z (P s) + φ s * inner ℝ z (Q s)) = 0) :
    (∫ s in a..b, deriv φ s • P s) = -(∫ s in a..b, φ s • Q s) := by
  have hDP : IntervalIntegrable (fun s ↦ deriv φ s • P s) volume a b :=
    hP.continuousOn_smul (hφ.continuous_deriv (by norm_num)).continuousOn
  have hφQ : IntervalIntegrable (fun s ↦ φ s • Q s) volume a b :=
    hQ.continuousOn_smul hφ.continuous.continuousOn
  apply ext_inner_left ℝ
  intro z
  let l : F →L[ℝ] ℝ := innerSL ℝ z
  have hDPscalar : IntervalIntegrable (fun s ↦ l (deriv φ s • P s)) volume a b :=
    ⟨l.integrable_comp hDP.1, l.integrable_comp hDP.2⟩
  have hQscalar : IntervalIntegrable (fun s ↦ l (φ s • Q s)) volume a b :=
    ⟨l.integrable_comp hφQ.1, l.integrable_comp hφQ.2⟩
  have hzero : (∫ s in a..b, l (deriv φ s • P s)) +
      (∫ s in a..b, l (φ s • Q s)) = 0 := by
    rw [← intervalIntegral.integral_add hDPscalar hQscalar]
    simpa only [l, innerSL_apply_apply, inner_smul_right] using hstationary z
  change l (∫ s in a..b, deriv φ s • P s) = l (-(∫ s in a..b, φ s • Q s))
  rw [map_neg, ← l.intervalIntegral_comp_comm hDP, ← l.intervalIntegral_comp_comm hφQ]
  linarith

theorem weak_momentum_of_chart_stationarity {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (w : ℝ → F) (hw : MemLp w 2 (volume.restrict (Icc a b)))
    (G : ℝ → F →L[ℝ] F →L[ℝ] ℝ)
    (DG : ℝ → F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) (DV : ℝ → F →L[ℝ] ℝ)
    (hG : ContinuousOn G (Icc a b)) (hDG : ContinuousOn DG (Icc a b))
    (hDV : ContinuousOn DV (Icc a b))
    (hbound : ∀ s ∈ Icc a b, ‖G s‖ ≤ C ∧ ‖DG s‖ ≤ C ∧ ‖DV s‖ ≤ C)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hstationary : ∀ z : F,
      (∫ s in a..b, DG s (φ s • z) (w s) (w s) / 2 +
        G s (w s) (deriv φ s • z) + DV s (φ s • z)) = 0) :
    IntervalIntegrable (fun s ↦ chartMomentumVector (G s) (w s)) volume a b ∧
    IntervalIntegrable (fun s ↦ chartForceVector (DG s) (DV s) (w s)) volume a b ∧
    (∫ s in a..b, deriv φ s • chartMomentumVector (G s) (w s)) =
      -(∫ s in a..b, φ s • chartForceVector (DG s) (DV s) (w s)) := by
  obtain ⟨hP, hQ⟩ := chart_momentum_force_intervalIntegrable hab hC w hw G DG DV
    hG hDG hDV hbound
  refine ⟨hP, hQ, weak_momentum_of_scalar_stationarity _ _ hP hQ φ hφ ?_⟩
  intro z
  calc
    _ = ∫ s in a..b, DG s (φ s • z) (w s) (w s) / 2 +
        G s (w s) (deriv φ s • z) + DV s (φ s • z) := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [chartMomentumVector_inner, chartForceVector_inner]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    _ = 0 := hstationary z

end InnerProduct

end PoincareConjecture.ReducedLengthMinimum.Variational
