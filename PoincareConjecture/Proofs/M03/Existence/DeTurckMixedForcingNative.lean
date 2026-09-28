import PoincareConjecture.Proofs.M03.Existence.DeTurckMetricProducerNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetAffineNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckSourceJetNative

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise

namespace PoincareConjecture.DeTurckMetricProducerNative

open DeTurckNative DeTurckQuasilinearEstimateNative DeTurckInverseCompositionNative
open SpectralHeatNative TimeL2BilinearNative

universe u v w z

variable {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [IsFiniteMeasure μ]
  {V W : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type z} [NormedAddCommGroup H] [NormedSpace ℝ H] {T : ℝ}

def spatialCoefficientAction (B : W →L[ℝ] E →L[ℝ] H) :
    C(M, W) →L[ℝ] Lp E 2 μ →L[ℝ] Lp H 2 μ :=
  (B.holderL μ (⊤ : ENNReal) 2 2).comp (ContinuousMap.toLp (⊤ : ENNReal) μ ℝ)

set_option backward.isDefEq.respectTransparency false in
theorem spatialCoefficientAction_coe (B : W →L[ℝ] E →L[ℝ] H)
    (A : C(M, W)) (Q : Lp E 2 μ) :
    spatialCoefficientAction μ B A Q =ᵐ[μ] fun x => B (A x) (Q x) := by
  filter_upwards [B.coeFn_holder (r := (2 : ENNReal))
    (ContinuousMap.toLp (⊤ : ENNReal) μ ℝ A) Q,
    ContinuousMap.coeFn_toLp (p := (⊤ : ENNReal)) (μ := μ) (𝕜 := ℝ) A] with x hx hA
  change spatialCoefficientAction μ B A Q x =
    B ((ContinuousMap.toLp (⊤ : ENNReal) μ ℝ A) x) (Q x) at hx
  rw [hA] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_coefficient_forcing_extension (hT : 0 ≤ T)
    {U : Set V} (hU : IsOpen U) (f : V → W)
    (hf : ∀ z ∈ U, ContDiffAt ℝ ∞ f z) (B : W →L[ℝ] E →L[ℝ] H)
    (u : TimePath C(M, V) T) (hu : ∀ t x, u t x ∈ U) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : (TimePath C(M, V) T × TimeL2 (Lp E 2 μ) T) → TimeL2 (Lp H 2 μ) T,
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon → ∀ Q : TimeL2 (Lp E 2 μ) T,
        ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          Phi (v, Q) t =ᵐ[μ] fun x => B (f (v ⟨t, ht⟩ x)) (Q t x) := by
  have hS : IsCompact (range u.uncurry) := isCompact_range u.uncurry.continuous
  obtain ⟨fExt, hfExt, O, hO, hSO, hEq⟩ := exists_contDiff_extension_near_compact hS hU
    (by rintro _ ⟨⟨t, x⟩, rfl⟩; exact hu t x) f hf
  obtain ⟨epsilon, hepsilon, hthick⟩ := hS.exists_thickening_subset_open hO hSO
  let G : C(C(M, V), C(M, W)) := ⟨fun v => fExt.comp v, fExt.continuous_postcomp⟩
  have hG : ContDiff ℝ ∞ G :=
    ContinuousPathCompositionNative.contDiff_postcomp M fExt hfExt
  let coefficient : TimePath C(M, V) T → TimePath C(M, W) T := fun v => G.comp v
  have hcoefficient : ContDiff ℝ ∞ coefficient :=
    ContinuousPathCompositionNative.contDiff_postcomp (Icc (0 : ℝ) T) G hG
  let P := productOperator hT (spatialCoefficientAction μ B)
  refine ⟨epsilon, hepsilon, fun z => P (coefficient z.1) z.2,
    (P.contDiff.comp (hcoefficient.comp contDiff_fst)).clm_apply contDiff_snd, ?_⟩
  intro v hv Q
  filter_upwards [product_ae_eq_on_interval hT (spatialCoefficientAction μ B)
    (coefficient v) Q] with t ht
  intro htmem
  change P (coefficient v) Q t =ᵐ[μ] _
  rw [show P (coefficient v) Q t = spatialCoefficientAction μ B
    (coefficient v ⟨t, htmem⟩) (Q t) from ht htmem]
  filter_upwards [spatialCoefficientAction_coe μ B (coefficient v ⟨t, htmem⟩) (Q t)]
    with x hx
  rw [hx]
  change B (fExt (v ⟨t, htmem⟩ x)) (Q t x) = _
  rw [hEq (hthick (mem_thickening_iff.mpr
    ⟨u ⟨t, htmem⟩ x,
      mem_range_self (f := u.uncurry) ((⟨t, htmem⟩ : Icc (0 : ℝ) T), x), by
      rw [dist_eq_norm]
      exact ((v ⟨t, htmem⟩ - u ⟨t, htmem⟩).norm_coe_le_norm x).trans_lt
        (((v - u).norm_coe_le_norm ⟨t, htmem⟩).trans_lt hv)⟩))]

def augmentHighInput (Q : TimeL2 (Lp E 2 μ) T) : TimeL2 (Lp (E × ℝ) 2 μ) T :=
  ((ContinuousLinearMap.inl ℝ E ℝ).compLpL 2 μ).compLpL 2 (timeMeasure T) Q +
    (memLp_const ((memLp_const ((0 : E), (1 : ℝ))).toLp
      (fun _ : M => ((0 : E), (1 : ℝ))))).toLp
      (fun _ : ℝ => (memLp_const ((0 : E), (1 : ℝ))).toLp
        (fun _ : M => ((0 : E), (1 : ℝ))))

theorem contDiff_augmentHighInput :
    ContDiff ℝ ∞ (augmentHighInput (E := E) (T := T) μ) :=
  (((ContinuousLinearMap.inl ℝ E ℝ).compLpL 2 μ).compLpL 2
    (timeMeasure T)).contDiff.add contDiff_const

theorem augmentHighInput_coe (Q : TimeL2 (Lp E 2 μ) T) :
    ∀ᵐ t ∂timeMeasure T, augmentHighInput μ Q t =ᵐ[μ] fun x => (Q t x, (1 : ℝ)) := by
  let J := (ContinuousLinearMap.inl ℝ E ℝ).compLpL 2 μ
  let c : Lp (E × ℝ) 2 μ := (memLp_const ((0 : E), (1 : ℝ))).toLp (fun _ => (0, 1))
  let C : TimeL2 (Lp (E × ℝ) 2 μ) T := (memLp_const c).toLp (fun _ => c)
  filter_upwards [J.coeFn_compLpL (p := 2) (μ := timeMeasure T) Q,
    (memLp_const c : MemLp (fun _ : ℝ => c) 2 (timeMeasure T)).coeFn_toLp,
    Lp.coeFn_add (J.compLpL 2 (timeMeasure T) Q) C] with t hJ hC hadd
  change (J.compLpL 2 (timeMeasure T) Q + C) t =ᵐ[μ] _
  rw [hadd, Pi.add_apply, hJ, hC]
  filter_upwards [(ContinuousLinearMap.inl ℝ E ℝ).coeFn_compLpL (Q t),
    (memLp_const ((0 : E), (1 : ℝ)) :
      MemLp (fun _ : M => ((0 : E), (1 : ℝ))) 2 μ).coeFn_toLp,
    Lp.coeFn_add (J (Q t)) c] with x hQ hc hx
  change J (Q t) x = (Q t x, (0 : ℝ)) at hQ
  change c x = ((0 : E), (1 : ℝ)) at hc
  rw [hx, Pi.add_apply, hQ, hc]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

variable {n : ℕ}

def mixedLowerJetOperator :
    (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) →L[ℝ]
      (MetricSecondJet n × ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ((ContinuousLinearMap.compL ℝ (MetricSecondJet n × ℝ)
    (MetricSecondJet n) (Matrix (Fin n) (Fin n) ℝ)).flip
    (ContinuousLinearMap.fst ℝ (MetricSecondJet n) ℝ)).comp
      (lowerJetContractionOperator.comp
        (ContinuousLinearMap.fst ℝ (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ))) +
  ((ContinuousLinearMap.compL ℝ (MetricSecondJet n × ℝ)
    ℝ (Matrix (Fin n) (Fin n) ℝ)).flip
    (ContinuousLinearMap.snd ℝ (MetricSecondJet n) ℝ)).comp
      ((ContinuousLinearMap.lsmul ℝ ℝ (E := Matrix (Fin n) (Fin n) ℝ)).flip.comp
        (ContinuousLinearMap.snd ℝ (Matrix (Fin n) (Fin n) ℝ) (Matrix (Fin n) (Fin n) ℝ)))

@[simp] theorem mixedLowerJetOperator_apply
    (A L : Matrix (Fin n) (Fin n) ℝ) (Q : MetricSecondJet n) (c : ℝ) :
    mixedLowerJetOperator (A, L) (Q, c) = lowerJetContraction A Q + c • L := rfl

set_option backward.isDefEq.respectTransparency false in

theorem exists_smooth_mixed_forcing_extension (hT : 0 ≤ T)
    (u : TimePath C(M, Matrix (Fin n) (Fin n) ℝ ×
      ChartState (n := n) × MetricLowerJet n) T)
    (h0 : ∀ t x, (u t x).1.PosDef)
    (hB : ∀ t x, (u t x).2.1.1.PosDef) (hg : ∀ t x, (u t x).2.2.1.PosDef) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : (TimePath C(M, Matrix (Fin n) (Fin n) ℝ ×
        ChartState (n := n) × MetricLowerJet n) T ×
        TimeL2 (Lp (MetricSecondJet n) 2 μ) T) →
        TimeL2 (Lp (Matrix (Fin n) (Fin n) ℝ) 2 μ) T,
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon →
        ∀ Q : TimeL2 (Lp (MetricSecondJet n) 2 μ) T,
        ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          Phi (v, Q) t =ᵐ[μ] fun x =>
            lowerJetContraction ((v ⟨t, ht⟩ x).2.2.1⁻¹ - (v ⟨t, ht⟩ x).1⁻¹) (Q t x) +
            lowerPerturbationSource (chartStateJet (v ⟨t, ht⟩ x).2.1)
              (v ⟨t, ht⟩ x).2.2 := by
  let V := Matrix (Fin n) (Fin n) ℝ × ChartState (n := n) × MetricLowerJet n
  let U : Set V := {z | z.1.det ≠ 0 ∧ z.2.1.1.det ≠ 0 ∧ z.2.2.1.det ≠ 0}
  let f : V → Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ :=
    fun z => (z.2.2.1⁻¹ - z.1⁻¹, lowerPerturbationSource (chartStateJet z.2.1) z.2.2)
  have hU : IsOpen U :=
    (isOpen_ne_fun continuous_fst.matrix_det continuous_const).inter
      ((isOpen_ne_fun continuous_snd.fst.fst.matrix_det continuous_const).inter
        (isOpen_ne_fun continuous_snd.snd.fst.matrix_det continuous_const))
  have hf (z : V) (hz : z ∈ U) : ContDiffAt ℝ ∞ f z := by
    have hp : ContDiffAt ℝ ∞ (fun q : V => matrixInverseEntries q.2.2.1) z :=
      (contDiffAt_matrixInverseEntries_infty _ hz.2.2).comp
        (f := fun q : Matrix (Fin n) (Fin n) ℝ × ChartState (n := n) × MetricLowerJet n =>
          q.2.2.1) (g := matrixInverseEntries) z (by fun_prop)
    have hfixed : ContDiffAt ℝ ∞ (fun q : V => matrixInverseEntries q.1) z :=
      (contDiffAt_matrixInverseEntries_infty _ hz.1).comp
        (f := fun q : Matrix (Fin n) (Fin n) ℝ × ChartState (n := n) × MetricLowerJet n =>
          q.1) (g := matrixInverseEntries) z (by fun_prop)
    exact (hp.sub hfixed).prodMk
      ((contDiffAt_jointLowerPerturbationSource_of_det_ne_zero z.2 hz.2.1 hz.2.2).comp
        (f := fun q : Matrix (Fin n) (Fin n) ℝ × ChartState (n := n) × MetricLowerJet n =>
          q.2) z (by fun_prop))
  obtain ⟨epsilon, hepsilon, Psi, hPsi, hEq⟩ :=
    exists_smooth_coefficient_forcing_extension μ hT hU f hf mixedLowerJetOperator u
      (fun t x => ⟨((u t x).1.isUnit_iff_isUnit_det.mp (h0 t x).isUnit).ne_zero,
        ((u t x).2.1.1.isUnit_iff_isUnit_det.mp (hB t x).isUnit).ne_zero,
        ((u t x).2.2.1.isUnit_iff_isUnit_det.mp (hg t x).isUnit).ne_zero⟩)
  refine ⟨epsilon, hepsilon, fun z => Psi (z.1, augmentHighInput μ z.2),
    hPsi.comp (contDiff_fst.prodMk ((contDiff_augmentHighInput μ).comp contDiff_snd)), ?_⟩
  intro v hv Q
  filter_upwards [hEq v hv (augmentHighInput μ Q), augmentHighInput_coe μ Q] with t ht hQ
  intro htmem
  filter_upwards [ht htmem, hQ] with x hx hQx
  rw [hx, hQx]
  simp only [f, mixedLowerJetOperator_apply, one_smul]
  rfl

def fixedGeneratorInput (b0 : C(M, Matrix (Fin n) (Fin n) ℝ))
    (v : TimePath C(M, ChartState (n := n) × MetricLowerJet n) T) :
    TimePath C(M, Matrix (Fin n) (Fin n) ℝ ×
      ChartState (n := n) × MetricLowerJet n) T :=
  ((ContinuousLinearMap.inr ℝ (Matrix (Fin n) (Fin n) ℝ)
    (ChartState (n := n) × MetricLowerJet n)).compLeftContinuous ℝ M).compLeftContinuous
      ℝ (Icc (0 : ℝ) T) v +
  ContinuousMap.const (Icc (0 : ℝ) T)
    ((ContinuousLinearMap.inl ℝ (Matrix (Fin n) (Fin n) ℝ)
      (ChartState (n := n) × MetricLowerJet n)).compLeftContinuous ℝ M b0)

@[simp] theorem fixedGeneratorInput_apply (b0 : C(M, Matrix (Fin n) (Fin n) ℝ))
    (v : TimePath C(M, ChartState (n := n) × MetricLowerJet n) T)
    (t : Icc (0 : ℝ) T) (x : M) : fixedGeneratorInput b0 v t x = (b0 x, v t x) := by
  change (0, v t x) + (b0 x, 0) = (b0 x, v t x)
  simp

theorem contDiff_fixedGeneratorInput (b0 : C(M, Matrix (Fin n) (Fin n) ℝ)) :
    ContDiff ℝ ∞ (fixedGeneratorInput (T := T) b0) := by
  let L : TimePath C(M, ChartState (n := n) × MetricLowerJet n) T →L[ℝ]
      TimePath C(M, Matrix (Fin n) (Fin n) ℝ × ChartState (n := n) × MetricLowerJet n) T :=
    ((ContinuousLinearMap.inr ℝ (Matrix (Fin n) (Fin n) ℝ)
    (ChartState (n := n) × MetricLowerJet n)).compLeftContinuous ℝ M).compLeftContinuous
      ℝ (Icc (0 : ℝ) T)
  let c := ContinuousMap.const (Icc (0 : ℝ) T)
    ((ContinuousLinearMap.inl ℝ (Matrix (Fin n) (Fin n) ℝ)
      (ChartState (n := n) × MetricLowerJet n)).compLeftContinuous ℝ M b0)
  change ContDiff ℝ ∞ (fun v => L v + c)
  have hL : ContDiff ℝ ∞
      (fun v : TimePath C(M, ChartState (n := n) × MetricLowerJet n) T => L v) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := TimePath C(M, ChartState (n := n) × MetricLowerJet n) T)
      (F := TimePath C(M,
        Matrix (Fin n) (Fin n) ℝ × ChartState (n := n) × MetricLowerJet n) T)
      (n := ∞) L
  exact hL.add contDiff_const

theorem norm_fixedGeneratorInput_sub_le (b0 : C(M, Matrix (Fin n) (Fin n) ℝ))
    (v u : TimePath C(M, ChartState (n := n) × MetricLowerJet n) T) :
    ‖fixedGeneratorInput b0 v - fixedGeneratorInput b0 u‖ ≤ ‖v - u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg (v - u))).mpr
  intro t
  apply (ContinuousMap.norm_le _ (norm_nonneg (v - u))).mpr
  intro x
  change ‖fixedGeneratorInput b0 v t x - fixedGeneratorInput b0 u t x‖ ≤ ‖v - u‖
  rw [fixedGeneratorInput_apply, fixedGeneratorInput_apply]
  change max ‖b0 x - b0 x‖ ‖v t x - u t x‖ ≤ ‖v - u‖
  simp only [sub_self, norm_zero, max_eq_right (norm_nonneg _)]
  exact ((v t - u t).norm_coe_le_norm x).trans ((v - u).norm_coe_le_norm t)

set_option backward.isDefEq.respectTransparency false in

theorem exists_smooth_fixed_generator_forcing_extension (hT : 0 ≤ T)
    (b0 : C(M, Matrix (Fin n) (Fin n) ℝ)) (hb0 : ∀ x, (b0 x).PosDef)
    (u : TimePath C(M, ChartState (n := n) × MetricLowerJet n) T)
    (hB : ∀ t x, (u t x).1.1.PosDef) (hg : ∀ t x, (u t x).2.1.PosDef) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : (TimePath C(M, ChartState (n := n) × MetricLowerJet n) T ×
        TimeL2 (Lp (MetricSecondJet n) 2 μ) T) →
        TimeL2 (Lp (Matrix (Fin n) (Fin n) ℝ) 2 μ) T,
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon →
        ∀ Q : TimeL2 (Lp (MetricSecondJet n) 2 μ) T,
        ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          Phi (v, Q) t =ᵐ[μ] fun x =>
            lowerJetContraction ((v ⟨t, ht⟩ x).2.1⁻¹ - (b0 x)⁻¹) (Q t x) +
            lowerPerturbationSource (chartStateJet (v ⟨t, ht⟩ x).1)
              (v ⟨t, ht⟩ x).2 := by
  obtain ⟨epsilon, hepsilon, Psi, hPsi, hEq⟩ :=
    exists_smooth_mixed_forcing_extension μ hT (fixedGeneratorInput b0 u)
      (by intro t x; simpa only [fixedGeneratorInput_apply] using hb0 x)
      (by intro t x; simpa only [fixedGeneratorInput_apply] using hB t x)
      (by intro t x; simpa only [fixedGeneratorInput_apply] using hg t x)
  refine ⟨epsilon, hepsilon, fun z => Psi (fixedGeneratorInput b0 z.1, z.2),
    hPsi.comp (((contDiff_fixedGeneratorInput b0).comp contDiff_fst).prodMk contDiff_snd), ?_⟩
  intro v hv Q
  exact (hEq (fixedGeneratorInput b0 v)
    ((norm_fixedGeneratorInput_sub_le b0 v u).trans_lt hv) Q).mono
      (fun t ht htmem => by simpa only [fixedGeneratorInput_apply] using ht htmem)

open DeTurckRationalJetNative DeTurckJetAffineNative

def finiteJetAffineOperator : ((E →L[ℝ] ℝ) × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (E × ℝ) E ℝ).flip
    (ContinuousLinearMap.fst ℝ E ℝ)).comp (ContinuousLinearMap.fst ℝ (E →L[ℝ] ℝ) ℝ) +
  ((ContinuousLinearMap.compL ℝ (E × ℝ) ℝ ℝ).flip
    (ContinuousLinearMap.snd ℝ E ℝ)).comp
      ((ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)).flip.comp
        (ContinuousLinearMap.snd ℝ (E →L[ℝ] ℝ) ℝ))

@[simp] theorem finiteJetAffineOperator_apply (L : E →L[ℝ] ℝ) (c : ℝ)
    (Q : E) (a : ℝ) : finiteJetAffineOperator (L, c) (Q, a) = L Q + a * c := rfl

variable {iota : Type v}

def augmentSpatialHighInput (Q : Lp E 2 μ) : Lp (E × ℝ) 2 μ :=
  (ContinuousLinearMap.inl ℝ E ℝ).compLpL 2 μ Q +
    (memLp_const ((0 : E), (1 : ℝ))).toLp (fun _ : M => ((0 : E), (1 : ℝ)))

theorem contDiff_augmentSpatialHighInput :
    ContDiff ℝ ∞ (augmentSpatialHighInput (E := E) μ) :=
  ((ContinuousLinearMap.inl ℝ E ℝ).compLpL 2 μ).contDiff.add contDiff_const

theorem augmentSpatialHighInput_coe (Q : Lp E 2 μ) :
    augmentSpatialHighInput μ Q =ᵐ[μ] fun x => (Q x, (1 : ℝ)) := by
  let c : Lp (E × ℝ) 2 μ :=
    (memLp_const ((0 : E), (1 : ℝ))).toLp (fun _ : M => ((0 : E), (1 : ℝ)))
  filter_upwards [(ContinuousLinearMap.inl ℝ E ℝ).coeFn_compLpL Q,
    (memLp_const ((0 : E), (1 : ℝ)) :
      MemLp (fun _ : M => ((0 : E), (1 : ℝ))) 2 μ).coeFn_toLp,
    Lp.coeFn_add ((ContinuousLinearMap.inl ℝ E ℝ).compLpL 2 μ Q) c] with x hQ hc hadd
  change ((ContinuousLinearMap.inl ℝ E ℝ).compLpL 2 μ Q + c) x = _
  change c x = ((0 : E), (1 : ℝ)) at hc
  rw [hadd, Pi.add_apply, hQ, hc]
  simp only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add]

abbrev FiniteSpatialJetInput (p : Expr iota n) (m : ℕ) :=
  C(M, LowAtom p m → ℝ) × Lp (HighAtom p m → ℝ) 2 μ

def finiteSpatialJetCoefficient (p : Expr iota n) (m : ℕ) :
    C(LowAtom p m → ℝ, ((HighAtom p m → ℝ) →L[ℝ] ℝ) × ℝ) :=
  ⟨fun low => (finiteLinearPart p m low, finiteConstantPart p m low),
    ((contDiff_finiteLinearPart p m).prodMk (contDiff_finiteConstantPart p m)).continuous⟩

theorem contDiff_finiteSpatialJetCoefficient (p : Expr iota n) (m : ℕ) :
    ContDiff ℝ ∞ (finiteSpatialJetCoefficient p m) :=
  (contDiff_finiteLinearPart p m).prodMk (contDiff_finiteConstantPart p m)

def finiteSpatialJetAction (p : Expr iota n) (m : ℕ)
    (z : FiniteSpatialJetInput μ p m) : Lp ℝ 2 μ :=
  spatialCoefficientAction μ finiteJetAffineOperator
    ((finiteSpatialJetCoefficient p m).comp z.1) (augmentSpatialHighInput μ z.2)

theorem contDiff_finiteSpatialJetAction (p : Expr iota n) (m : ℕ) :
    ContDiff ℝ ∞ (finiteSpatialJetAction μ p m) := by
  have hcoefficient := ContinuousPathCompositionNative.contDiff_postcomp M
    (finiteSpatialJetCoefficient p m) (contDiff_finiteSpatialJetCoefficient p m)
  exact ((spatialCoefficientAction μ
    (finiteJetAffineOperator (E := HighAtom p m → ℝ))).contDiff.comp
      (hcoefficient.comp contDiff_fst)).clm_apply
    ((contDiff_augmentSpatialHighInput μ).comp contDiff_snd)

theorem finiteSpatialJetAction_coe (p : Expr iota n) (m : ℕ)
    (z : FiniteSpatialJetInput μ p m) :
    finiteSpatialJetAction μ p m z =ᵐ[μ] fun x =>
      finiteConstantPart p m (z.1 x) + finiteLinearPart p m (z.1 x) (z.2 x) := by
  filter_upwards [spatialCoefficientAction_coe μ finiteJetAffineOperator
    ((finiteSpatialJetCoefficient p m).comp z.1) (augmentSpatialHighInput μ z.2),
    augmentSpatialHighInput_coe μ z.2] with x hx hQ
  change finiteSpatialJetAction μ p m z x = _ at hx
  rw [hx, hQ]
  change finiteLinearPart p m (z.1 x) (z.2 x) + 1 * finiteConstantPart p m (z.1 x) = _
  rw [one_mul, add_comm]

theorem finiteSpatialJetAction_ae_eq_eval (p : Expr iota n) (m : ℕ)
    (hp : p.degree ≤ 2 * m) (z : FiniteSpatialJetInput μ p m)
    (values : M → Atom iota n → ℝ)
    (hLow : ∀ x, (fun a : LowAtom p m => values x a.val.val) = z.1 x)
    (hHigh : (fun x => fun a : HighAtom p m => values x a.val.val) =ᵐ[μ] z.2) :
    finiteSpatialJetAction μ p m z =ᵐ[μ] fun x => p.eval (values x) := by
  filter_upwards [finiteSpatialJetAction_coe μ p m z, hHigh] with x hx hQ
  rw [hx, ← hLow x, ← hQ]
  exact (eval_eq_finiteParts p m hp (values x)).symm

def tracePathL2 (hT : 0 ≤ T) : TimePath E T →L[ℝ] TimeL2 E T :=
  (productOperator hT (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip).flip
    ((memLp_const (1 : ℝ)).toLp (fun _ : ℝ => (1 : ℝ)))

theorem tracePathL2_ae_eq (hT : 0 ≤ T) (A : TimePath E T) :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      tracePathL2 hT A t = A ⟨t, ht⟩ := by
  let c : TimeL2 ℝ T := (memLp_const (1 : ℝ)).toLp (fun _ : ℝ => (1 : ℝ))
  filter_upwards [product_ae_eq_on_interval hT
    (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip A c,
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (timeMeasure T)).coeFn_toLp]
    with t ht hc
  intro htmem
  change product hT (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip A c t = _
  rw [ht htmem, hc]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, one_smul]

theorem norm_tracePathL2_apply_le (hT : 0 ≤ T) (A : TimePath E T) :
    ‖tracePathL2 hT A‖ ≤ Real.sqrt T * ‖A‖ := by
  let c : TimeL2 ℝ T := (memLp_const (1 : ℝ)).toLp (fun _ : ℝ => (1 : ℝ))
  have hmeasure : (timeMeasure T Set.univ).toReal = T := by
    simp only [timeMeasure, Measure.restrict_apply_univ, Real.volume_Ioc,
      sub_zero, ENNReal.toReal_ofReal hT]
  have hc : ‖c‖ = Real.sqrt T := by
    change ‖Lp.const 2 (timeMeasure T) (1 : ℝ)‖ = Real.sqrt T
    rw [Lp.norm_const' (p := (2 : ENNReal)) (μ := timeMeasure T) (c := (1 : ℝ))
      (by norm_num) (by norm_num)]
    simp only [norm_one, one_mul, measureReal_def,
      ENNReal.toReal_ofNat, hmeasure, Real.sqrt_eq_rpow]
  have hB : ‖(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_flip]
    exact ContinuousLinearMap.opNorm_lsmul_le
  calc
    ‖tracePathL2 hT A‖ ≤
        ‖(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip‖ * ‖A‖ * ‖c‖ :=
      norm_product_le hT (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip A c
    _ ≤ 1 * ‖A‖ * Real.sqrt T := by
      rw [hc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hB (norm_nonneg A)) (Real.sqrt_nonneg T)
    _ = Real.sqrt T * ‖A‖ := by ring

theorem norm_tracePathL2_le (hT : 0 ≤ T) :
    ‖tracePathL2 (E := E) hT‖ ≤ Real.sqrt T :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg T) (norm_tracePathL2_apply_le hT)

def finiteJetTraceForcing (hT : 0 ≤ T) (p : Expr iota n) (m : ℕ)
    (z : TimePath (FiniteSpatialJetInput μ p m) T) : TimeL2 (Lp ℝ 2 μ) T :=
  tracePathL2 hT ((⟨finiteSpatialJetAction μ p m,
    (contDiff_finiteSpatialJetAction μ p m).continuous⟩ :
      C(FiniteSpatialJetInput μ p m, Lp ℝ 2 μ)).comp z)

theorem contDiff_finiteJetTraceForcing (hT : 0 ≤ T) (p : Expr iota n) (m : ℕ) :
    ContDiff ℝ ∞ (finiteJetTraceForcing μ hT p m) := by
  let e : ULift.{v} (Lp ℝ 2 μ) ≃L[ℝ] Lp ℝ 2 μ := ContinuousLinearEquiv.ulift
  let f : C(FiniteSpatialJetInput μ p m, ULift.{v} (Lp ℝ 2 μ)) :=
    ⟨fun q => e.symm (finiteSpatialJetAction μ p m q),
      e.symm.continuous.comp (contDiff_finiteSpatialJetAction μ p m).continuous⟩
  have hf : ContDiff ℝ ∞ f :=
    e.symm.contDiff.comp (contDiff_finiteSpatialJetAction μ p m)
  let down : TimePath (ULift.{v} (Lp ℝ 2 μ)) T →L[ℝ] TimePath (Lp ℝ 2 μ) T :=
    e.toContinuousLinearMap.compLeftContinuous ℝ (Icc (0 : ℝ) T)
  change ContDiff ℝ ∞ (fun z : TimePath (FiniteSpatialJetInput μ p m) T =>
    tracePathL2 hT (down (f.comp z)))
  exact (tracePathL2 (E := Lp ℝ 2 μ) hT).contDiff.comp
    (down.contDiff.comp
      (ContinuousPathCompositionNative.contDiff_postcomp (Icc (0 : ℝ) T) f hf))

theorem finiteJetTraceForcing_ae_eq_eval (hT : 0 ≤ T) (p : Expr iota n) (m : ℕ)
    (hp : p.degree ≤ 2 * m) (z : TimePath (FiniteSpatialJetInput μ p m) T)
    (values : ℝ → M → Atom iota n → ℝ)
    (hLow : ∀ t (ht : t ∈ Icc (0 : ℝ) T) x,
      (fun a : LowAtom p m => values t x a.val.val) = (z ⟨t, ht⟩).1 x)
    (hHigh : ∀ t (ht : t ∈ Icc (0 : ℝ) T),
      (fun x => fun a : HighAtom p m => values t x a.val.val) =ᵐ[μ] (z ⟨t, ht⟩).2) :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      finiteJetTraceForcing μ hT p m z t =ᵐ[μ] fun x => p.eval (values t x) := by
  let f : C(FiniteSpatialJetInput μ p m, Lp ℝ 2 μ) :=
    ⟨finiteSpatialJetAction μ p m, (contDiff_finiteSpatialJetAction μ p m).continuous⟩
  filter_upwards [tracePathL2_ae_eq hT (f.comp z)] with t ht
  intro htmem
  change tracePathL2 hT (f.comp z) t =ᵐ[μ] _
  rw [ht htmem]
  exact finiteSpatialJetAction_ae_eq_eval μ p m hp (z ⟨t, htmem⟩)
    (values t) (hLow t htmem) (hHigh t htmem)

theorem exists_finiteJetTraceForcing_lipschitz_bound (p : Expr iota n) (m : ℕ)
    (u : FiniteSpatialJetInput μ p m) :
    ∃ K : NNReal, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (S : ℝ) (hS : 0 ≤ S) (z w : TimePath (FiniteSpatialJetInput μ p m) S),
        (∀ t, z t ∈ Metric.ball u epsilon) →
        (∀ t, w t ∈ Metric.ball u epsilon) →
        ‖finiteJetTraceForcing μ hS p m z - finiteJetTraceForcing μ hS p m w‖ ≤
          Real.sqrt S * (K : ℝ) * ‖z - w‖ := by
  have hf : ContDiffAt ℝ 1 (finiteSpatialJetAction μ p m) u :=
    ((contDiff_finiteSpatialJetAction μ p m).of_le (by simp)).contDiffAt
  obtain ⟨K, s, hs, hK⟩ := hf.exists_lipschitzOnWith
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨K, epsilon, hepsilon, ?_⟩
  intro S hS z w hz hw
  let f : C(FiniteSpatialJetInput μ p m, Lp ℝ 2 μ) :=
    ⟨finiteSpatialJetAction μ p m, (contDiff_finiteSpatialJetAction μ p m).continuous⟩
  have hpath : ‖f.comp z - f.comp w‖ ≤ (K : ℝ) * ‖z - w‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    have hpoint := (lipschitzOnWith_iff_dist_le_mul.mp hK)
      (z t) (hball (hz t)) (w t) (hball (hw t))
    simp only [dist_eq_norm] at hpoint
    exact hpoint.trans (mul_le_mul_of_nonneg_left
      ((z - w).norm_coe_le_norm t) K.2)
  change ‖tracePathL2 hS (f.comp z) - tracePathL2 hS (f.comp w)‖ ≤ _
  rw [← map_sub]
  exact (norm_tracePathL2_apply_le hS (f.comp z - f.comp w)).trans
    ((mul_le_mul_of_nonneg_left hpath (Real.sqrt_nonneg S)).trans_eq (by ring))

theorem exists_smooth_finite_jet_forcing_extension (hT : 0 ≤ T) (p : Expr iota n) (m : ℕ)
    (u : TimePath C(M, LowAtom p m → ℝ) T) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : (TimePath C(M, LowAtom p m → ℝ) T ×
        TimeL2 (Lp (HighAtom p m → ℝ) 2 μ) T) → TimeL2 (Lp ℝ 2 μ) T,
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon →
        ∀ Q : TimeL2 (Lp (HighAtom p m → ℝ) 2 μ) T,
        ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          Phi (v, Q) t =ᵐ[μ] fun x => finiteConstantPart p m (v ⟨t, ht⟩ x) +
            finiteLinearPart p m (v ⟨t, ht⟩ x) (Q t x) := by
  let f : (LowAtom p m → ℝ) → ((HighAtom p m → ℝ) →L[ℝ] ℝ) × ℝ :=
    fun low => (finiteLinearPart p m low, finiteConstantPart p m low)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_finiteLinearPart p m).prodMk (contDiff_finiteConstantPart p m)
  obtain ⟨epsilon, hepsilon, Psi, hPsi, hEq⟩ :=
    exists_smooth_coefficient_forcing_extension μ hT isOpen_univ f
      (fun _ _ => hf.contDiffAt) finiteJetAffineOperator u (fun _ _ => mem_univ _)
  refine ⟨epsilon, hepsilon, fun z => Psi (z.1, augmentHighInput μ z.2),
    hPsi.comp (contDiff_fst.prodMk ((contDiff_augmentHighInput μ).comp contDiff_snd)), ?_⟩
  intro v hv Q
  filter_upwards [hEq v hv (augmentHighInput μ Q), augmentHighInput_coe μ Q] with t ht hQ
  intro htmem
  filter_upwards [ht htmem, hQ] with x hx hQx
  rw [hx, hQx]
  change finiteLinearPart p m (v ⟨t, htmem⟩ x) (Q t x) +
    1 * finiteConstantPart p m (v ⟨t, htmem⟩ x) = _
  rw [one_mul, add_comm]

theorem finite_jet_forcing_ae_eq_eval (p : Expr iota n) (m : ℕ) (hp : p.degree ≤ 2 * m)
    (v : TimePath C(M, LowAtom p m → ℝ) T) (Q : TimeL2 (Lp (HighAtom p m → ℝ) 2 μ) T)
    (values : ℝ → M → Atom iota n → ℝ)
    (hLow : ∀ t (ht : t ∈ Icc (0 : ℝ) T) x,
      (fun a : LowAtom p m => values t x a.val.val) = v ⟨t, ht⟩ x)
    (hHigh : ∀ᵐ t ∂timeMeasure T, ∀ _ht : t ∈ Icc (0 : ℝ) T,
      (fun x => fun a : HighAtom p m => values t x a.val.val) =ᵐ[μ] Q t) :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      (fun x => finiteConstantPart p m (v ⟨t, ht⟩ x) +
        finiteLinearPart p m (v ⟨t, ht⟩ x) (Q t x)) =ᵐ[μ]
        (fun x => p.eval (values t x)) := by
  filter_upwards [hHigh] with t ht
  intro htmem
  filter_upwards [ht htmem] with x hx
  rw [← hx, ← hLow t htmem x]
  exact (eval_eq_finiteParts p m hp (values t x)).symm

section NativeLowerSource

open TensorProbeNative DeTurckSourceJetNative
open scoped Manifold

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [Fintype iota]

theorem exists_smooth_ordered_lower_forcing_extension (hT : 0 ≤ T)
    (F : iota → SmoothField (n := n) (M := M)) (e : Fin n → iota)
    (i j : Fin n) (word : List iota) (r : ℕ) (hword : word.length ≤ 2 * r)
    (u : TimePath C(M,
      LowAtom ((lowerPerturbationExpr e i j).orderedDerivative word) (r + 1) → ℝ) T) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : (TimePath C(M,
        LowAtom ((lowerPerturbationExpr e i j).orderedDerivative word) (r + 1) → ℝ) T ×
        TimeL2 (Lp
          (HighAtom ((lowerPerturbationExpr e i j).orderedDerivative word) (r + 1) → ℝ)
          2 μ) T) → TimeL2 (Lp ℝ 2 μ) T,
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon →
        ∀ Q : TimeL2 (Lp
          (HighAtom ((lowerPerturbationExpr e i j).orderedDerivative word) (r + 1) → ℝ)
          2 μ) T,
        ∀ G : ℝ → Bool → M → Matrix (Fin n) (Fin n) ℝ,
        (∀ t b, ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
          (fun x i j => G t b x i j)) →
        (∀ t b x, (G t b x).det ≠ 0) →
        (∀ t (ht : t ∈ Icc (0 : ℝ) T) x,
          (fun a : LowAtom ((lowerPerturbationExpr e i j).orderedDerivative word) (r + 1) =>
            nativeValues F (G t) x a.val.val) = v ⟨t, ht⟩ x) →
        (∀ᵐ t ∂timeMeasure T, ∀ _ht : t ∈ Icc (0 : ℝ) T,
          (fun x => fun a :
            HighAtom ((lowerPerturbationExpr e i j).orderedDerivative word) (r + 1) =>
              nativeValues F (G t) x a.val.val) =ᵐ[μ] Q t) →
        ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          Phi (v, Q) t =ᵐ[μ] fun x =>
            directionalWord F word (fun y =>
              secondJetSource (G t false y) (nativeJet F (G t) e false true y).second i j +
                ricciDeTurckSource (nativeJet F (G t) e false true y)
                  (eraseSecondJet (nativeJet F (G t) e false false y)) i j) x := by
  let p := (lowerPerturbationExpr e i j).orderedDerivative word
  have hp : p.degree ≤ 2 * (r + 1) :=
    (degree_ordered_lowerPerturbationExpr_le e i j word).trans (by omega)
  obtain ⟨epsilon, hepsilon, Phi, hPhi, hEq⟩ :=
    exists_smooth_finite_jet_forcing_extension μ hT p (r + 1) u
  refine ⟨epsilon, hepsilon, Phi, hPhi, ?_⟩
  intro v hv Q G hG hdet hLow hHigh
  have hEval := finite_jet_forcing_ae_eq_eval μ p (r + 1) hp v Q
    (fun t x => nativeValues F (G t) x) hLow hHigh
  filter_upwards [hEq v hv Q, hEval] with t ht heval
  intro htmem
  filter_upwards [ht htmem, heval htmem] with x hx hvalue
  exact hx.trans (hvalue.trans (ordered_lowerPerturbationExpr_native F (G t) e
    (hG t) (hdet t) i j word x))

open DeTurckCompatibleJetNative DeTurckJetCoordinatesNative

theorem exists_smooth_native_inverse_extension
    (F : iota → SmoothField (n := n) (M := M)) {a : M} {K : Set M}
    (C : Cutoffs (n := n) a K) (g0 : RiemannianMetric n M) (m : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ Inv : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ Inv ∧
      ∀ Q : NativeProbeContinuous (M := M) (iota := iota) m, ‖Q‖ < delta →
        ∀ x, Inv (matrixValueContinuous F C g0 Q) x =
          (matrixValueContinuous F C g0 Q x)⁻¹ := by
  have hU : IsOpen {A : Matrix (Fin n) (Fin n) ℝ | A.det ≠ 0} :=
    isOpen_ne_fun continuous_id.matrix_det continuous_const
  obtain ⟨epsilon, hepsilon, Inv, hInv, hInvEq⟩ :=
    exists_smooth_pointwise_extension hU matrixInverseEntries
      (fun A hA => contDiffAt_matrixInverseEntries_infty A hA)
      (backgroundMatrixContinuous C g0)
      (fun x => ((C.matrix g0 x).isUnit_iff_isUnit_det.mp
        (C.matrix_posDef g0 x).isUnit).ne_zero)
  let L := matrixDifferenceValueContinuous (k := m) F C g0
  have hLpos : 0 < ‖L‖ + 1 := by positivity
  refine ⟨epsilon / (‖L‖ + 1), div_pos hepsilon hLpos, Inv, hInv, ?_⟩
  intro Q hQsmall x
  have hprod : ‖Q‖ * (‖L‖ + 1) < epsilon := (lt_div_iff₀ hLpos).mp hQsmall
  have hnear : ‖matrixValueContinuous F C g0 Q - backgroundMatrixContinuous C g0‖ <
      epsilon := by
    rw [matrixValueContinuous_sub]
    change ‖L Q‖ < epsilon
    exact (L.le_opNorm Q).trans_lt (by nlinarith [norm_nonneg Q])
  exact hInvEq (matrixValueContinuous F C g0 Q) hnear x

theorem exists_smooth_native_low_atom_extension
    (F : iota → SmoothField (n := n) (M := M)) {a : M} {K : Set M}
    (C : Cutoffs (n := n) a K) (g0 : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (p : Expr (Fin n ⊕ iota) n) (m : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ Phi : NativeProbeContinuous (M := M) (iota := iota) m → C(M, LowAtom p m → ℝ),
      ContDiff ℝ ∞ Phi ∧
      ∀ Q : NativeProbeContinuous (M := M) (iota := iota) m, ‖Q‖ < delta →
        ∀ g : RiemannianMetric n M,
        (∀ ab w (hw : w.length ≤ m) x,
          Q ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x) →
        ∀ x b, Phi Q x b =
          nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x b.val.val := by
  obtain ⟨delta, hdelta, Inv, hInv, hInvEq⟩ :=
    exists_smooth_native_inverse_extension F C g0 m
  refine ⟨delta, hdelta,
    lowAtomTupleContinuous F C g0 p m Inv,
    contDiff_lowAtomTupleContinuous F C g0 p m Inv hInv, ?_⟩
  intro Q hQsmall g hQ x b
  exact lowAtomTupleContinuous_eq F C g0 hF p m Inv Q g hQ (hInvEq Q hQsmall) x b

theorem exists_smooth_native_inverse_difference
    (F : iota → SmoothField (n := n) (M := M)) {a : M} {K : Set M}
    (C : Cutoffs (n := n) a K) (g0 : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v) (m : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ A : NativeProbeContinuous (M := M) (iota := iota) m →
          C(M, Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ A ∧ A 0 = 0 ∧
      ∀ Q : NativeProbeContinuous (M := M) (iota := iota) m, ‖Q‖ < delta →
        ∀ g : RiemannianMetric n M,
        (∀ ab w (hw : w.length ≤ m) x,
          Q ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x) →
        ∀ x, A Q x = (C.matrix g x)⁻¹ - (C.matrix g0 x)⁻¹ := by
  obtain ⟨delta, hdelta, Inv, hInv, hInvEq⟩ :=
    exists_smooth_native_inverse_extension F C g0 m
  let A : NativeProbeContinuous (M := M) (iota := iota) m →
      C(M, Matrix (Fin n) (Fin n) ℝ) := fun Q =>
    Inv (matrixValueContinuous F C g0 Q) - Inv (backgroundMatrixContinuous C g0)
  have hzero : matrixValueContinuous F C g0
      (0 : NativeProbeContinuous (M := M) (iota := iota) m) =
        backgroundMatrixContinuous C g0 := by
    simp only [matrixValueContinuous, map_zero, add_zero]
  refine ⟨delta, hdelta, A,
    (hInv.comp (contDiff_matrixValueContinuous F C g0)).sub contDiff_const, ?_, ?_⟩
  · change Inv (matrixValueContinuous F C g0 0) - Inv (backgroundMatrixContinuous C g0) = 0
    rw [hzero, sub_self]
  · intro Q hQsmall g hQ x
    have hbg := hInvEq 0 (by simpa only [norm_zero] using hdelta) x
    rw [hzero] at hbg
    change Inv (matrixValueContinuous F C g0 Q) x - Inv (backgroundMatrixContinuous C g0) x = _
    rw [hInvEq Q hQsmall x, hbg, matrixValueContinuous_eq F C g0 hF Q g hQ x]
    rfl

theorem exists_smooth_native_jet_action
    (F : iota → SmoothField (n := n) (M := M)) {a : M} {K : Set M}
    (C : Cutoffs (n := n) a K) (g0 : RiemannianMetric n M)
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (p : Expr (Fin n ⊕ iota) n) (m k : ℕ)
    (hp : p.degree ≤ 2 * m) (hk : p.metricOrder false ≤ k) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ Phi : (NativeProbeContinuous (M := M) (iota := iota) m ×
          NativeProbeL2 (iota := iota) μ k) → Lp ℝ 2 μ,
      ContDiff ℝ ∞ Phi ∧
      ∀ Q : NativeProbeContinuous (M := M) (iota := iota) m, ‖Q‖ < delta →
        ∀ H : NativeProbeL2 (iota := iota) μ k, ∀ g : RiemannianMetric n M,
        (∀ ab w (hw : w.length ≤ m) x,
          Q ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x) →
        (∀ ab w (hw : w.length ≤ k),
          H ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) →
        Phi (Q, H) =ᵐ[μ] fun x =>
          p.eval (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) := by
  obtain ⟨delta, hdelta, low, hlow, hlowEq⟩ :=
    exists_smooth_native_low_atom_extension F C g0 hF p m
  refine ⟨delta, hdelta, fun z =>
    finiteSpatialJetAction μ p m (low z.1, highAtomTupleL2 F C g0 μ p m k hk z.2),
    (contDiff_finiteSpatialJetAction μ p m).comp
      ((hlow.comp contDiff_fst).prodMk
        ((contDiff_highAtomTupleL2 F C g0 μ p m k hk).comp contDiff_snd)), ?_⟩
  intro Q hQsmall H g hQ hH
  apply finiteSpatialJetAction_ae_eq_eval μ p m hp
    (low Q, highAtomTupleL2 F C g0 μ p m k hk H)
    (fun x => nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x)
  · intro x
    funext b
    exact (hlowEq Q hQsmall g hQ x b).symm
  · exact (highAtomTupleL2_ae_eq F C g0 μ hF p m k hk H g hH).symm

theorem exists_smooth_compatible_ordered_lower_forcing_extension (hT : 0 ≤ T)
    (F : iota → SmoothField (n := n) (M := M)) {a : M} {K : Set M}
    (C : Cutoffs (n := n) a K) (g0 : RiemannianMetric n M)
    (i j : Fin n) (word : List iota) (r : ℕ) (hword : word.length ≤ 2 * r)
    (u : TimePath C(M, LowAtom
      ((lowerPerturbationExpr (Sum.inl : Fin n → Fin n ⊕ iota) i j).orderedDerivative
        (word.map Sum.inr)) (r + 1) → ℝ) T) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Phi : (TimePath C(M, LowAtom
        ((lowerPerturbationExpr (Sum.inl : Fin n → Fin n ⊕ iota) i j).orderedDerivative
          (word.map Sum.inr)) (r + 1) → ℝ) T ×
        TimeL2 (Lp (HighAtom
          ((lowerPerturbationExpr (Sum.inl : Fin n → Fin n ⊕ iota) i j).orderedDerivative
            (word.map Sum.inr)) (r + 1) → ℝ) 2 μ) T) → TimeL2 (Lp ℝ 2 μ) T,
      ContDiff ℝ ∞ Phi ∧ ∀ v, ‖v - u‖ < epsilon →
        ∀ Q : TimeL2 (Lp (HighAtom
          ((lowerPerturbationExpr (Sum.inl : Fin n → Fin n ⊕ iota) i j).orderedDerivative
            (word.map Sum.inr)) (r + 1) → ℝ) 2 μ) T,
        ∀ g : ℝ → RiemannianMetric n M,
        (∀ t (ht : t ∈ Icc (0 : ℝ) T) x,
          (fun b : LowAtom
            ((lowerPerturbationExpr (Sum.inl : Fin n → Fin n ⊕ iota) i j).orderedDerivative
              (word.map Sum.inr)) (r + 1) =>
            nativeValues (combinedFields F C) (compatibleMatrix C g0 (g t)) x b.val.val) =
              v ⟨t, ht⟩ x) →
        (∀ᵐ t ∂timeMeasure T, ∀ _ht : t ∈ Icc (0 : ℝ) T,
          (fun x => fun b : HighAtom
            ((lowerPerturbationExpr (Sum.inl : Fin n → Fin n ⊕ iota) i j).orderedDerivative
              (word.map Sum.inr)) (r + 1) =>
            nativeValues (combinedFields F C) (compatibleMatrix C g0 (g t)) x b.val.val) =ᵐ[μ]
              Q t) →
        ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
          Phi (v, Q) t =ᵐ[μ] fun x =>
            directionalWord F word (fun y =>
              lowerJetContraction (C.matrix (g t) y)⁻¹ (C.jet g0 y).second i j +
                lowerJetSource (C.jet g0 y) (backgroundLowerJet (C.jet (g t) y)) i j) x := by
  let p := (lowerPerturbationExpr (Sum.inl : Fin n → Fin n ⊕ iota) i j).orderedDerivative
    (word.map Sum.inr)
  have hp : p.degree ≤ 2 * (r + 1) := by
    have h := degree_ordered_lowerPerturbationExpr_le
      (Sum.inl : Fin n → Fin n ⊕ iota) i j (word.map Sum.inr)
    simp only [List.length_map] at h
    exact h.trans (by omega)
  obtain ⟨epsilon, hepsilon, Phi, hPhi, hEq⟩ :=
    exists_smooth_finite_jet_forcing_extension μ hT p (r + 1) u
  refine ⟨epsilon, hepsilon, Phi, hPhi, ?_⟩
  intro v hv Q g hLow hHigh
  have hEval := finite_jet_forcing_ae_eq_eval μ p (r + 1) hp v Q
    (fun t x => nativeValues (combinedFields F C) (compatibleMatrix C g0 (g t)) x)
    hLow hHigh
  filter_upwards [hEq v hv Q, hEval] with t ht heval
  intro htmem
  filter_upwards [ht htmem, heval htmem] with x hx hvalue
  exact hx.trans (hvalue.trans
    (ordered_lowerPerturbationExpr_compatible F C g0 (g t) i j word x))

end NativeLowerSource

end PoincareConjecture.DeTurckMetricProducerNative
