import PoincareConjecture.Proofs.M03.Existence.DeTurckStatePullbackNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckParameterBackgroundNative
import PoincareConjecture.Proofs.M03.Existence.SpectralLpOperatorNative
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators ENNReal

namespace PoincareConjecture.DeTurckStatePullbackContinuityNative

open TensorProbeNative TensorHilbertNative ParsevalTensorNative ChartMeasureNative
  DeTurckJetCoordinatesNative DeTurckJetAffineNative DeTurckMetricDomainNative
  DeTurckCompletedOutputNative DeTurckStatePullbackNative
  DeTurckParameterBackgroundNative ChartLpNative SpectralHeatNative

variable {n : ℕ} {M P : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "I" => 𝓡 n

theorem contMDiffOn_transportedField {U : Set P}
    (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (V : SmoothField (n := n) (M := M)) :
    ContMDiffOn (𝓘(ℝ, P).prod I) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (fun q : P × M => (⟨q.2, transportedField (Phi q.1) V q.2⟩ : TangentBundle I M))
      (U ×ˢ univ) := by
  have h := (contMDiffOn_parameter_pushforward Phi hPhi V).comp
    (contMDiffOn_fst.prodMk hInv) (fun q hq => ⟨hq.1, mem_univ _⟩)
  apply h.congr
  intro q _
  have heq := transportedField_apply (Phi q.1) V ((Phi q.1).symm q.2)
  rw [(Phi q.1).apply_symm_apply] at heq
  simp only [Function.comp_def, heq]
  exact Bundle.TotalSpace.ext ((Phi q.1).apply_symm_apply q.2).symm HEq.rfl

variable [T2Space M] [CompactSpace M] {g0 : RiemannianMetric n M} (d : Data g0)

theorem contMDiffOn_transportCoefficient {U : Set P}
    (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (i a : Fin d.fieldCount) :
    ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : P × M => transportCoefficient d (Phi q.1) i a q.2) (U ×ˢ univ) := by
  have hsnd : ContMDiff (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (Prod.snd : P × M → M) := contMDiff_snd
  have hg := (g0.contMDiff.comp hsnd).contMDiffOn (s := U ×ˢ univ)
  have hF := ((d.fields a).contMDiff.comp hsnd).contMDiffOn (s := U ×ˢ univ)
  have hG := contMDiffOn_transportedField Phi hPhi hInv (d.fields i)
  have hpair := ContMDiffOn.clm_bundle_apply₂
    (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := fun _ : M => ℝ)
    (b := Prod.snd) (ψ := fun q : P × M => g0.inner q.2) hg hF hG
  intro q hq
  exact (Bundle.contMDiffWithinAt_totalSpace.mp (hpair q hq)).2

structure CoefficientFamily (U : Set P) where
  toFun : P × M → ℝ
  slice_smooth : ∀ p, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => toFun (p, x))
  joint_smooth : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞ toFun (U ×ˢ univ)

def coefficientProduct {U : Set P}
    (c e : CoefficientFamily (n := n) (M := M) U) : CoefficientFamily (n := n) (M := M) U where
  toFun q := c.toFun q * e.toFun q
  slice_smooth p := (c.slice_smooth p).mul (e.slice_smooth p)
  joint_smooth := c.joint_smooth.mul e.joint_smooth

def coefficientDirectional {U : Set P} (i : Fin d.fieldCount)
    (c : CoefficientFamily (n := n) (M := M) U) : CoefficientFamily (n := n) (M := M) U where
  toFun q := scalarDirectional (d.fields i) (fun x => c.toFun (q.1, x)) q.2
  slice_smooth p := contMDiff_directional (c.slice_smooth p) (d.fields i)
  joint_smooth := contMDiffOn_parameter_directional c.toFun c.joint_smooth (d.fields i)

structure PullbackTermFamily (U : Set P) where
  coefficient : CoefficientFamily (n := n) (M := M) U
  word : List (Fin d.fieldCount)

def termAt {U : Set P} (p : P) (t : PullbackTermFamily d U) :
    DirectionalTerm (n := n) (M := M) (iota := Fin d.fieldCount) :=
  ⟨fun x => t.coefficient.toFun (p, x), t.coefficient.slice_smooth p, t.word⟩

def termsAt {U : Set P} (p : P) (ts : List (PullbackTermFamily d U)) :
    List (DirectionalTerm (n := n) (M := M) (iota := Fin d.fieldCount)) :=
  ts.map (termAt d p)

def familyScale {U : Set P} (c : CoefficientFamily (n := n) (M := M) U)
    (ts : List (PullbackTermFamily d U)) : List (PullbackTermFamily d U) :=
  ts.map (fun t => ⟨coefficientProduct c t.coefficient, t.word⟩)

def familyDifferentiate {U : Set P} (i : Fin d.fieldCount)
    (ts : List (PullbackTermFamily d U)) : List (PullbackTermFamily d U) :=
  ts.flatMap (fun t => [⟨coefficientDirectional d i t.coefficient, t.word⟩,
    ⟨t.coefficient, i :: t.word⟩])

def familyExpand {U : Set P}
    (c : Fin d.fieldCount → Fin d.fieldCount → CoefficientFamily (n := n) (M := M) U)
    (i : Fin d.fieldCount) (ts : List (PullbackTermFamily d U)) :
    List (PullbackTermFamily d U) :=
  Finset.univ.toList.flatMap (fun a => familyScale d (c i a) (familyDifferentiate d a ts))

theorem termsAt_scale {U : Set P} (p : P)
    (c : CoefficientFamily (n := n) (M := M) U) (ts : List (PullbackTermFamily d U)) :
    termsAt d p (familyScale d c ts) =
      scaleTerms (fun x => c.toFun (p, x)) (c.slice_smooth p) (termsAt d p ts) := by
  simp only [termsAt, familyScale, scaleTerms, List.map_map]
  rfl

theorem termsAt_differentiate {U : Set P} (p : P) (i : Fin d.fieldCount)
    (ts : List (PullbackTermFamily d U)) :
    termsAt d p (familyDifferentiate d i ts) =
      differentiateDirectionalTerms d.fields i (termsAt d p ts) := by
  simp only [termsAt, familyDifferentiate, differentiateDirectionalTerms,
    List.map_flatMap, List.flatMap_map, List.map_cons, List.map_nil]
  rfl

theorem termsAt_expand {U : Set P} (p : P)
    (c : Fin d.fieldCount → Fin d.fieldCount → CoefficientFamily (n := n) (M := M) U)
    (i : Fin d.fieldCount) (ts : List (PullbackTermFamily d U)) :
    termsAt d p (familyExpand d c i ts) =
      expandedDerivative d.fields (fun j a x => (c j a).toFun (p, x))
        (fun j a => (c j a).slice_smooth p) i (termsAt d p ts) := by
  simp only [termsAt, familyExpand, expandedDerivative, List.map_flatMap]
  congr 1
  funext a
  exact (termsAt_scale d p (c i a) (familyDifferentiate d a ts)).trans
    (congrArg (scaleTerms (fun x => (c i a).toFun (p, x)) ((c i a).slice_smooth p))
      (termsAt_differentiate d p a ts))

def familyWords {U : Set P}
    (c : Fin d.fieldCount → Fin d.fieldCount → CoefficientFamily (n := n) (M := M) U)
    (seed : CoefficientFamily (n := n) (M := M) U) :
    List (Fin d.fieldCount) → List (PullbackTermFamily d U)
  | [] => [⟨seed, []⟩]
  | i :: w => familyExpand d c i (familyWords c seed w)

theorem termsAt_words {U : Set P} (p : P)
    (c : Fin d.fieldCount → Fin d.fieldCount → CoefficientFamily (n := n) (M := M) U)
    (seed : CoefficientFamily (n := n) (M := M) U) (w : List (Fin d.fieldCount)) :
    termsAt d p (familyWords d c seed w) =
      weightedWordTerms d.fields (fun j a x => (c j a).toFun (p, x))
        (fun j a => (c j a).slice_smooth p)
        (fun x => seed.toFun (p, x)) (seed.slice_smooth p) w := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [familyWords, termsAt_expand, ih, weightedWordTerms]

theorem familyWords_order {U : Set P}
    (c : Fin d.fieldCount → Fin d.fieldCount → CoefficientFamily (n := n) (M := M) U)
    (seed : CoefficientFamily (n := n) (M := M) U) (w : List (Fin d.fieldCount)) :
    ∀ t ∈ familyWords d c seed w, t.word.length ≤ w.length := by
  intro t ht
  have hm : termAt d (0 : P) t ∈ termsAt d (0 : P) (familyWords d c seed w) :=
    List.mem_map.mpr ⟨t, ht, rfl⟩
  rw [termsAt_words] at hm
  exact weightedWordTerms_order d.fields (fun j a x => (c j a).toFun (0, x))
    (fun j a => (c j a).slice_smooth 0)
    (fun x => seed.toFun (0, x)) (seed.slice_smooth 0) w _ hm

def transportFamily {U : Set P} (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (i a : Fin d.fieldCount) : CoefficientFamily (n := n) (M := M) U where
  toFun q := transportCoefficient d (Phi q.1) i a q.2
  slice_smooth p := transportCoefficient_contMDiff d (Phi p) i a
  joint_smooth := contMDiffOn_transportCoefficient d Phi hPhi hInv i a

def pullbackTermFamilies {U : Set P} (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (ab cd : d.ProbeIndex) (w : List (Fin d.fieldCount)) : List (PullbackTermFamily d U) :=
  familyWords d (transportFamily d Phi hPhi hInv)
    (coefficientProduct (transportFamily d Phi hPhi hInv ab.1 cd.1)
      (transportFamily d Phi hPhi hInv ab.2 cd.2)) w

theorem termsAt_pullbackTermFamilies {U : Set P} (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (ab cd : d.ProbeIndex) (w : List (Fin d.fieldCount)) (p : P) :
    termsAt d p (pullbackTermFamilies d Phi hPhi hInv ab cd w) =
      pullbackTerms d (Phi p) ab cd w :=
  termsAt_words d p _ _ w

theorem termsAt_order {U : Set P} (p : P) (ts : List (PullbackTermFamily d U))
    {k : ℕ} (horder : ∀ t ∈ ts, t.word.length ≤ k) :
    ∀ t ∈ termsAt d p ts, t.word.length ≤ k := by
  intro t ht
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
  exact horder q hq

variable [MeasurableSpace M] [BorelSpace M]

theorem continuousOn_coefficientL2 {U : Set P} (hU : IsOpen U)
    (c : CoefficientFamily (n := n) (M := M) U) :
    ContinuousOn (fun p => coefficientL2 d.charts.measure
      (fun x => c.toFun (p, x)) (c.slice_smooth p)) U := by
  have hc := ContinuousMap.continuousOn_mkD_of_uncurry
    (fun p x => c.toFun (p, x)) 0 c.joint_smooth.continuousOn
  have heq (p : P) : ContinuousMap.mkD (fun x => c.toFun (p, x)) 0 =
      (⟨fun x => c.toFun (p, x), (c.slice_smooth p).continuous⟩ : C(M, ℝ)) :=
    ContinuousMap.mkD_of_continuous (c.slice_smooth p).continuous
  have hs : ContinuousOn (fun p =>
      (⟨fun x => c.toFun (p, x), (c.slice_smooth p).continuous⟩ : C(M, ℝ))) U := by
    simpa only [heq] using hc
  exact ((ContinuousLinearMap.mul ℝ ℝ).holderL d.charts.measure (⊤ : ENNReal) 2 2).continuous.comp_continuousOn
    ((ContinuousMap.toLp (⊤ : ENNReal) d.charts.measure ℝ).continuous.comp_continuousOn hs)

theorem continuousOn_termsAtL2 {U : Set P} (hU : IsOpen U)
    (ts : List (PullbackTermFamily d U)) {k : ℕ}
    (horder : ∀ t ∈ ts, t.word.length ≤ k) :
    ContinuousOn (fun p => termsL2 d.charts.measure (termsAt d p ts)
      (termsAt_order d p ts horder)) U := by
  induction ts with
  | nil => exact continuousOn_const
  | cons t ts ih =>
    change ContinuousOn (fun p =>
      (coefficientL2 d.charts.measure (fun x => t.coefficient.toFun (p, x))
        (t.coefficient.slice_smooth p)).comp
          (ContinuousLinearMap.proj (wordIndex t.word (horder t List.mem_cons_self))) +
      termsL2 d.charts.measure (termsAt d p ts)
        (termsAt_order d p ts (fun s hs => horder s (List.mem_cons_of_mem t hs)))) U
    exact ((continuousOn_coefficientL2 d hU t.coefficient).clm_comp continuousOn_const).add
      (ih (fun s hs => horder s (List.mem_cons_of_mem t hs)))

theorem continuousOn_pullbackTermsL2 {U : Set P} (hU : IsOpen U)
    (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (k : ℕ) (ab cd : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ k) :
    ContinuousOn (fun p => termsL2 d.charts.measure (pullbackTerms d (Phi p) ab cd w)
      (fun t ht => (pullbackTerms_order d (Phi p) ab cd w t ht).trans hw)) U := by
  let ts := pullbackTermFamilies d Phi hPhi hInv ab cd w
  have ho : ∀ t ∈ ts, t.word.length ≤ k :=
    fun t ht => (familyWords_order d _ _ w t ht).trans hw
  have hc := continuousOn_termsAtL2 d hU ts ho
  have heq (p : P) : termsL2 d.charts.measure (termsAt d p ts) (termsAt_order d p ts ho) =
      termsL2 d.charts.measure (pullbackTerms d (Phi p) ab cd w)
        (fun t ht => (pullbackTerms_order d (Phi p) ab cd w t ht).trans hw) := by
    congr 1
    exact termsAt_pullbackTermFamilies d Phi hPhi hInv ab cd w p
  simpa only [heq] using hc

theorem continuousOn_pullbackWordBefore {U : Set P} (hU : IsOpen U)
    (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
    (k : ℕ) (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ k) :
    ContinuousOn (fun p => pullbackWordBefore d (Phi p) k ab w hw) U := by
  apply continuousOn_finsetSum
  intro cd _
  exact (continuousOn_pullbackTermsL2 d hU Phi hPhi hInv k ab cd w hw).clm_comp
    continuousOn_const

section StrongAction

variable {U N : Set P} (hU : IsOpen U) (hNU : N ⊆ U)
  (Phi : P → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
  (hPhi : ContMDiffOn (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
    (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
  (hInv : ContMDiffOn (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
    (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ))
  {C : ℝ≥0∞} (hC : C ≠ ⊤)
  (hdom : ∀ p ∈ N, d.charts.measure.map (Phi p) ≤ C • d.charts.measure)

include hU hNU hPhi hInv

theorem continuous_pullbackTuple (k : ℕ) :
    Continuous (fun q : N × ProbeTuples d k =>
      pullbackTuple d (Phi q.1) hC (hdom q.1 q.1.property) k q.2) := by
  have hfamily : Continuous (fun q : N × M => Phi q.1 q.2) :=
    hPhi.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun q => ⟨hNU q.1.property, mem_univ _⟩)
  have hscalar : Continuous (fun q : N × Lp ℝ 2 d.charts.measure =>
      dominatedPullbackL2 (Phi q.1) (Phi q.1).continuous.measurable.aemeasurable
        hC (hdom q.1 q.1.property) q.2) :=
    continuous_dominatedPullbackL2 d (fun p : N => Phi p) hC
      (fun p => hdom p p.property) hfamily
  simp only [pullbackTuple, ContinuousLinearMap.coe_pi', ContinuousLinearMap.comp_apply]
  apply continuous_pi
  intro ab
  apply continuous_pi
  intro w
  have hw : (List.ofFn w.2).length ≤ k := by
    simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt
  have hbefore : Continuous (fun p : N =>
      pullbackWordBefore d (Phi p) k ab (List.ofFn w.2) hw) :=
    (continuousOn_pullbackWordBefore d hU Phi hPhi hInv k ab (List.ofFn w.2) hw).comp_continuous
      continuous_subtype_val (fun p => hNU p.property)
  have hinput : Continuous (fun q : N × ProbeTuples d k =>
      (q.1, pullbackWordBefore d (Phi q.1) k ab (List.ofFn w.2) hw q.2)) :=
    continuous_fst.prodMk ((hbefore.comp continuous_fst).clm_apply continuous_snd)
  simpa only [Function.comp_def] using hscalar.comp hinput

theorem continuous_evenPullback (L : FiniteChartLocalizationData d.charts) (r : ℕ) :
    Continuous (fun q : N × State d.SymmetricIndex =>
      evenPullback d (Phi q.1) hC (hdom q.1 q.1.property) L r q.2) := by
  have h := continuous_pullbackTuple d hU hNU Phi hPhi hInv hC hdom (2 * r)
  have hinput : Continuous (fun q : N × State d.SymmetricIndex =>
      (q.1, nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl q.2)) :=
    continuous_fst.prodMk
      ((nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl).continuous.comp continuous_snd)
  have htuple := h.comp hinput
  simpa only [evenPullback, ContinuousLinearMap.comp_apply, Function.comp_def] using
    (evenOutput d r).continuous.comp htuple

end StrongAction

theorem norm_pullbackTuple_le (Phi : Diffeomorph I I M M ∞)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure)
    (k : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hbefore : ∀ (ab : d.ProbeIndex) (w : WordIndex (Fin d.fieldCount) k),
      ‖pullbackWordBefore d Phi k ab (List.ofFn w.2)
        (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)‖ ≤ B) :
    ‖pullbackTuple d Phi hC hdom k‖ ≤ C.toReal ^ (1 / (2 : ℝ≥0∞)).toReal * B := by
  let K := C.toReal ^ (1 / (2 : ℝ≥0∞)).toReal
  have hK : 0 ≤ K := Real.rpow_nonneg ENNReal.toReal_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK hB)
  intro Q
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hK hB) (norm_nonneg Q))).mpr
  intro ab
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hK hB) (norm_nonneg Q))).mpr
  intro w
  have hw : (List.ofFn w.2).length ≤ k := by
    simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt
  change ‖dominatedPullbackL2 Phi Phi.continuous.measurable.aemeasurable hC hdom
    (pullbackWordBefore d Phi k ab (List.ofFn w.2) hw Q)‖ ≤ _
  calc
    _ ≤ K * ‖pullbackWordBefore d Phi k ab (List.ofFn w.2) hw Q‖ :=
      norm_dominatedPullbackL2_apply_le Phi Phi.continuous.measurable.aemeasurable hC hdom _
    _ ≤ K * (B * ‖Q‖) := mul_le_mul_of_nonneg_left
      (((pullbackWordBefore d Phi k ab (List.ofFn w.2) hw).le_opNorm Q).trans
        (mul_le_mul_of_nonneg_right (hbefore ab w) (norm_nonneg Q))) hK
    _ = _ := by rw [mul_assoc]

theorem norm_evenPullback_le (L : FiniteChartLocalizationData d.charts)
    (Phi : Diffeomorph I I M M ∞) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure) (r : ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbefore : ∀ (ab : d.ProbeIndex) (w : WordIndex (Fin d.fieldCount) (2 * r)),
      ‖pullbackWordBefore d Phi (2 * r) ab (List.ofFn w.2)
        (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)‖ ≤ B) :
    ‖evenPullback d Phi hC hdom L r‖ ≤
      ‖evenOutput d r‖ * ((C.toReal ^ (1 / (2 : ℝ≥0∞)).toReal * B) *
        ‖nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl‖) := by
  apply ((evenOutput d r).opNorm_comp_le _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact ((pullbackTuple d Phi hC hdom (2 * r)).opNorm_comp_le _).trans
    (mul_le_mul_of_nonneg_right (norm_pullbackTuple_le d Phi hC hdom (2 * r) hB hbefore)
      (norm_nonneg _))

theorem exists_locally_uniform_coefficient_bound {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U)
    (Phi : P → Diffeomorph I I M M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ)) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ p in 𝓝 (0 : P),
      ∀ (ab : d.ProbeIndex) (w : WordIndex (Fin d.fieldCount) k),
        ‖pullbackWordBefore d (Phi p) k ab (List.ofFn w.2)
          (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)‖ ≤ B := by
  classical
  let b (ab : d.ProbeIndex) (w : WordIndex (Fin d.fieldCount) k) :=
    ‖pullbackWordBefore d (Phi 0) k ab (List.ofFn w.2)
      (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)‖ + 1
  let B : ℝ := ∑ ab : d.ProbeIndex, ∑ w : WordIndex (Fin d.fieldCount) k, b ab w
  have hb (ab : d.ProbeIndex) (w : WordIndex (Fin d.fieldCount) k) : 0 ≤ b ab w := by
    dsimp [b]
    positivity
  have hbB (ab : d.ProbeIndex) (w : WordIndex (Fin d.fieldCount) k) : b ab w ≤ B :=
    (Finset.single_le_sum (fun v _ => hb ab v) (Finset.mem_univ w)).trans
      (Finset.single_le_sum (fun cd _ => Finset.sum_nonneg (fun v _ => hb cd v))
        (Finset.mem_univ ab))
  refine ⟨B, Finset.sum_nonneg (fun ab _ => Finset.sum_nonneg (fun w _ => hb ab w)), ?_⟩
  apply Filter.eventually_all.mpr
  intro ab
  apply Filter.eventually_all.mpr
  intro w
  have hw : (List.ofFn w.2).length ≤ k := by
    simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt
  have hc := (continuousOn_pullbackWordBefore d hU Phi hPhi hInv k ab
    (List.ofFn w.2) hw).continuousAt (hU.mem_nhds hzero)
  have hlt : ‖pullbackWordBefore d (Phi 0) k ab (List.ofFn w.2) hw‖ < b ab w := by
    dsimp [b]
    linarith
  filter_upwards [hc.norm (Iio_mem_nhds hlt)] with p hp
  exact hp.le.trans (hbB ab w)

theorem exists_locally_uniform_evenPullback (L : FiniteChartLocalizationData d.charts)
    {U : Set P} (hU : IsOpen U) (hzero : (0 : P) ∈ U)
    (Phi : P → Diffeomorph I I M M ∞) (hidentity : Phi 0 = Diffeomorph.refl I M ∞)
    (hPhi : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => Phi q.1 q.2) (U ×ˢ univ))
    (hInv : ContMDiffOn (𝓘(ℝ, P).prod I) I ∞
      (fun q : P × M => (Phi q.1).symm q.2) (U ×ˢ univ)) (r : ℕ) :
    ∃ C : ℝ≥0∞, ∃ hC : C ≠ ⊤, ∃ V : Set P,
      IsOpen V ∧ (0 : P) ∈ V ∧ V ⊆ U ∧
      ∃ hdom : ∀ p ∈ V, d.charts.measure.map (Phi p) ≤ C • d.charts.measure,
        Continuous (fun q : V × State d.SymmetricIndex =>
          evenPullback d (Phi q.1) hC (hdom q.1 q.1.property) L r q.2) ∧
        ∃ K : ℝ, 0 ≤ K ∧ ∀ p : V,
          ‖evenPullback d (Phi p) hC (hdom p p.property) L r‖ ≤ K := by
  obtain ⟨C, hC, N, hN, hdomN⟩ := exists_locally_uniform_measure_domination d L Phi hidentity
    (fun x => hInv.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hzero, mem_univ x⟩))
  obtain ⟨B, hB, hbound⟩ := exists_locally_uniform_coefficient_bound d hU hzero Phi hPhi hInv (2 * r)
  have hevent : {p | p ∈ U ∧ p ∈ N ∧
      ∀ (ab : d.ProbeIndex) (w : WordIndex (Fin d.fieldCount) (2 * r)),
        ‖pullbackWordBefore d (Phi p) (2 * r) ab (List.ofFn w.2)
          (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)‖ ≤ B} ∈ 𝓝 0 :=
    Filter.inter_mem (hU.mem_nhds hzero) (Filter.inter_mem hN hbound)
  obtain ⟨V, hVsub, hVo, h0V⟩ := mem_nhds_iff.mp hevent
  have hVU : V ⊆ U := fun p hp => (hVsub hp).1
  have hdom : ∀ p ∈ V, d.charts.measure.map (Phi p) ≤ C • d.charts.measure :=
    fun p hp => hdomN p (hVsub hp).2.1
  refine ⟨C, hC, V, hVo, h0V, hVU, hdom,
    continuous_evenPullback d hU hVU Phi hPhi hInv hC hdom L r,
    ‖evenOutput d r‖ * ((C.toReal ^ (1 / (2 : ℝ≥0∞)).toReal * B) *
      ‖nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl‖), ?_, ?_⟩
  · exact mul_nonneg (norm_nonneg _)
      (mul_nonneg (mul_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _) hB) (norm_nonneg _))
  · intro p
    exact norm_evenPullback_le d L (Phi p) hC (hdom p p.property) r hB
      (hVsub p.property).2.2

theorem continuous_evenPullback_timeL2 (L : FiniteChartLocalizationData d.charts)
    (Phi : P → Diffeomorph I I M M ∞) {C : ℝ≥0∞} (hC : C ≠ ⊤) {V : Set P}
    (hdom : ∀ p ∈ V, d.charts.measure.map (Phi p) ≤ C • d.charts.measure) (r : ℕ)
    (hstrong : Continuous (fun q : V × State d.SymmetricIndex =>
      evenPullback d (Phi q.1) hC (hdom q.1 q.1.property) L r q.2))
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ p : V, ‖evenPullback d (Phi p) hC (hdom p p.property) L r‖ ≤ K)
    (μ : Measure ℝ) :
    Continuous (fun q : V × Lp (State d.SymmetricIndex) 2 μ =>
      (evenPullback d (Phi q.1) hC (hdom q.1 q.1.property) L r).compLpL 2 μ q.2) := by
  let A (p : V) := evenPullback d (Phi p) hC (hdom p p.property) L r
  apply continuous_prod_of_continuous_lipschitzWith' _ (⟨K, hK⟩ : NNReal)
  · intro p
    exact ContinuousLinearMap.lipschitzWith_of_opNorm_le (K := (⟨K, hK⟩ : NNReal))
      ((ContinuousLinearMap.norm_compLpL_le (A p)).trans (hbound p))
  · intro F
    apply continuous_iff_continuousAt.mpr
    intro p0
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    let f (p : V) (t : ℝ) : ℝ := ‖A p (F t) - A p0 (F t)‖ ^ 2
    let b (t : ℝ) : ℝ := (K + K) ^ 2 * ‖F t‖ ^ 2
    have hmeas (p : V) : AEStronglyMeasurable (f p) μ :=
      (((A p).continuous.comp_aestronglyMeasurable (Lp.memLp F).aestronglyMeasurable).sub
        ((A p0).continuous.comp_aestronglyMeasurable (Lp.memLp F).aestronglyMeasurable)).norm.pow 2
    have hb : Integrable b μ :=
      ((Lp.memLp F).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
    have hdomf (p : V) (t : ℝ) : ‖f p t‖ ≤ b t := by
      have hn : ‖A p (F t) - A p0 (F t)‖ ≤ (K + K) * ‖F t‖ := by
        calc
          _ ≤ ‖A p (F t)‖ + ‖A p0 (F t)‖ := norm_sub_le _ _
          _ ≤ K * ‖F t‖ + K * ‖F t‖ := add_le_add
            (((A p).le_opNorm (F t)).trans
              (mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg _)))
            (((A p0).le_opNorm (F t)).trans
              (mul_le_mul_of_nonneg_right (hbound p0) (norm_nonneg _)))
          _ = _ := (add_mul _ _ _).symm
      change ‖‖A p (F t) - A p0 (F t)‖ ^ 2‖ ≤ _
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [b, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hlim (t : ℝ) : Tendsto (fun p => f p t) (𝓝 p0) (𝓝 (0 : ℝ)) := by
      have hc := hstrong.comp (continuous_id.prodMk (continuous_const (y := F t)))
      simpa only [Function.comp_def, id_eq, A, f, sub_self, norm_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        ((hc.tendsto p0).sub_const (A p0 (F t))).norm.pow 2
    have hint : Tendsto (fun p => ∫ t, f p t ∂μ) (𝓝 p0) (𝓝 (0 : ℝ)) := by
      simpa only [integral_zero] using
        tendsto_integral_filter_of_dominated_convergence (μ := μ) b
          (Eventually.of_forall hmeas)
          (Eventually.of_forall (fun p => Eventually.of_forall (hdomf p))) hb
          (Eventually.of_forall hlim)
    have hid (p : V) : ‖(A p).compLpL 2 μ F - (A p0).compLpL 2 μ F‖ ^ 2 =
        ∫ t, f p t ∂μ := by
      rw [forcing_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub ((A p).compLpL 2 μ F) ((A p0).compLpL 2 μ F),
        (A p).coeFn_compLpL F, (A p0).coeFn_compLpL F] with t ht hp hp0
      simp only [ht, Pi.sub_apply, hp, hp0, f]
    have hsq : Tendsto (fun p => ‖(A p).compLpL 2 μ F - (A p0).compLpL 2 μ F‖ ^ 2)
        (𝓝 p0) (𝓝 (0 : ℝ)) := by simpa only [hid] using hint
    have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

end PoincareConjecture.DeTurckStatePullbackContinuityNative

end
