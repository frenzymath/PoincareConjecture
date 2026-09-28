import PoincareConjecture.Proofs.M03.Existence.DeTurckStateApproximationNative
import PoincareConjecture.Proofs.M03.Existence.PullbackConnectionNative
import PoincareConjecture.Proofs.M03.Existence.ChartMeasureUpperNative
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.MeasureTheory.Function.ContinuousMapDense

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators ENNReal

namespace PoincareConjecture.DeTurckStatePullbackNative

open TensorProbeNative TensorHilbertNative ParsevalTensorNative ChartMeasureNative
  DeTurckJetCoordinatesNative DeTurckJetAffineNative DeTurckInverseCompositionNative
  DeTurckMetricDomainNative DeTurckCompletedOutputNative DeTurckStateApproximationNative
  ChartLpNative SpectralHeatNative

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def transportedField (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (V : SmoothField (n := n) (M := M)) : SmoothField (n := n) (M := M) where
  toFun := DiffeomorphNative.pullField Phi.symm V
  contMDiff_toFun := by
    apply contMDiffOn_univ.mp
    simpa only [preimage_univ] using
      DiffeomorphNative.contMDiffOn_pullField Phi.symm (U := univ) V.contMDiff.contMDiffOn

theorem transportedField_apply (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (V : SmoothField (n := n) (M := M)) (x : M) :
    transportedField Phi V (Phi x) = mfderiv (𝓡 n) (𝓡 n) Phi x (V x) := by
  have hid : ((Phi.symm : M → M) ∘ Phi) = id := funext Phi.symm_apply_apply
  have hcomp : (mfderiv (𝓡 n) (𝓡 n) Phi.symm (Phi x)).comp
      (mfderiv (𝓡 n) (𝓡 n) Phi x) = ContinuousLinearMap.id ℝ _ := by
    rw [← mfderiv_comp x (Phi.symm.mdifferentiable (by simp) (Phi x))
      (Phi.mdifferentiable (by simp) x), hid, mfderiv_id]
  apply (Phi.symm.mfderivToContinuousLinearEquiv (by simp) (Phi x)).injective
  change mfderiv (𝓡 n) (𝓡 n) Phi.symm (Phi x)
      (DiffeomorphNative.pullField Phi.symm V (Phi x)) =
    mfderiv (𝓡 n) (𝓡 n) Phi.symm (Phi x)
      (mfderiv (𝓡 n) (𝓡 n) Phi x (V x))
  rw [DiffeomorphNative.mfderiv_pullField, Phi.symm_apply_apply]
  exact (congrArg (fun A : E →L[ℝ] E => A (V x)) hcomp).symm

theorem scalarDirectional_comp (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (V : SmoothField (n := n) (M := M)) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    scalarDirectional V (f ∘ Phi) x =
      scalarDirectional (transportedField Phi V) f (Phi x) := by
  change mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (f ∘ Phi) x (V x) = _
  rw [mfderiv_comp_apply x (hf.mdifferentiable (by simp) (Phi x))
    (Phi.mdifferentiable (by simp) x), ← transportedField_apply]
  rfl

theorem directionalWord_comp {iota : Type*}
    (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (F : iota → SmoothField (n := n) (M := M)) (w : List iota)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalWord F w (f ∘ Phi) x =
      directionalWord (fun i => transportedField Phi (F i)) w f (Phi x) := by
  have hsmooth : ∀ v : List iota, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (directionalWord (fun i => transportedField Phi (F i)) v f) := by
    intro v
    induction v with
    | nil => exact hf
    | cons i v ih => exact contMDiff_directional ih (transportedField Phi (F i))
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    have heq : directionalWord F w (f ∘ Phi) =
        directionalWord (fun j => transportedField Phi (F j)) w f ∘ Phi := funext ih
    change scalarDirectional (F i) (directionalWord F w (f ∘ Phi)) x =
      scalarDirectional (transportedField Phi (F i))
        (directionalWord (fun j => transportedField Phi (F j)) w f) (Phi x)
    rw [heq, scalarDirectional_comp Phi (F i) (hsmooth w)]

variable [T2Space M] [CompactSpace M] {g0 : RiemannianMetric n M} (d : Data g0)

def transportCoefficient (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (i a : Fin d.fieldCount) (y : M) : ℝ :=
  g0.inner y (d.fields a y) (transportedField Phi (d.fields i) y)

theorem transportCoefficient_contMDiff (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (i a : Fin d.fieldCount) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (transportCoefficient d Phi i a) :=
  contMDiff_pairing (metricTensor g0) (d.fields a) (transportedField Phi (d.fields i))

theorem transportedField_eq_sum (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (i : Fin d.fieldCount) (y : M) :
    transportedField Phi (d.fields i) y =
      ∑ a, transportCoefficient d Phi i a y • d.fields a y :=
  (d.parseval y (transportedField Phi (d.fields i) y)).symm

def fiberPullback (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (h : SmoothTensor (n := n) (M := M)) (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := h (Phi x)
  let J : E →L[ℝ] E := mfderiv (𝓡 n) (𝓡 n) Phi x
  exact B.bilinearComp J J

def pullbackProbes (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (h : SmoothTensor (n := n) (M := M)) (x : M) : Coefficients (Fin d.fieldCount) :=
  WithLp.toLp 2 (fun ab : d.ProbeIndex => h (Phi x)
    (transportedField Phi (d.fields ab.1) (Phi x))
    (transportedField Phi (d.fields ab.2) (Phi x)))

theorem pullbackProbes_contMDiff (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (h : SmoothTensor (n := n) (M := M)) (ab : d.ProbeIndex) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => pullbackProbes d Phi h x ab) :=
  (contMDiff_pairing h (transportedField Phi (d.fields ab.1))
    (transportedField Phi (d.fields ab.2))).comp Phi.contMDiff

def smoothPullback (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (h : SmoothTensor (n := n) (M := M)) : SmoothTensor (n := n) (M := M) :=
  smoothDecode g0 d.fields (pullbackProbes d Phi h) (pullbackProbes_contMDiff d Phi h)

theorem smoothPullback_eq_fiber (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (h : SmoothTensor (n := n) (M := M)) (x : M) :
    smoothPullback d Phi h x = fiberPullback Phi h x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g0.toRiemannianMetric⟩
  have hprobe : pullbackProbes d Phi h x =
      encode (fun a => d.fields a x) (fiberPullback Phi h x) := by
    ext ab
    change h (Phi x) (transportedField Phi (d.fields ab.1) (Phi x))
        (transportedField Phi (d.fields ab.2) (Phi x)) =
      h (Phi x) (mfderiv (𝓡 n) (𝓡 n) Phi x (d.fields ab.1 x))
        (mfderiv (𝓡 n) (𝓡 n) Phi x (d.fields ab.2 x))
    rw [transportedField_apply, transportedField_apply]
  change decode (fun a => d.fields a x) (pullbackProbes d Phi h x) = _
  rw [hprobe]
  exact decode_encode (fun a => d.fields a x) (d.parseval x) _

theorem smoothPullback_apply (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (h : SmoothTensor (n := n) (M := M)) (x : M) (v w : TangentSpace (𝓡 n) x) :
    smoothPullback d Phi h x v w =
      h (Phi x) (mfderiv (𝓡 n) (𝓡 n) Phi x v) (mfderiv (𝓡 n) (𝓡 n) Phi x w) := by
  rw [smoothPullback_eq_fiber]
  rfl

theorem smoothPullback_symm (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    smoothPullback d Phi h x v w = smoothPullback d Phi h x w v := by
  rw [smoothPullback_apply, smoothPullback_apply]
  exact hs _ _ _

theorem smoothPullback_refl (h : SmoothTensor (n := n) (M := M)) :
    smoothPullback d (Diffeomorph.refl (𝓡 n) M ∞) h = h := by
  ext x v w
  rw [smoothPullback_apply]
  simp only [Diffeomorph.coe_refl, mfderiv_id, ContinuousLinearMap.id_apply, id_eq]

def probeWeight (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (ab cd : d.ProbeIndex) (y : M) : ℝ :=
  transportCoefficient d Phi ab.1 cd.1 y * transportCoefficient d Phi ab.2 cd.2 y

theorem probeWeight_contMDiff (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (ab cd : d.ProbeIndex) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (probeWeight d Phi ab cd) :=
  (transportCoefficient_contMDiff d Phi ab.1 cd.1).mul
    (transportCoefficient_contMDiff d Phi ab.2 cd.2)

theorem scalarProbe_smoothPullback (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (h : SmoothTensor (n := n) (M := M)) (ab : d.ProbeIndex) (x : M) :
    scalarProbe d.fields (smoothPullback d Phi h) ab x =
      ∑ cd : d.ProbeIndex, probeWeight d Phi ab cd (Phi x) *
        scalarProbe d.fields h cd (Phi x) := by
  classical
  change smoothPullback d Phi h x (d.fields ab.1 x) (d.fields ab.2 x) = _
  rw [smoothPullback_apply, ← transportedField_apply, ← transportedField_apply,
    transportedField_eq_sum d Phi ab.1, transportedField_eq_sum d Phi ab.2]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [probeWeight, scalarProbe]
  ring

def pullbackTerms (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (ab cd : d.ProbeIndex) (w : List (Fin d.fieldCount)) :
    List (DirectionalTerm (n := n) (M := M) (iota := Fin d.fieldCount)) :=
  weightedWordTerms d.fields (transportCoefficient d Phi)
    (transportCoefficient_contMDiff d Phi) (probeWeight d Phi ab cd)
    (probeWeight_contMDiff d Phi ab cd) w

theorem pullbackTerms_order (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (ab cd : d.ProbeIndex) (w : List (Fin d.fieldCount)) :
    ∀ t ∈ pullbackTerms d Phi ab cd w, t.word.length ≤ w.length :=
  weightedWordTerms_order d.fields (transportCoefficient d Phi)
    (transportCoefficient_contMDiff d Phi) (probeWeight d Phi ab cd)
    (probeWeight_contMDiff d Phi ab cd) w

private theorem finiteScalarSum_contMDiff {iota : Type*} (s : Finset iota)
    (f : iota → M → ℝ) (hf : ∀ i ∈ s, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contMDiff_const (c := (0 : ℝ)))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem directionalWord_smoothPullback (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (h : SmoothTensor (n := n) (M := M)) (ab : d.ProbeIndex)
    (w : List (Fin d.fieldCount)) (x : M) :
    directionalWord d.fields w (scalarProbe d.fields (smoothPullback d Phi h) ab) x =
      ∑ cd : d.ProbeIndex, directionalTerms d.fields (pullbackTerms d Phi ab cd w)
        (scalarProbe d.fields h cd) (Phi x) := by
  classical
  let f (cd : d.ProbeIndex) : M → ℝ :=
    fun y => probeWeight d Phi ab cd y * scalarProbe d.fields h cd y
  have hf (cd : d.ProbeIndex) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f cd) :=
    (probeWeight_contMDiff d Phi ab cd).mul (scalarProbe_contMDiff d.fields h cd)
  have heq : scalarProbe d.fields (smoothPullback d Phi h) ab =
      (fun y => ∑ cd : d.ProbeIndex, f cd y) ∘ Phi :=
    funext (scalarProbe_smoothPullback d Phi h ab)
  rw [heq, directionalWord_comp Phi d.fields w
      (finiteScalarSum_contMDiff Finset.univ f (fun cd _ => hf cd)),
    directionalWord_sum Finset.univ (fun i => transportedField Phi (d.fields i))
      w f (fun cd _ => hf cd)]
  apply Finset.sum_congr rfl
  intro cd _
  exact (weightedWordTerms_eq d.fields (transportCoefficient d Phi)
    (transportCoefficient_contMDiff d Phi) (fun i => transportedField Phi (d.fields i))
    (transportedField_eq_sum d Phi) (probeWeight d Phi ab cd)
    (probeWeight_contMDiff d Phi ab cd) w (scalarProbe_contMDiff d.fields h cd) (Phi x)).symm

variable [MeasurableSpace M] [BorelSpace M]

def pullbackWordBefore (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (k : ℕ) (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ k) :
    ProbeTuples d k →L[ℝ] Lp ℝ 2 d.charts.measure :=
  ∑ cd : d.ProbeIndex,
    (termsL2 d.charts.measure (pullbackTerms d Phi ab cd w)
      (fun t ht => (pullbackTerms_order d Phi ab cd w t ht).trans hw)).comp
        (ContinuousLinearMap.proj cd)

theorem pullbackWordBefore_ae_eq (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (k : ℕ) (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ k)
    (Q : ProbeTuples d k) (h : SmoothTensor (n := n) (M := M))
    (hQ : ∀ cd v (hv : v.length ≤ k), Q cd (wordIndex v hv) =ᵐ[d.charts.measure]
      directionalWord d.fields v (scalarProbe d.fields h cd)) :
    pullbackWordBefore d Phi k ab w hw Q =ᵐ[d.charts.measure]
      fun y => ∑ cd : d.ProbeIndex, directionalTerms d.fields (pullbackTerms d Phi ab cd w)
        (scalarProbe d.fields h cd) y := by
  let q (cd : d.ProbeIndex) : Lp ℝ 2 d.charts.measure :=
    termsL2 d.charts.measure (pullbackTerms d Phi ab cd w)
      (fun t ht => (pullbackTerms_order d Phi ab cd w t ht).trans hw) (Q cd)
  have hq (cd : d.ProbeIndex) : q cd =ᵐ[d.charts.measure]
      directionalTerms d.fields (pullbackTerms d Phi ab cd w) (scalarProbe d.fields h cd) :=
    termsL2_ae_eq d.fields d.charts.measure _ _ (Q cd) _ (hQ cd)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ q, ae_all_iff.mpr hq]
    with x hsum hterms
  simp only [pullbackWordBefore, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change (∑ cd : d.ProbeIndex, q cd) x = _
  rw [hsum]
  simp only [hterms]

section Dominated

variable (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) {C : ℝ≥0∞}
  (hC : C ≠ ⊤) (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure)

def pullbackTuple (k : ℕ) : ProbeTuples d k →L[ℝ] ProbeTuples d k :=
  ContinuousLinearMap.pi (fun ab => ContinuousLinearMap.pi (fun w =>
    (dominatedPullbackL2 Phi Phi.continuous.measurable.aemeasurable hC hdom).comp
      (pullbackWordBefore d Phi k ab (List.ofFn w.2)
        (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt))))

theorem pullbackTuple_ae_eq (k : ℕ) (Q : ProbeTuples d k)
    (h : SmoothTensor (n := n) (M := M))
    (hQ : ∀ cd v (hv : v.length ≤ k), Q cd (wordIndex v hv) =ᵐ[d.charts.measure]
      directionalWord d.fields v (scalarProbe d.fields h cd))
    (ab : d.ProbeIndex) (w : List (Fin d.fieldCount)) (hw : w.length ≤ k) :
    pullbackTuple d Phi hC hdom k Q ab (wordIndex w hw) =ᵐ[d.charts.measure]
      directionalWord d.fields w (scalarProbe d.fields (smoothPullback d Phi h) ab) := by
  have heq := pullbackWordBefore_ae_eq d Phi k ab w hw Q h hQ
  have hcomp := ae_of_ae_map Phi.continuous.measurable.aemeasurable
    (ae_mono hdom (Measure.ae_smul_measure heq C))
  have hp := dominatedPullbackL2_coe Phi Phi.continuous.measurable.aemeasurable hC hdom
    (pullbackWordBefore d Phi k ab w hw Q)
  change dominatedPullbackL2 Phi Phi.continuous.measurable.aemeasurable hC hdom
      (pullbackWordBefore d Phi k ab (List.ofFn (wordIndex w hw).2) _ Q) =ᵐ[_] _
  simp only [wordIndex_word]
  filter_upwards [hp, hcomp] with x hx hc
  exact hx.trans (hc.trans (directionalWord_smoothPullback d Phi h ab w x).symm)

theorem pullbackTuple_smoothProbeTuples (k : ℕ) (h : SmoothTensor (n := n) (M := M)) :
    pullbackTuple d Phi hC hdom k (smoothProbeTuples d k h) =
      smoothProbeTuples d k (smoothPullback d Phi h) := by
  funext ab w
  apply Lp.ext
  have hw : (List.ofFn w.2).length ≤ k := by
    simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt
  have ha := pullbackTuple_ae_eq d Phi hC hdom k (smoothProbeTuples d k h) h
    (smoothProbeTuples_ae_eq d k h) ab (List.ofFn w.2) hw
  have hb := smoothProbeTuples_ae_eq d k (smoothPullback d Phi h) ab (List.ofFn w.2) hw
  have hi : wordIndex (List.ofFn w.2) hw = w := by
    rcases w with ⟨⟨j, hj⟩, w⟩
    simp [wordIndex]
    apply (Fin.heq_fun_iff (List.length_ofFn (f := w))).mpr
    intro i
    exact List.get_ofFn w i
  rw [hi] at ha hb
  exact ha.trans hb.symm

variable (L : FiniteChartLocalizationData d.charts)

def evenPullback (r : ℕ) : State d.SymmetricIndex →L[ℝ] State d.SymmetricIndex :=
  (evenOutput d r).comp ((pullbackTuple d Phi hC hdom (2 * r)).comp
    (nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl))

theorem evenPullback_smoothTensorCoordinates (r : ℕ)
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    evenPullback d Phi hC hdom L r (d.smoothTensorCoordinates (2 * r) h hs) =
      d.smoothTensorCoordinates (2 * r) (smoothPullback d Phi h)
        (smoothPullback_symm d Phi h hs) := by
  change evenOutput d r (pullbackTuple d Phi hC hdom (2 * r)
    (nativeProbeTupleL2 d L (2 * r) (2 * r) le_rfl
      (d.smoothTensorCoordinates (2 * r) h hs))) = _
  rw [nativeProbeTupleL2_eq_smoothProbeTuples, pullbackTuple_smoothProbeTuples,
    evenOutput_smoothProbeTuples]

end Dominated

theorem scaleDecode_smoothTensorCoordinates (k l : ℕ)
    (h : SmoothTensor (n := n) (M := M))
    (hs : ∀ (x : M) (v w : TangentSpace (𝓡 n) x), h x v w = h x w v) :
    scaleDecode d.symmetricParameters l (d.smoothTensorCoordinates (k + l) h hs) =
      d.smoothTensorCoordinates k h hs := by
  apply scaleDecode_injective d.symmetricParameters k
  calc
    _ = scaleDecode d.symmetricParameters (k + l)
        (d.smoothTensorCoordinates (k + l) h hs) := by
      rw [scaleDecode_add]
      rfl
    _ = d.symmetricBasis.repr (d.intoSymmetricValue h hs) :=
      scaleDecode_scaleEncode d.symmetricParameters (k + l) _ _
    _ = _ := (scaleDecode_scaleEncode d.symmetricParameters k _ _).symm

theorem evenPullback_refl (L : FiniteChartLocalizationData d.charts) (r : ℕ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdom : d.charts.measure.map (Diffeomorph.refl (𝓡 n) M ∞) ≤ C • d.charts.measure)
    (z : State d.SymmetricIndex) :
    evenPullback d (Diffeomorph.refl (𝓡 n) M ∞) hC hdom L r z = z := by
  obtain ⟨h, hs, hlim⟩ := exists_smooth_symmetric_approximation d L r z
  have hout := ((evenPullback d (Diffeomorph.refl (𝓡 n) M ∞) hC hdom L r).continuous.tendsto _).comp hlim
  have hid (j : ℕ) : evenPullback d (Diffeomorph.refl (𝓡 n) M ∞) hC hdom L r
      (d.smoothTensorCoordinates (2 * r) (h j) (hs j)) =
        d.smoothTensorCoordinates (2 * r) (h j) (hs j) := by
    rw [evenPullback_smoothTensorCoordinates]
    simp only [smoothPullback_refl]
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, hid] using hout) hlim

theorem evenPullback_scaleDecode_two (L : FiniteChartLocalizationData d.charts)
    (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hdom : d.charts.measure.map Phi ≤ C • d.charts.measure)
    (r : ℕ) (z : State d.SymmetricIndex) :
    evenPullback d Phi hC hdom L r (scaleDecode d.symmetricParameters 2 z) =
      scaleDecode d.symmetricParameters 2 (evenPullback d Phi hC hdom L (r + 1) z) := by
  obtain ⟨h, hs, hlim⟩ := exists_smooth_symmetric_approximation d L (r + 1) z
  have hlevel : 2 * (r + 1) = 2 * r + 2 := by omega
  have hsmooth (j : ℕ) :
      evenPullback d Phi hC hdom L r (scaleDecode d.symmetricParameters 2
        (d.smoothTensorCoordinates (2 * (r + 1)) (h j) (hs j))) =
      scaleDecode d.symmetricParameters 2 (evenPullback d Phi hC hdom L (r + 1)
        (d.smoothTensorCoordinates (2 * (r + 1)) (h j) (hs j))) := by
    rw [evenPullback_smoothTensorCoordinates, hlevel,
      scaleDecode_smoothTensorCoordinates, scaleDecode_smoothTensorCoordinates,
      evenPullback_smoothTensorCoordinates]
  have hleft := ((evenPullback d Phi hC hdom L r).continuous.tendsto _).comp
    (((scaleDecode d.symmetricParameters 2).continuous.tendsto _).comp hlim)
  have hright := ((scaleDecode d.symmetricParameters 2).continuous.tendsto _).comp
    (((evenPullback d Phi hC hdom L (r + 1)).continuous.tendsto _).comp hlim)
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, hsmooth] using hleft) hright

section UniformMeasure

variable (L : FiniteChartLocalizationData d.charts)

def patchBuffer (a : L.patches) : Set M :=
  {x | L.lowerConstant a / 2 ≤ d.charts.weight a.val.1 x}

theorem patchBuffer_isCompact (a : L.patches) : IsCompact (patchBuffer d L a) :=
  (isClosed_le continuous_const (d.charts.weight a.val.1).continuous).isCompact

theorem patchBuffer_subset_source (a : L.patches) :
    patchBuffer d L a ⊆ (L.chart a).source := by
  intro x hx
  have hpos : 0 < d.charts.weight a.val.1 x :=
    (div_pos (L.lowerConstant_pos a) (by norm_num : (0 : ℝ) < 2)).trans_le hx
  exact d.charts.weight_support_subset a.val.1
    (subset_tsupport (d.charts.weight a.val.1) hpos.ne')

theorem patch_coordinate_volume_le (a : L.patches) {S : Set M}
    (hS : MeasurableSet S) (hSK : S ⊆ tsupport (L.weight a)) :
    volume (L.chart a '' S) ≤
      (ENNReal.ofReal (L.lowerConstant a))⁻¹ * d.charts.measure S := by
  have hA := (L.region_open a).measurableSet
  have hmeas : AEMeasurable (L.chart a).symm (volume.restrict (L.region a)) :=
    ((L.chart a).symm.continuousOn.mono (L.region_subset_target a)).aemeasurable hA
  have hdom := le_inv_smul_of_smul_le
    (ne_of_gt (ENNReal.ofReal_pos.mpr (L.lowerConstant_pos a))) ENNReal.ofReal_ne_top
    (L.region_measure_lower a)
  have hbound := (Measure.le_iff.mp hdom) S hS
  rw [Measure.map_apply_of_aemeasurable hmeas hS, Measure.restrict_apply' hA,
    Measure.smul_apply, smul_eq_mul] at hbound
  have hset : (L.chart a).symm ⁻¹' S ∩ L.region a = L.chart a '' S := by
    ext z
    constructor
    · rintro ⟨hzS, hzA⟩
      exact ⟨(L.chart a).symm z, hzS, (L.chart a).right_inv (L.region_subset_target a hzA)⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, L.supportImage_subset_region a ⟨x, hSK hx, rfl⟩⟩
      change (L.chart a).symm (L.chart a x) ∈ S
      rwa [(L.chart a).left_inv (L.weight_support_source a (hSK hx))]
  rwa [hset] at hbound

theorem exists_patch_support (x : M) : ∃ a : L.patches, x ∈ tsupport (L.weight a) := by
  classical
  by_contra h
  have hz : ∀ a : L.patches, L.weight a x = 0 := by
    intro a
    by_contra ha
    exact h ⟨a, subset_tsupport (L.weight a) ha⟩
  have hsum := L.weight_sum x
  simp only [hz, Finset.sum_const_zero] at hsum
  exact zero_ne_one hsum

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  (Phi : P → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)

def inverseCoordinateMap (a : L.patches) (q : P × E) : E :=
  L.chart a ((Phi q.1).symm ((L.chart a).symm q.2))

theorem inverseCoordinateMap_contDiffAt
    (hzero : Phi 0 = Diffeomorph.refl (𝓡 n) M ∞)
    (hsmooth : ∀ x : M, ContMDiffAt (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : P × M => (Phi q.1).symm q.2) (0, x))
    (a : L.patches) {z : E} (hz : z ∈ (L.chart a).target) :
    ContDiffAt ℝ ∞ (inverseCoordinateMap d L Phi a) (0, z) := by
  have hi : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ (L.chart a).symm z :=
    (contMDiffOn_chart_symm (I := 𝓡 n) (x := a.val.1.val)).contMDiffAt
      ((L.chart a).open_target.mem_nhds hz)
  have hsrc : (Phi 0).symm ((L.chart a).symm z) ∈ (L.chart a).source := by
    simpa only [hzero, Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq] using
      (L.chart a).map_target hz
  have ho : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ (L.chart a)
      ((Phi 0).symm ((L.chart a).symm z)) :=
    (contMDiffOn_chart (I := 𝓡 n) (x := a.val.1.val)).contMDiffAt
      ((L.chart a).open_source.mem_nhds hsrc)
  have hm := (hsmooth ((L.chart a).symm z)).comp (0, z)
    (contMDiffAt_fst.prodMk (hi.comp (0, z) contMDiffAt_snd))
  have h := ho.comp (0, z) hm
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  exact h.contDiffAt

theorem inverseCoordinateMap_spatialDerivative_zero
    (hzero : Phi 0 = Diffeomorph.refl (𝓡 n) M ∞)
    (a : L.patches) {z : E} (hz : z ∈ (L.chart a).target) :
    fderiv ℝ (fun y => inverseCoordinateMap d L Phi a (0, y)) z =
      ContinuousLinearMap.id ℝ E := by
  have heq : (fun y => inverseCoordinateMap d L Phi a (0, y)) =ᶠ[𝓝 z] id := by
    filter_upwards [(L.chart a).open_target.mem_nhds hz] with y hy
    simp only [inverseCoordinateMap, hzero, Diffeomorph.symm_refl,
      Diffeomorph.coe_refl, id_eq, (L.chart a).right_inv hy]
  exact ((hasFDerivAt_id z).congr_of_eventuallyEq heq).fderiv

theorem eventually_inverse_coordinate_volume_bound
    (hzero : Phi 0 = Diffeomorph.refl (𝓡 n) M ∞)
    (hsmooth : ∀ x : M, ContMDiffAt (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : P × M => (Phi q.1).symm q.2) (0, x)) (a : L.patches) :
    ∀ᶠ p in 𝓝 (0 : P), ∀ A : Set E, MeasurableSet A → A ⊆ L.supportImage a →
      volume ((fun z => inverseCoordinateMap d L Phi a (p, z)) '' A) ≤
        ENNReal.ofReal 2 * volume A := by
  let H := inverseCoordinateMap d L Phi a
  let D (q : P × E) : E →L[ℝ] E :=
    (fderiv ℝ H q).comp (ContinuousLinearMap.inr ℝ P E)
  have hloc (z : E) (hz : z ∈ L.supportImage a) :
      ∀ᶠ q in 𝓝 ((0 : P), z), DifferentiableAt ℝ H q ∧ |(D q).det| < 2 := by
    have hzt := L.region_subset_target a (L.supportImage_subset_region a hz)
    have hH := inverseCoordinateMap_contDiffAt d L Phi hzero hsmooth a hzt
    have hder : fderiv ℝ (fun y => H (0, y)) z = D (0, z) :=
      ((hH.differentiableAt (by simp)).hasFDerivAt.comp z
        (hasFDerivAt_prodMk_right (0 : P) z)).fderiv
    have hD : D (0, z) = ContinuousLinearMap.id ℝ E :=
      hder.symm.trans (inverseCoordinateMap_spatialDerivative_zero d L Phi hzero a hzt)
    have hc : ContinuousAt (fun q => |(D q).det|) (0, z) :=
      (ContinuousLinearMap.continuous_det.continuousAt.comp
        ((hH.continuousAt_fderiv (by simp)).clm_comp continuousAt_const)).abs
    have hlt : |(D (0, z)).det| < 2 := by
      rw [hD]
      change |LinearMap.det (LinearMap.id : E →ₗ[ℝ] E)| < 2
      rw [LinearMap.det_id]
      norm_num
    have hH1 : ContDiffAt ℝ 1 H (0, z) := hH.of_le (by simp)
    filter_upwards [hH1.eventually (by norm_num), hc (Iio_mem_nhds hlt)] with q hq hqdet
    exact ⟨hq.differentiableAt (by norm_num), hqdet⟩
  filter_upwards [(L.supportImage_compact a).eventually_forall_of_forall_eventually
    (P := fun p z => DifferentiableAt ℝ H (p, z) ∧ |(D (p, z)).det| < 2) hloc]
    with p hp
  intro A hA hAK
  calc
    _ ≤ ∫⁻ z in A, ENNReal.ofReal |(D (p, z)).det| := by
      apply addHaar_image_le_lintegral_abs_det_fderiv volume hA
      intro z hz
      exact ((hp z (hAK hz)).1.hasFDerivAt.comp z
        (hasFDerivAt_prodMk_right p z)).hasFDerivWithinAt
    _ ≤ ∫⁻ _z in A, ENNReal.ofReal 2 := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with z hz
      exact ENNReal.ofReal_le_ofReal (hp z (hAK hz)).2.le
    _ = _ := by simp

theorem eventually_inverse_maps_patch_buffer
    (hzero : Phi 0 = Diffeomorph.refl (𝓡 n) M ∞)
    (hsmooth : ∀ x : M, ContMDiffAt (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : P × M => (Phi q.1).symm q.2) (0, x)) (a : L.patches) :
    ∀ᶠ p in 𝓝 (0 : P), MapsTo (Phi p).symm (tsupport (L.weight a)) (patchBuffer d L a) := by
  apply (isClosed_tsupport (L.weight a)).isCompact.eventually_forall_of_forall_eventually
  intro x hx
  have hc : ContinuousAt (fun q : P × M => d.charts.weight a.val.1 ((Phi q.1).symm q.2))
      (0, x) := (d.charts.weight a.val.1).continuous.continuousAt.comp (hsmooth x).continuousAt
  have hxpos : L.lowerConstant a < d.charts.weight a.val.1 x := (L.support_subset a hx).2
  have hlt : L.lowerConstant a / 2 < d.charts.weight a.val.1 ((Phi 0).symm x) := by
    simp only [hzero, Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq]
    linarith [L.lowerConstant_pos a]
  filter_upwards [hc (Ioi_mem_nhds hlt)] with q hq
  change L.lowerConstant a / 2 < d.charts.weight a.val.1 ((Phi q.1).symm q.2) at hq
  exact hq.le

include L in

theorem exists_locally_uniform_measure_domination
    (hzero : Phi 0 = Diffeomorph.refl (𝓡 n) M ∞)
    (hsmooth : ∀ x : M, ContMDiffAt (𝓘(ℝ, P).prod (𝓡 n)) (𝓡 n) ∞
      (fun q : P × M => (Phi q.1).symm q.2) (0, x)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ N : Set P, N ∈ 𝓝 0 ∧
      ∀ p ∈ N, d.charts.measure.map (Phi p) ≤ C • d.charts.measure := by
  classical
  choose A hA hupper using fun a : L.patches =>
    d.charts.exists_measure_restrict_le_chart a.val.1.val
      (patchBuffer_isCompact d L a) (patchBuffer_subset_source d L a)
  let C : ℝ≥0∞ := ∑ a : L.patches,
    A a * ENNReal.ofReal 2 * (ENNReal.ofReal (L.lowerConstant a))⁻¹
  have hC : C ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro a _
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hA a) ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (L.lowerConstant_pos a))))
  have hevent : ∀ᶠ p in 𝓝 (0 : P), ∀ a : L.patches,
      MapsTo (Phi p).symm (tsupport (L.weight a)) (patchBuffer d L a) ∧
      ∀ S : Set E, MeasurableSet S → S ⊆ L.supportImage a →
        volume ((fun z => inverseCoordinateMap d L Phi a (p, z)) '' S) ≤
          ENNReal.ofReal 2 * volume S := by
    apply Filter.eventually_all.mpr
    intro a
    exact (eventually_inverse_maps_patch_buffer d L Phi hzero hsmooth a).and
      (eventually_inverse_coordinate_volume_bound d L Phi hzero hsmooth a)
  refine ⟨C, hC, {p | ∀ a : L.patches,
      MapsTo (Phi p).symm (tsupport (L.weight a)) (patchBuffer d L a) ∧
      ∀ S : Set E, MeasurableSet S → S ⊆ L.supportImage a →
        volume ((fun z => inverseCoordinateMap d L Phi a (p, z)) '' S) ≤
          ENNReal.ofReal 2 * volume S}, hevent, ?_⟩
  intro p hp
  apply Measure.le_iff.mpr
  intro S hS
  let T (a : L.patches) : Set M := (Phi p).symm '' (S ∩ tsupport (L.weight a))
  have hT (a : L.patches) : MeasurableSet (T a) :=
    (Phi p).symm.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (hS.inter (isClosed_tsupport (L.weight a)).measurableSet)
  have hTJ (a : L.patches) : T a ⊆ patchBuffer d L a := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hp a).1 hx.2
  have hlocal (a : L.patches) : d.charts.measure (T a) ≤
      (A a * ENNReal.ofReal 2 * (ENNReal.ofReal (L.lowerConstant a))⁻¹) *
        d.charts.measure S := by
    have hu := (Measure.le_iff.mp (hupper a)) (T a) (hT a)
    rw [Measure.restrict_apply (hT a), inter_eq_left.mpr (hTJ a),
      Measure.smul_apply, smul_eq_mul] at hu
    change d.charts.measure (T a) ≤
      A a * coordinatePushforward (L.chart a) (patchBuffer d L a) (T a) at hu
    rw [coordinatePushforward_apply (L.chart a) (patchBuffer_isCompact d L a).measurableSet
        (patchBuffer_subset_source d L a) (hT a), inter_eq_left.mpr (hTJ a)] at hu
    have himage : L.chart a '' T a =
        (fun z => inverseCoordinateMap d L Phi a (p, z)) ''
          (L.chart a '' (S ∩ tsupport (L.weight a))) := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨L.chart a x, ⟨x, hx, rfl⟩, ?_⟩
        simp only [inverseCoordinateMap,
          (L.chart a).left_inv (L.weight_support_source a hx.2)]
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨(Phi p).symm x, ⟨x, hx, rfl⟩, ?_⟩
        simp only [inverseCoordinateMap,
          (L.chart a).left_inv (L.weight_support_source a hx.2)]
    have hv := (hp a).2 (L.chart a '' (S ∩ tsupport (L.weight a)))
      (measurableSet_chart_image (L.chart a)
        (hS.inter (isClosed_tsupport (L.weight a)).measurableSet)
        (inter_subset_right.trans (L.weight_support_source a)))
      (image_mono inter_subset_right)
    have hlower := patch_coordinate_volume_le d L a
      (hS.inter (isClosed_tsupport (L.weight a)).measurableSet) inter_subset_right
    calc
      _ ≤ A a * volume (L.chart a '' T a) := hu
      _ ≤ A a * (ENNReal.ofReal 2 * volume (L.chart a '' (S ∩ tsupport (L.weight a)))) := by
        rw [himage]
        exact mul_le_mul_right hv (A a)
      _ ≤ A a * (ENNReal.ofReal 2 *
          ((ENNReal.ofReal (L.lowerConstant a))⁻¹ * d.charts.measure S)) := by
        apply mul_le_mul_right
        apply mul_le_mul_right
        exact hlower.trans (mul_le_mul_right (measure_mono inter_subset_left) _)
      _ = _ := by ac_rfl
  have hcover : (Phi p) ⁻¹' S ⊆ ⋃ a : L.patches, T a := by
    intro x hx
    obtain ⟨a, ha⟩ := exists_patch_support d L (Phi p x)
    exact mem_iUnion.mpr ⟨a, Phi p x, ⟨hx, ha⟩, (Phi p).symm_apply_apply x⟩
  rw [Measure.map_apply (Phi p).continuous.measurable hS, Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ d.charts.measure (⋃ a : L.patches, T a) := measure_mono hcover
    _ ≤ ∑ a : L.patches, d.charts.measure (T a) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ a : L.patches,
        (A a * ENNReal.ofReal 2 * (ENNReal.ofReal (L.lowerConstant a))⁻¹) *
          d.charts.measure S := Finset.sum_le_sum (fun a _ => hlocal a)
    _ = C * d.charts.measure S := by rw [← Finset.sum_mul]

end UniformMeasure

section ScalarContinuity

variable {X : Type*} [TopologicalSpace X]
  (Phi : X → Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
  {C : ℝ≥0∞} (hC : C ≠ ⊤)
  (hdom : ∀ p, d.charts.measure.map (Phi p) ≤ C • d.charts.measure)

theorem continuous_dominatedPullbackL2
    (hPhi : Continuous (fun q : X × M => Phi q.1 q.2)) :
    Continuous (fun q : X × Lp ℝ 2 d.charts.measure =>
      dominatedPullbackL2 (Phi q.1) (Phi q.1).continuous.measurable.aemeasurable
        hC (hdom q.1) q.2) := by
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace (𝓡 n) M
  letI : d.charts.measure.WeaklyRegular := inferInstance
  let K : NNReal := ⟨C.toReal ^ (1 / (2 : ℝ≥0∞)).toReal,
    Real.rpow_nonneg ENNReal.toReal_nonneg _⟩
  apply continuous_prod_of_dense_continuous_lipschitzWith' _ K
    (ContinuousMap.toLp_denseRange (p := (2 : ENNReal)) ℝ d.charts.measure ℝ (by simp))
  · intro p
    exact ContinuousLinearMap.lipschitzWith_of_opNorm_le (K := K)
      (norm_dominatedPullbackL2_le («E» := ℝ) (Phi p)
        (Phi p).continuous.measurable.aemeasurable hC (hdom p))
  · rintro _ ⟨f, rfl⟩
    let family (p : X) : C(M, ℝ) :=
      ⟨fun x => f (Phi p x), f.continuous.comp (Phi p).continuous⟩
    have hfamily : Continuous family :=
      ContinuousMap.continuous_of_continuous_uncurry family (f.continuous.comp hPhi)
    have heq (p : X) : dominatedPullbackL2 (Phi p)
        (Phi p).continuous.measurable.aemeasurable hC (hdom p)
          (ContinuousMap.toLp 2 d.charts.measure ℝ f) =
        ContinuousMap.toLp 2 d.charts.measure ℝ (family p) := by
      apply Lp.ext
      have hp := dominatedPullbackL2_coe (Phi p)
        (Phi p).continuous.measurable.aemeasurable hC (hdom p)
        (ContinuousMap.toLp 2 d.charts.measure ℝ f)
      have hf := ae_of_ae_map (Phi p).continuous.measurable.aemeasurable
        (ae_mono (hdom p) (Measure.ae_smul_measure
          (ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (𝕜 := ℝ) d.charts.measure f) C))
      filter_upwards [hp, hf,
        ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (𝕜 := ℝ) d.charts.measure (family p)]
        with x hx hfx hfamilyx
      exact hx.trans (hfx.trans hfamilyx.symm)
    simpa only [Function.comp_def, heq] using
      (ContinuousMap.toLp 2 d.charts.measure ℝ).continuous.comp hfamily

theorem dominatedPullbackL2_refl {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdom : d.charts.measure.map (Diffeomorph.refl (𝓡 n) M ∞) ≤ C • d.charts.measure)
    (f : Lp ℝ 2 d.charts.measure) :
    dominatedPullbackL2 (Diffeomorph.refl (𝓡 n) M ∞)
      (Diffeomorph.refl (𝓡 n) M ∞).continuous.measurable.aemeasurable hC hdom f = f := by
  apply Lp.ext
  simpa only [Diffeomorph.coe_refl, Function.comp_id] using
    dominatedPullbackL2_coe (Diffeomorph.refl (𝓡 n) M ∞)
      (Diffeomorph.refl (𝓡 n) M ∞).continuous.measurable.aemeasurable hC hdom f

end ScalarContinuity

end PoincareConjecture.DeTurckStatePullbackNative

end
