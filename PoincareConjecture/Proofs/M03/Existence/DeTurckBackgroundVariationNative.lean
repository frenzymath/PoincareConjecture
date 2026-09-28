import PoincareConjecture.Proofs.M03.Existence.DeTurckMixedForcingNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckTensorForcingNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix.Norms.Elementwise

namespace PoincareConjecture.DeTurckBackgroundVariationNative

open TensorProbeNative DeTurckNative DeTurckRationalJetNative DeTurckSourceJetNative
  DeTurckJetCoordinatesNative DeTurckJetAffineNative DeTurckCompatibleJetNative
  DeTurckMetricProducerNative DeTurckTensorForcingNative

variable {n : ℕ}

theorem source_background_difference (B C q : MetricJet2 (n := n)) (i j : Fin n) :
    ricciDeTurckSource B q i j - ricciDeTurckSource C q i j =
      ricciDeTurckSource B (eraseSecondJet q) i j -
        ricciDeTurckSource C (eraseSecondJet q) i j := by
  rw [ricciDeTurckSource_split B q, ricciDeTurckSource_split C q]
  ring

variable {M iota : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [Fintype iota] (F : iota → SmoothField (n := n) (M := M))
  {base : M} {K : Set M} (C : Cutoffs (n := n) base K) (g0 : RiemannianMetric n M)

def varyingLowAtom (p : Expr (Fin n ⊕ iota) n) (m kb : ℕ)
    (hbg : p.metricOrder true ≤ kb)
    (InvB InvC : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ)) :
    LowAtom p m → (NativeProbeContinuous (M := M) (iota := iota) kb ×
      NativeProbeContinuous (M := M) (iota := iota) m) → C(M, ℝ)
  | ⟨⟨.metric false word i j, _⟩, hw⟩, Q => matrixWordContinuous F C g0 word hw i j Q.2
  | ⟨⟨.metric true word i j, ha⟩, _⟩, Q => matrixWordContinuous F C g0 word
      ((p.word_length_le_metricOrder_of_mem true word i j ha).trans hbg) i j Q.1
  | ⟨⟨.inverse false i j, _⟩, _⟩, Q => inverseEntryContinuous F C g0 InvC i j Q.2
  | ⟨⟨.inverse true i j, _⟩, _⟩, Q => inverseEntryContinuous F C g0 InvB i j Q.1

theorem contDiff_varyingLowAtom (p : Expr (Fin n ⊕ iota) n) (m kb : ℕ)
    (hbg : p.metricOrder true ≤ kb)
    (InvB InvC : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    (hInvB : ContDiff ℝ ∞ InvB) (hInvC : ContDiff ℝ ∞ InvC) (a : LowAtom p m) :
    ContDiff ℝ ∞ (varyingLowAtom F C g0 p m kb hbg InvB InvC a) := by
  rcases a with ⟨⟨a, ha⟩, hw⟩
  cases a with
  | metric b word i j =>
    cases b with
    | false => exact (contDiff_matrixWordContinuous F C g0 word hw i j).comp contDiff_snd
    | true => exact (contDiff_matrixWordContinuous F C g0 word
        ((p.word_length_le_metricOrder_of_mem true word i j ha).trans hbg) i j).comp contDiff_fst
  | inverse b i j =>
    cases b with
    | false => exact (contDiff_inverseEntryContinuous F C g0 InvC hInvC i j).comp contDiff_snd
    | true => exact (contDiff_inverseEntryContinuous F C g0 InvB hInvB i j).comp contDiff_fst

def varyingLowTuple (p : Expr (Fin n ⊕ iota) n) (m kb : ℕ)
    (hbg : p.metricOrder true ≤ kb)
    (InvB InvC : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : NativeProbeContinuous (M := M) (iota := iota) kb ×
      NativeProbeContinuous (M := M) (iota := iota) m) : C(M, LowAtom p m → ℝ) :=
  packContinuous (fun a => varyingLowAtom F C g0 p m kb hbg InvB InvC a Q)

theorem contDiff_varyingLowTuple (p : Expr (Fin n ⊕ iota) n) (m kb : ℕ)
    (hbg : p.metricOrder true ≤ kb)
    (InvB InvC : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    (hInvB : ContDiff ℝ ∞ InvB) (hInvC : ContDiff ℝ ∞ InvC) :
    ContDiff ℝ ∞ (varyingLowTuple F C g0 p m kb hbg InvB InvC) := by
  apply (packContinuous (M := M) (A := LowAtom p m)).contDiff.comp
  exact contDiff_pi.mpr (contDiff_varyingLowAtom F C g0 p m kb hbg InvB InvC hInvB hInvC)

theorem varyingLowTuple_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (p : Expr (Fin n ⊕ iota) n) (m kb : ℕ) (hbg : p.metricOrder true ≤ kb)
    (InvB InvC : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    (QB : NativeProbeContinuous (M := M) (iota := iota) kb)
    (QC : NativeProbeContinuous (M := M) (iota := iota) m)
    (background g : RiemannianMetric n M)
    (hQB : ∀ ab w (hw : w.length ≤ kb) x,
      QB ab (wordIndex w hw) x = directionalWord F w (probeDifference F background g0 ab) x)
    (hQC : ∀ ab w (hw : w.length ≤ m) x,
      QC ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x)
    (hInvB : ∀ x, InvB (matrixValueContinuous F C g0 QB) x =
      (matrixValueContinuous F C g0 QB x)⁻¹)
    (hInvC : ∀ x, InvC (matrixValueContinuous F C g0 QC) x =
      (matrixValueContinuous F C g0 QC x)⁻¹) (x : M) (a : LowAtom p m) :
    varyingLowTuple F C g0 p m kb hbg InvB InvC (QB, QC) x a =
      nativeValues (combinedFields F C) (compatibleMatrix C background g) x a.val.val := by
  rw [varyingLowTuple, packContinuous_apply]
  rcases a with ⟨⟨a, ha⟩, hw⟩
  cases a with
  | metric b word i j =>
    cases b with
    | false => exact matrixWordContinuous_eq F C g0 hF word hw i j QC g hQC x
    | true =>
      exact matrixWordContinuous_eq F C g0 hF word
        ((p.word_length_le_metricOrder_of_mem true word i j ha).trans hbg) i j QB background hQB x
  | inverse b i j =>
    cases b with
    | false =>
      change InvC (matrixValueContinuous F C g0 QC) x i j = (C.matrix g x)⁻¹ i j
      rw [hInvC, matrixValueContinuous_eq F C g0 hF QC g hQC x]
    | true =>
      change InvB (matrixValueContinuous F C g0 QB) x i j = (C.matrix background x)⁻¹ i j
      rw [hInvB, matrixValueContinuous_eq F C g0 hF QB background hQB x]

variable (μ : Measure M) [IsFiniteMeasure μ]

def varyingHighAtom (p : Expr (Fin n ⊕ iota) n) (m kb kc : ℕ)
    (hbg : p.metricOrder true ≤ kb) (hcur : p.metricOrder false ≤ kc) :
    HighAtom p m → (NativeProbeContinuous (M := M) (iota := iota) kb ×
      NativeProbeL2 (iota := iota) μ kc) → Lp ℝ 2 μ
  | ⟨⟨.metric false word i j, ha⟩, _⟩, Q => matrixWordL2 F C g0 μ word
      ((p.word_length_le_metricOrder_of_mem false word i j ha).trans hcur) i j Q.2
  | ⟨⟨.metric true word i j, ha⟩, _⟩, Q => ContinuousMap.toLp 2 μ ℝ
      (matrixWordContinuous F C g0 word
        ((p.word_length_le_metricOrder_of_mem true word i j ha).trans hbg) i j Q.1)
  | ⟨⟨.inverse _ _ _, _⟩, hw⟩, _ => False.elim (hw (Nat.zero_le m))

theorem contDiff_varyingHighAtom (p : Expr (Fin n ⊕ iota) n) (m kb kc : ℕ)
    (hbg : p.metricOrder true ≤ kb) (hcur : p.metricOrder false ≤ kc) (a : HighAtom p m) :
    ContDiff ℝ ∞ (varyingHighAtom F C g0 μ p m kb kc hbg hcur a) := by
  rcases a with ⟨⟨a, ha⟩, hw⟩
  cases a with
  | metric b word i j =>
    cases b with
    | false => exact (contDiff_matrixWordL2 F C g0 μ word
        ((p.word_length_le_metricOrder_of_mem false word i j ha).trans hcur) i j).comp contDiff_snd
    | true =>
      exact (ContinuousMap.toLp 2 μ ℝ : C(M, ℝ) →L[ℝ] Lp ℝ 2 μ).contDiff.comp
        ((contDiff_matrixWordContinuous F C g0 word
          ((p.word_length_le_metricOrder_of_mem true word i j ha).trans hbg) i j).comp contDiff_fst)
  | inverse b i j => exact False.elim (hw (Nat.zero_le m))

def varyingHighTuple (p : Expr (Fin n ⊕ iota) n) (m kb kc : ℕ)
    (hbg : p.metricOrder true ≤ kb) (hcur : p.metricOrder false ≤ kc)
    (Q : NativeProbeContinuous (M := M) (iota := iota) kb ×
      NativeProbeL2 (iota := iota) μ kc) : Lp (HighAtom p m → ℝ) 2 μ :=
  packL2 μ (fun a => varyingHighAtom F C g0 μ p m kb kc hbg hcur a Q)

theorem contDiff_varyingHighTuple (p : Expr (Fin n ⊕ iota) n) (m kb kc : ℕ)
    (hbg : p.metricOrder true ≤ kb) (hcur : p.metricOrder false ≤ kc) :
    ContDiff ℝ ∞ (varyingHighTuple F C g0 μ p m kb kc hbg hcur) := by
  apply (packL2 (A := HighAtom p m) μ).contDiff.comp
  exact contDiff_pi.mpr (contDiff_varyingHighAtom F C g0 μ p m kb kc hbg hcur)

theorem varyingHighTuple_ae_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (p : Expr (Fin n ⊕ iota) n) (m kb kc : ℕ)
    (hbg : p.metricOrder true ≤ kb) (hcur : p.metricOrder false ≤ kc)
    (QB : NativeProbeContinuous (M := M) (iota := iota) kb)
    (HC : NativeProbeL2 (iota := iota) μ kc) (background g : RiemannianMetric n M)
    (hQB : ∀ ab w (hw : w.length ≤ kb) x,
      QB ab (wordIndex w hw) x = directionalWord F w (probeDifference F background g0 ab) x)
    (hHC : ∀ ab w (hw : w.length ≤ kc),
      HC ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) :
    varyingHighTuple F C g0 μ p m kb kc hbg hcur (QB, HC) =ᵐ[μ] fun x a =>
      nativeValues (combinedFields F C) (compatibleMatrix C background g) x a.val.val := by
  apply packL2_ae_eq
  intro a
  rcases a with ⟨⟨a, ha⟩, hw⟩
  cases a with
  | metric b word i j =>
    cases b with
    | false =>
      exact matrixWordL2_ae_eq F C g0 μ hF word
        ((p.word_length_le_metricOrder_of_mem false word i j ha).trans hcur) i j HC g hHC
    | true =>
      filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℝ)
        (matrixWordContinuous F C g0 word
          ((p.word_length_le_metricOrder_of_mem true word i j ha).trans hbg) i j QB)] with x hx
      exact hx.trans (matrixWordContinuous_eq F C g0 hF word
        ((p.word_length_le_metricOrder_of_mem true word i j ha).trans hbg) i j QB background hQB x)
  | inverse b i j => exact False.elim (hw (Nat.zero_le m))

theorem exists_smooth_varying_jet_action
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (p : Expr (Fin n ⊕ iota) n) (m kb kc : ℕ) (hp : p.degree ≤ 2 * m)
    (hbg : p.metricOrder true ≤ kb) (hcur : p.metricOrder false ≤ kc) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ Phi : (NativeProbeContinuous (M := M) (iota := iota) kb ×
          (NativeProbeContinuous (M := M) (iota := iota) m ×
            NativeProbeL2 (iota := iota) μ kc)) → Lp ℝ 2 μ,
      ContDiff ℝ ∞ Phi ∧
      ∀ QB : NativeProbeContinuous (M := M) (iota := iota) kb, ‖QB‖ < delta →
        ∀ QC : NativeProbeContinuous (M := M) (iota := iota) m, ‖QC‖ < delta →
        ∀ HC : NativeProbeL2 (iota := iota) μ kc, ∀ background g : RiemannianMetric n M,
        (∀ ab w (hw : w.length ≤ kb) x,
          QB ab (wordIndex w hw) x = directionalWord F w (probeDifference F background g0 ab) x) →
        (∀ ab w (hw : w.length ≤ m) x,
          QC ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x) →
        (∀ ab w (hw : w.length ≤ kc),
          HC ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) →
        Phi (QB, QC, HC) =ᵐ[μ] fun x =>
          p.eval (nativeValues (combinedFields F C) (compatibleMatrix C background g) x) := by
  obtain ⟨db, hdb, InvB, hInvB, hInvBEq⟩ := exists_smooth_native_inverse_extension F C g0 kb
  obtain ⟨dc, hdc, InvC, hInvC, hInvCEq⟩ := exists_smooth_native_inverse_extension F C g0 m
  let low := varyingLowTuple F C g0 p m kb hbg InvB InvC
  let high := varyingHighTuple F C g0 μ p m kb kc hbg hcur
  let Phi := fun z : NativeProbeContinuous (M := M) (iota := iota) kb ×
      (NativeProbeContinuous (M := M) (iota := iota) m × NativeProbeL2 (iota := iota) μ kc) =>
    finiteSpatialJetAction μ p m (low (z.1, z.2.1), high (z.1, z.2.2))
  have hlow : ContDiff ℝ ∞ low :=
    contDiff_varyingLowTuple F C g0 p m kb hbg InvB InvC hInvB hInvC
  have hhigh : ContDiff ℝ ∞ high := contDiff_varyingHighTuple F C g0 μ p m kb kc hbg hcur
  refine ⟨min db dc, lt_min hdb hdc, Phi, ?_, ?_⟩
  · exact (contDiff_finiteSpatialJetAction μ p m).comp
      ((hlow.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))).prodMk
        (hhigh.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))))
  · intro QB hQBsmall QC hQCsmall HC background g hQB hQC hHC
    apply finiteSpatialJetAction_ae_eq_eval μ p m hp
      (low (QB, QC), high (QB, HC))
      (fun x => nativeValues (combinedFields F C) (compatibleMatrix C background g) x)
    · intro x
      funext a
      exact (varyingLowTuple_eq F C g0 hF p m kb hbg InvB InvC QB QC background g hQB hQC
        (hInvBEq QB (hQBsmall.trans_le (min_le_left _ _)))
        (hInvCEq QC (hQCsmall.trans_le (min_le_right _ _))) x a).symm
    · exact (varyingHighTuple_ae_eq F C g0 μ hF p m kb kc hbg hcur
        QB HC background g hQB hHC).symm

private theorem ordered_sub (word : List iota) {f q : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hq : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ q) :
    directionalWord F word (fun x => f x - q x) =
      fun x => directionalWord F word f x - directionalWord F word q x := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    funext x
    rw [directionalWord_cons, ih]
    exact scalarDirectional_sub (F a)
      ((directionalWord_contMDiff F word hf).mdifferentiable (by simp) x)
      ((directionalWord_contMDiff F word hq).mdifferentiable (by simp) x)

private theorem ordered_zero (word : List iota) :
    directionalWord F word (fun _ : M => (0 : ℝ)) = fun _ => 0 := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    rw [directionalWord_cons, ih]
    funext x
    simp only [scalarDirectional, mfderiv_const]
    rfl

theorem zero_native_probes (kb : ℕ) (ab : iota × iota)
    (word : List iota) (hw : word.length ≤ kb) (x : M) :
    (0 : NativeProbeContinuous (M := M) (iota := iota) kb) ab (wordIndex word hw) x =
      directionalWord F word (probeDifference F g0 g0 ab) x := by
  have hp : probeDifference F g0 g0 ab = fun _ => 0 := by
    funext y
    exact sub_self _
  rw [hp, ordered_zero]
  rfl

def backgroundDifferenceEntry (background g : RiemannianMetric n M)
    (i j : Fin n) (x : M) : ℝ :=
  ricciDeTurckSource (C.jet background x) (C.jet g x) i j -
    ricciDeTurckSource (C.jet g0 x) (C.jet g x) i j

theorem backgroundDifferenceEntry_eq_lower (background g : RiemannianMetric n M)
    (i j : Fin n) (x : M) :
    backgroundDifferenceEntry C g0 background g i j x =
      lowerJetSource (C.jet background x) (backgroundLowerJet (C.jet g x)) i j -
        lowerJetSource (C.jet g0 x) (backgroundLowerJet (C.jet g x)) i j :=
  source_background_difference (C.jet background x) (C.jet g0 x) (C.jet g x) i j

include F in
theorem lowerSource_contMDiff (background g : RiemannianMetric n M) (i j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => lowerJetSource (C.jet background x) (backgroundLowerJet (C.jet g x)) i j) := by
  have heq : (fun x => lowerJetSource (C.jet background x) (backgroundLowerJet (C.jet g x)) i j) =
      fun x => (sourceExpr (Sum.inl : Fin n → Fin n ⊕ iota) true i j).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C background g) x) := by
    funext x
    exact (eval_lower_sourceExpr_compatible F C background g i j x).symm
  rw [heq]
  exact Expr.native_contMDiff _ (combinedFields F C) (compatibleMatrix C background g)
    (compatibleMatrix_contMDiff C background g) (compatibleMatrix_det_ne_zero C background g)

include F in
theorem backgroundDifferenceEntry_contMDiff (background g : RiemannianMetric n M)
    (i j : Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (backgroundDifferenceEntry C g0 background g i j) := by
  have heq : backgroundDifferenceEntry C g0 background g i j = fun x =>
      lowerJetSource (C.jet background x) (backgroundLowerJet (C.jet g x)) i j -
        lowerJetSource (C.jet g0 x) (backgroundLowerJet (C.jet g x)) i j :=
    funext (backgroundDifferenceEntry_eq_lower C g0 background g i j)
  rw [heq]
  exact (lowerSource_contMDiff F C background g i j).sub (lowerSource_contMDiff F C g0 g i j)

theorem ordered_backgroundDifferenceEntry (background g : RiemannianMetric n M)
    (i j : Fin n) (word : List iota) (x : M) :
    ((sourceExpr Sum.inl true i j).orderedDerivative (word.map Sum.inr)).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C background g) x) -
      ((sourceExpr Sum.inl true i j).orderedDerivative (word.map Sum.inr)).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      directionalWord F word (backgroundDifferenceEntry C g0 background g i j) x := by
  rw [ordered_lower_sourceExpr_compatible, ordered_lower_sourceExpr_compatible]
  have heq : backgroundDifferenceEntry C g0 background g i j = fun y =>
      lowerJetSource (C.jet background y) (backgroundLowerJet (C.jet g y)) i j -
        lowerJetSource (C.jet g0 y) (backgroundLowerJet (C.jet g y)) i j :=
    funext (backgroundDifferenceEntry_eq_lower C g0 background g i j)
  rw [heq, ordered_sub F word (lowerSource_contMDiff F C background g i j)
    (lowerSource_contMDiff F C g0 g i j)]

theorem backgroundDifferenceEntry_eq_intrinsic (background g : RiemannianMetric n M)
    (D : LeviCivitaData g) (B : LeviCivitaData background) (B0 : LeviCivitaData g0)
    {x : M} (hx : x ∈ K) (i j : Fin n) :
    backgroundDifferenceEntry C g0 background g i j x =
      (smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0) x
        (C.field i x) (C.field j x) := by
  have hsource (b : RiemannianMetric n M) (Db : LeviCivitaData b) :
      ricciDeTurckSource (C.jet b x) (C.jet g x) i j =
        smoothRicciDeTurckTensor D Db x (C.field i x) (C.field j x) := by
    rw [C.jet_eq_on b hx, C.jet_eq_on g hx,
      (C.field_eventuallyEq (C.zeta_one x (C.mem_eta_support hx)) i).eq_of_nhds,
      (C.field_eventuallyEq (C.zeta_one x (C.mem_eta_support hx)) j).eq_of_nhds,
      smoothRicciDeTurckTensor_apply]
    exact ricciDeTurckSource_frameMetricJet_eq_intrinsic D Db base
      (C.eta_support (C.mem_eta_support hx)) i j
  change ricciDeTurckSource (C.jet background x) (C.jet g x) i j -
    ricciDeTurckSource (C.jet g0 x) (C.jet g x) i j =
      smoothRicciDeTurckTensor D B x (C.field i x) (C.field j x) -
        smoothRicciDeTurckTensor D B0 x (C.field i x) (C.field j x)
  rw [hsource background B, hsource g0 B0]

private theorem backgroundOrder_le_degree {jota : Type*} (p : Expr jota n) (b : Bool) :
    p.metricOrder b ≤ p.degree := by
  induction p with
  | constant c => exact le_rfl
  | atom a =>
    cases a with
    | metric c word i j =>
      simp only [Expr.metricOrder, Expr.degree, Atom.weight]
      split_ifs <;> omega
    | inverse c i j => exact le_rfl
  | add p q hp hq => exact max_le_max hp hq
  | mul p q hp hq =>
    change max (p.metricOrder b) (q.metricOrder b) ≤ p.degree + q.degree
    omega
  | neg p hp => exact hp

theorem exists_smooth_background_word_action
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (k m : ℕ) (hkm : k + 2 ≤ 2 * m)
    (i j : Fin n) (word : List iota) (hw : word.length ≤ k) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ Psi : (NativeProbeContinuous (M := M) (iota := iota) (k + 2) ×
          (NativeProbeContinuous (M := M) (iota := iota) m ×
            NativeProbeL2 (iota := iota) μ (k + 1))) → Lp ℝ 2 μ,
      ContDiff ℝ ∞ Psi ∧ (∀ QC HC, Psi (0, QC, HC) = 0) ∧
      ∀ QB : NativeProbeContinuous (M := M) (iota := iota) (k + 2), ‖QB‖ < delta →
        ∀ QC : NativeProbeContinuous (M := M) (iota := iota) m, ‖QC‖ < delta →
        ∀ HC : NativeProbeL2 (iota := iota) μ (k + 1), ∀ background g : RiemannianMetric n M,
        (∀ ab w (hw : w.length ≤ k + 2) x,
          QB ab (wordIndex w hw) x = directionalWord F w (probeDifference F background g0 ab) x) →
        (∀ ab w (hw : w.length ≤ m) x,
          QC ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x) →
        (∀ ab w (hw : w.length ≤ k + 1),
          HC ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) →
        Psi (QB, QC, HC) =ᵐ[μ]
          directionalWord F word (backgroundDifferenceEntry C g0 background g i j) := by
  let p : Expr (Fin n ⊕ iota) n :=
    (sourceExpr Sum.inl true i j).orderedDerivative (word.map Sum.inr)
  have hpdeg : p.degree ≤ k + 2 := by
    have h := degree_ordered_sourceExpr_le (Sum.inl : Fin n → Fin n ⊕ iota)
      true i j (word.map Sum.inr)
    simp only [List.length_map] at h
    exact h.trans (by omega)
  have hpbg : p.metricOrder true ≤ k + 2 := (backgroundOrder_le_degree p true).trans hpdeg
  have hpcur : p.metricOrder false ≤ k + 1 := by
    have h := currentOrder_ordered_sourceExpr_lower (Sum.inl : Fin n → Fin n ⊕ iota)
      i j (word.map Sum.inr)
    simp only [List.length_map] at h
    exact h.trans (by omega)
  obtain ⟨delta, hdelta, Phi, hPhi, hEq⟩ := exists_smooth_varying_jet_action F C g0 μ hF
    p m (k + 2) (k + 1) (hpdeg.trans hkm) hpbg hpcur
  let Psi := fun z : NativeProbeContinuous (M := M) (iota := iota) (k + 2) ×
      (NativeProbeContinuous (M := M) (iota := iota) m ×
        NativeProbeL2 (iota := iota) μ (k + 1)) => Phi z - Phi (0, z.2)
  refine ⟨delta, hdelta, Psi, hPhi.sub (hPhi.comp (contDiff_const.prodMk contDiff_snd)),
    fun QC HC => sub_self _, ?_⟩
  intro QB hQBsmall QC hQCsmall HC background g hQB hQC hHC
  have hbg := hEq QB hQBsmall QC hQCsmall HC background g hQB hQC hHC
  have hbase := hEq 0 (by simpa only [norm_zero] using hdelta) QC hQCsmall HC g0 g
    (zero_native_probes F g0 (k + 2)) hQC hHC
  filter_upwards [Lp.coeFn_sub (Phi (QB, QC, HC)) (Phi (0, QC, HC)), hbg, hbase]
    with x hsub hb hc
  change (Phi (QB, QC, HC) - Phi (0, QC, HC)) x = _
  rw [hsub, Pi.sub_apply, hb, hc]
  exact ordered_backgroundDifferenceEntry F C g0 background g i j word x

section FiniteCover

variable (A : CompatibleChartCover (n := n) (M := M))

theorem backgroundDifferenceEntry_reconstruction (background g : RiemannianMetric n M)
    (D : LeviCivitaData g) (B : LeviCivitaData background) (B0 : LeviCivitaData g0)
    (ab : iota × iota) :
    entryReconstruction F A g0
        (fun a ij => backgroundDifferenceEntry (A.cutoffs a) g0 background g ij.1 ij.2) ab =
      (fun x => (smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0) x
        (F ab.1 x) (F ab.2 x)) := by
  funext x
  let R := smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0
  change (∑ a : A.centers, ∑ ij : Fin n × Fin n,
    outputCoefficient (A.cutoffs a) g0 (A.partition a) (F ab.1) (F ab.2) ij.1 ij.2 x *
      backgroundDifferenceEntry (A.cutoffs a) g0 background g ij.1 ij.2 x) =
        R x (F ab.1 x) (F ab.2 x)
  calc
    _ = ∑ a : A.centers, A.partition a x * R x (F ab.1 x) (F ab.2 x) := by
      apply Finset.sum_congr rfl
      intro a _
      have heq := weighted_source_eq (A.cutoffs a) g0 (A.partition a)
        (subset_tsupport (A.partition a)) (F ab.1) (F ab.2) R
        (fun y i j => backgroundDifferenceEntry (A.cutoffs a) g0 background g i j y)
        (fun y hy i j => backgroundDifferenceEntry_eq_intrinsic (A.cutoffs a) g0
          background g D B B0 hy i j) x
      simpa only [Fintype.sum_prod_type] using heq.symm
    _ = _ := by rw [← Finset.sum_mul, A.weight_sum, one_mul]

theorem backgroundOutput_ae_eq {k : ℕ} (Q : ChartSourceTuples (iota := iota) A μ k)
    (background g : RiemannianMetric n M)
    (D : LeviCivitaData g) (B : LeviCivitaData background) (B0 : LeviCivitaData g0)
    (hQ : ∀ a ij word (hw : word.length ≤ k),
      Q a ij (wordIndex word hw) =ᵐ[μ] directionalWord F word
        (backgroundDifferenceEntry (A.cutoffs a) g0 background g ij.1 ij.2))
    (ab : iota × iota) (word : List iota) (hw : word.length ≤ k) :
    sourceOutputL2 F A g0 μ k Q ab (wordIndex word hw) =ᵐ[μ] directionalWord F word
      (fun x => (smoothRicciDeTurckTensor D B - smoothRicciDeTurckTensor D B0) x
        (F ab.1 x) (F ab.2 x)) := by
  have heq := sourceOutputL2_ae_reconstruction F A g0 μ Q
    (fun a ij => backgroundDifferenceEntry (A.cutoffs a) g0 background g ij.1 ij.2)
    (fun a ij => backgroundDifferenceEntry_contMDiff F (A.cutoffs a) g0 background g ij.1 ij.2)
    hQ ab word hw
  rw [backgroundDifferenceEntry_reconstruction F g0 A background g D B B0 ab] at heq
  exact heq

theorem exists_smooth_background_chart_action
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (k m : ℕ) (hkm : k + 2 ≤ 2 * m) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ Psi : (NativeProbeContinuous (M := M) (iota := iota) (k + 2) ×
          (NativeProbeContinuous (M := M) (iota := iota) m ×
            NativeProbeL2 (iota := iota) μ (k + 1))) → ChartSourceTuples (iota := iota) A μ k,
      ContDiff ℝ ∞ Psi ∧ (∀ QC HC, Psi (0, QC, HC) = 0) ∧
      ∀ QB : NativeProbeContinuous (M := M) (iota := iota) (k + 2), ‖QB‖ < delta →
        ∀ QC : NativeProbeContinuous (M := M) (iota := iota) m, ‖QC‖ < delta →
        ∀ HC : NativeProbeL2 (iota := iota) μ (k + 1), ∀ background g : RiemannianMetric n M,
        (∀ ab w (hw : w.length ≤ k + 2) x,
          QB ab (wordIndex w hw) x = directionalWord F w (probeDifference F background g0 ab) x) →
        (∀ ab w (hw : w.length ≤ m) x,
          QC ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x) →
        (∀ ab w (hw : w.length ≤ k + 1),
          HC ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) →
        ∀ a ij word (hw : word.length ≤ k),
          Psi (QB, QC, HC) a ij (wordIndex word hw) =ᵐ[μ]
            directionalWord F word (backgroundDifferenceEntry (A.cutoffs a) g0 background g ij.1 ij.2) := by
  classical
  have hdata (a : A.centers) (ij : Fin n × Fin n) (word : WordIndex iota k) :=
    exists_smooth_background_word_action F (A.cutoffs a) g0 μ hF k m hkm ij.1 ij.2
      (List.ofFn word.2) (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ word.1.isLt)
  choose delta hdelta Psi hPsi hPsi0 hPsiEq using hdata
  obtain ⟨r, hr, hrd⟩ := exists_common_positive_time
    (Finset.univ : Finset (A.centers × (Fin n × Fin n) × WordIndex iota k))
    (fun z => delta z.1 z.2.1 z.2.2) (fun z _ => hdelta z.1 z.2.1 z.2.2)
  refine ⟨r, hr, fun z a ij word => Psi a ij word z,
    contDiff_pi.mpr (fun a => contDiff_pi.mpr (fun ij => contDiff_pi.mpr (hPsi a ij))), ?_, ?_⟩
  · intro QC HC
    funext a ij word
    exact hPsi0 a ij word QC HC
  · intro QB hQBsmall QC hQCsmall HC background g hQB hQC hHC a ij word hw
    have hbound := hrd (a, ij, wordIndex word hw) (Finset.mem_univ _)
    have heq := hPsiEq a ij (wordIndex word hw) QB (hQBsmall.trans_le hbound)
      QC (hQCsmall.trans_le hbound) HC background g hQB hQC hHC
    simpa only [wordIndex_word] using heq

end FiniteCover

end PoincareConjecture.DeTurckBackgroundVariationNative

end
