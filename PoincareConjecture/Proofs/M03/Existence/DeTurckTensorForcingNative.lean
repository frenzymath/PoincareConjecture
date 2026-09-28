import PoincareConjecture.Proofs.M03.Existence.DeTurckSourceJetNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetAffineNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckMixedForcingNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckPrincipalForcingNative
import PoincareConjecture.Proofs.M03.Existence.FiniteChartCommonTimeNative








set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.DeTurckTensorForcingNative

open TensorProbeNative DeTurckNative DeTurckCompatibleJetNative
  DeTurckJetCoordinatesNative DeTurckJetAffineNative DeTurckSourceJetNative
  DeTurckRationalJetNative DeTurckInverseCompositionNative

variable {n : ℕ} {M iota : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [Fintype iota]
  (F : iota → SmoothField (n := n) (M := M))
  (A : CompatibleChartCover (n := n) (M := M)) (g0 : RiemannianMetric n M)

def nativeCoefficient (a i : iota) (_ : M) : ℝ := by
  classical
  exact if a = i then 1 else 0

theorem nativeCoefficient_contMDiff (a i : iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (nativeCoefficient (M := M) a i) := contMDiff_const

theorem nativeField_eq_sum (a : iota) (x : M) :
    F a x = ∑ i, nativeCoefficient a i x • F i x := by
  classical
  simp [nativeCoefficient]

def outputWordTerms (a : A.centers) (ab : iota × iota) (ij : Fin n × Fin n)
    (word : List iota) : List (DirectionalTerm (n := n) (M := M) (iota := iota)) :=
  weightedWordTerms F nativeCoefficient nativeCoefficient_contMDiff
    (outputCoefficient (A.cutoffs a) g0 (A.partition a) (F ab.1) (F ab.2) ij.1 ij.2)
    (outputCoefficient_contMDiff (A.cutoffs a) g0 (A.partition a).contMDiff
      (F ab.1) (F ab.2) ij.1 ij.2) word

theorem outputWordTerms_order (a : A.centers) (ab : iota × iota)
    (ij : Fin n × Fin n) (word : List iota) :
    ∀ t ∈ outputWordTerms F A g0 a ab ij word, t.word.length ≤ word.length :=
  weightedWordTerms_order F nativeCoefficient nativeCoefficient_contMDiff
    (outputCoefficient (A.cutoffs a) g0 (A.partition a) (F ab.1) (F ab.2) ij.1 ij.2)
    (outputCoefficient_contMDiff (A.cutoffs a) g0 (A.partition a).contMDiff
      (F ab.1) (F ab.2) ij.1 ij.2) word

theorem outputWordTerms_eq (a : A.centers) (ab : iota × iota)
    (ij : Fin n × Fin n) (word : List iota) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalTerms F (outputWordTerms F A g0 a ab ij word) f x =
      directionalWord F word (fun y =>
        outputCoefficient (A.cutoffs a) g0 (A.partition a) (F ab.1) (F ab.2) ij.1 ij.2 y *
          f y) x :=
  weightedWordTerms_eq F nativeCoefficient nativeCoefficient_contMDiff F
    (nativeField_eq_sum F)
    (outputCoefficient (A.cutoffs a) g0 (A.partition a) (F ab.1) (F ab.2) ij.1 ij.2)
    (outputCoefficient_contMDiff (A.cutoffs a) g0 (A.partition a).contMDiff
      (F ab.1) (F ab.2) ij.1 ij.2) word hf x

def sourceEntry (g : RiemannianMetric n M) (a : A.centers)
    (ij : Fin n × Fin n) (x : M) : ℝ :=
  ricciDeTurckSource ((A.cutoffs a).jet g0 x) ((A.cutoffs a).jet g x) ij.1 ij.2

include F in
theorem sourceEntry_contMDiff (g : RiemannianMetric n M) (a : A.centers)
    (ij : Fin n × Fin n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (sourceEntry A g0 g a ij) := by
  change ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x =>
    ricciDeTurckSource ((A.cutoffs a).jet g0 x) ((A.cutoffs a).jet g x) ij.1 ij.2)
  simpa only [eval_sourceExpr_compatible] using
    (sourceExpr Sum.inl false ij.1 ij.2).native_contMDiff
      (combinedFields F (A.cutoffs a)) (compatibleMatrix (A.cutoffs a) g0 g)
      (compatibleMatrix_contMDiff (A.cutoffs a) g0 g)
      (compatibleMatrix_det_ne_zero (A.cutoffs a) g0 g)

def entryReconstruction (f : A.centers → (Fin n × Fin n) → M → ℝ)
    (ab : iota × iota) (x : M) : ℝ :=
  ∑ a : A.centers, ∑ ij : Fin n × Fin n,
    outputCoefficient (A.cutoffs a) g0 (A.partition a) (F ab.1) (F ab.2) ij.1 ij.2 x *
      f a ij x

theorem entryReconstruction_word (f : A.centers → (Fin n × Fin n) → M → ℝ)
    (hf : ∀ a ij, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f a ij))
    (ab : iota × iota) (word : List iota) (x : M) :
    directionalWord F word (entryReconstruction F A g0 f ab) x =
      ∑ a : A.centers, ∑ ij : Fin n × Fin n,
        directionalTerms F (outputWordTerms F A g0 a ab ij word) (f a ij) x := by
  let q (a : A.centers) (ij : Fin n × Fin n) (y : M) :=
    outputCoefficient (A.cutoffs a) g0 (A.partition a) (F ab.1) (F ab.2) ij.1 ij.2 y *
      f a ij y
  have hq (a : A.centers) (ij : Fin n × Fin n) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (q a ij) :=
    (outputCoefficient_contMDiff (A.cutoffs a) g0 (A.partition a).contMDiff
      (F ab.1) (F ab.2) ij.1 ij.2).mul (hf a ij)
  have hsum (a : A.centers) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => ∑ ij : Fin n × Fin n, q a ij y) :=
    ContMDiff.sum (t := Finset.univ) (fun ij _ => hq a ij)
  change directionalWord F word (fun y => ∑ a : A.centers, ∑ ij, q a ij y) x = _
  rw [directionalWord_sum Finset.univ F word _ (fun a _ => hsum a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [directionalWord_sum Finset.univ F word _ (fun ij _ => hq a ij)]
  apply Finset.sum_congr rfl
  intro ij _
  exact (outputWordTerms_eq F A g0 a ab ij word (hf a ij) x).symm


theorem sourceWord_eq (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (B : LeviCivitaData g0) (ab : iota × iota) (word : List iota) (x : M) :
    directionalWord F word
      (fun y => smoothRicciDeTurckTensor D B y (F ab.1 y) (F ab.2 y)) x =
      ∑ a : A.centers, ∑ ij : Fin n × Fin n,
        directionalTerms F (outputWordTerms F A g0 a ab ij word) (sourceEntry A g0 g a ij) x := by
  have heq : (fun y => smoothRicciDeTurckTensor D B y (F ab.1 y) (F ab.2 y)) =
      entryReconstruction F A g0 (sourceEntry A g0 g) ab := by
    funext y
    simpa only [Fintype.sum_prod_type, entryReconstruction, sourceEntry] using
      A.source_eq g0 g D B (F ab.1) (F ab.2) y
  rw [heq]
  exact entryReconstruction_word F A g0 (sourceEntry A g0 g)
    (sourceEntry_contMDiff F A g0 g) ab word x

section CompletedOutput

variable [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [IsFiniteMeasure μ]

abbrev ChartSourceTuples (k : ℕ) :=
  A.centers → (Fin n × Fin n) → WordIndex iota k → Lp ℝ 2 μ


def sourceOutputWordL2 {k : ℕ} (ab : iota × iota) (word : List iota)
    (hw : word.length ≤ k) :
    ChartSourceTuples (iota := iota) A μ k →L[ℝ] Lp ℝ 2 μ := by
  classical
  let entry (a : A.centers) (ij : Fin n × Fin n) :
      ChartSourceTuples (iota := iota) A μ k →L[ℝ] (WordIndex iota k → Lp ℝ 2 μ) :=
    (ContinuousLinearMap.proj ij).comp
      (ContinuousLinearMap.proj a : ChartSourceTuples (iota := iota) A μ k →L[ℝ]
        ((Fin n × Fin n) → WordIndex iota k → Lp ℝ 2 μ))
  exact ∑ a : A.centers, ∑ ij : Fin n × Fin n,
    (termsL2 μ (outputWordTerms F A g0 a ab ij word)
      (fun t ht => (outputWordTerms_order F A g0 a ab ij word t ht).trans hw)).comp
        (entry a ij)

theorem sourceOutputWordL2_ae_sum {k : ℕ} (ab : iota × iota) (word : List iota)
    (hw : word.length ≤ k) (Q : ChartSourceTuples (iota := iota) A μ k)
    (f : A.centers → (Fin n × Fin n) → M → ℝ)
    (hQ : ∀ a ij w (hw : w.length ≤ k),
      Q a ij (wordIndex w hw) =ᵐ[μ] directionalWord F w (f a ij)) :
    sourceOutputWordL2 F A g0 μ ab word hw Q =ᵐ[μ] fun x =>
      ∑ a : A.centers, ∑ ij : Fin n × Fin n,
        directionalTerms F (outputWordTerms F A g0 a ab ij word) (f a ij) x := by
  classical
  let q (a : A.centers) (ij : Fin n × Fin n) : Lp ℝ 2 μ :=
    termsL2 μ (outputWordTerms F A g0 a ab ij word)
      (fun t ht => (outputWordTerms_order F A g0 a ab ij word t ht).trans hw) (Q a ij)
  have hq (a : A.centers) (ij : Fin n × Fin n) :
      q a ij =ᵐ[μ] directionalTerms F (outputWordTerms F A g0 a ab ij word)
        (f a ij) :=
    termsL2_ae_eq F μ (outputWordTerms F A g0 a ab ij word)
      (fun t ht => (outputWordTerms_order F A g0 a ab ij word t ht).trans hw)
      (Q a ij) (f a ij) (hQ a ij)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun a : A.centers => ∑ ij, q a ij),
    ae_all_iff.mpr (fun a : A.centers => Lp.coeFn_fun_finsetSum Finset.univ (q a)),
    ae_all_iff.mpr (fun a : A.centers => ae_all_iff.mpr (hq a))] with x houter hinner hterms
  simp only [sourceOutputWordL2, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change (∑ a : A.centers, ∑ ij : Fin n × Fin n, q a ij) x = _
  rw [houter]
  simp only [hinner, hterms]

theorem sourceOutputWordL2_ae_reconstruction {k : ℕ}
    (ab : iota × iota) (word : List iota) (hw : word.length ≤ k)
    (Q : ChartSourceTuples (iota := iota) A μ k)
    (f : A.centers → (Fin n × Fin n) → M → ℝ)
    (hf : ∀ a ij, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f a ij))
    (hQ : ∀ a ij w (hw : w.length ≤ k),
      Q a ij (wordIndex w hw) =ᵐ[μ] directionalWord F w (f a ij)) :
    sourceOutputWordL2 F A g0 μ ab word hw Q =ᵐ[μ]
      directionalWord F word (entryReconstruction F A g0 f ab) := by
  filter_upwards [sourceOutputWordL2_ae_sum F A g0 μ ab word hw Q f hQ] with x hx
  exact hx.trans (entryReconstruction_word F A g0 f hf ab word x).symm

theorem sourceOutputWordL2_ae_eq {k : ℕ} (ab : iota × iota) (word : List iota)
    (hw : word.length ≤ k) (Q : ChartSourceTuples (iota := iota) A μ k)
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (hQ : ∀ a ij w (hw : w.length ≤ k),
      Q a ij (wordIndex w hw) =ᵐ[μ] directionalWord F w (sourceEntry A g0 g a ij)) :
    sourceOutputWordL2 F A g0 μ ab word hw Q =ᵐ[μ]
      directionalWord F word
        (fun y => smoothRicciDeTurckTensor D B y (F ab.1 y) (F ab.2 y)) := by
  filter_upwards [sourceOutputWordL2_ae_sum F A g0 μ ab word hw Q
    (sourceEntry A g0 g) hQ] with x hx
  exact hx.trans (sourceWord_eq F A g0 g D B ab word x).symm


def sourceOutputL2 (k : ℕ) :
    ChartSourceTuples (iota := iota) A μ k →L[ℝ] NativeProbeL2 (iota := iota) μ k :=
  ContinuousLinearMap.pi (fun ab => ContinuousLinearMap.pi (fun w =>
    sourceOutputWordL2 F A g0 μ ab (List.ofFn w.2)
      (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt)))

theorem sourceOutputL2_apply {k : ℕ} (Q : ChartSourceTuples (iota := iota) A μ k)
    (ab : iota × iota) (word : List iota) (hw : word.length ≤ k) :
    sourceOutputL2 F A g0 μ k Q ab (wordIndex word hw) =
      sourceOutputWordL2 F A g0 μ ab word hw Q := by
  simp only [sourceOutputL2, ContinuousLinearMap.pi_apply, wordIndex_word]

theorem sourceOutputL2_ae_reconstruction {k : ℕ}
    (Q : ChartSourceTuples (iota := iota) A μ k)
    (f : A.centers → (Fin n × Fin n) → M → ℝ)
    (hf : ∀ a ij, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f a ij))
    (hQ : ∀ a ij w (hw : w.length ≤ k),
      Q a ij (wordIndex w hw) =ᵐ[μ] directionalWord F w (f a ij))
    (ab : iota × iota) (word : List iota) (hw : word.length ≤ k) :
    sourceOutputL2 F A g0 μ k Q ab (wordIndex word hw) =ᵐ[μ]
      directionalWord F word (entryReconstruction F A g0 f ab) := by
  rw [sourceOutputL2_apply]
  exact sourceOutputWordL2_ae_reconstruction F A g0 μ ab word hw Q f hf hQ

theorem sourceOutputL2_ae_eq {k : ℕ} (Q : ChartSourceTuples (iota := iota) A μ k)
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (B : LeviCivitaData g0)
    (hQ : ∀ a ij w (hw : w.length ≤ k),
      Q a ij (wordIndex w hw) =ᵐ[μ] directionalWord F w (sourceEntry A g0 g a ij))
    (ab : iota × iota) (word : List iota) (hw : word.length ≤ k) :
    sourceOutputL2 F A g0 μ k Q ab (wordIndex word hw) =ᵐ[μ]
      directionalWord F word
        (fun y => smoothRicciDeTurckTensor D B y (F ab.1 y) (F ab.2 y)) := by
  rw [sourceOutputL2_apply]
  exact sourceOutputWordL2_ae_eq F A g0 μ ab word hw Q g D B hQ

section PrincipalTop

open DeTurckMetricProducerNative
open scoped Matrix.Norms.Elementwise

variable [SecondCountableTopology M] {base : M} {K : Set M}
  (C : Cutoffs (n := n) base K)

def matrixEntryContinuous (i j : Fin n) :
    C(M, Matrix (Fin n) (Fin n) ℝ) →L[ℝ] C(M, ℝ) :=
  ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ))).compLeftContinuous
      ℝ M

@[simp] theorem matrixEntryContinuous_apply (i j : Fin n)
    (B : C(M, Matrix (Fin n) (Fin n) ℝ)) (x : M) :
    matrixEntryContinuous (M := M) i j B x = B x i j := rfl


def principalHighWordL2 {k : ℕ} (word : List iota) (hw : word.length ≤ k)
    (c d i j : Fin n) : NativeProbeL2 (iota := iota) μ (k + 2) →L[ℝ] Lp ℝ 2 μ :=
  matrixDifferenceWordL2 F C g0 μ
    (word.map Sum.inr ++ [Sum.inl c, Sum.inl d])
    (by simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil]
      using Nat.add_le_add_right hw 2) i j


def principalTopWordL2 {k : ℕ} (word : List iota) (hw : word.length ≤ k)
    (i j : Fin n) : C(M, Matrix (Fin n) (Fin n) ℝ) →L[ℝ]
      NativeProbeL2 (iota := iota) μ (k + 2) →L[ℝ] Lp ℝ 2 μ :=
  ∑ c : Fin n, ∑ d : Fin n,
    ((ContinuousLinearMap.compL ℝ (NativeProbeL2 (iota := iota) μ (k + 2))
      (Lp ℝ 2 μ) (Lp ℝ 2 μ)).flip
        (principalHighWordL2 F g0 μ C word hw c d i j)).comp
          ((spatialCoefficientAction μ (ContinuousLinearMap.mul ℝ ℝ)).comp
            (matrixEntryContinuous c d))

theorem principalTopWordL2_apply {k : ℕ} (word : List iota) (hw : word.length ≤ k)
    (i j : Fin n) (B : C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : NativeProbeL2 (iota := iota) μ (k + 2)) :
    principalTopWordL2 F g0 μ C word hw i j B Q =
      ∑ c : Fin n, ∑ d : Fin n,
        spatialCoefficientAction μ (ContinuousLinearMap.mul ℝ ℝ)
          (matrixEntryContinuous c d B) (principalHighWordL2 F g0 μ C word hw c d i j Q) := by
  simp only [principalTopWordL2, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply]

theorem principalTopWordL2_norm_le {k : ℕ} (word : List iota) (hw : word.length ≤ k)
    (i j : Fin n) (B : C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : NativeProbeL2 (iota := iota) μ (k + 2)) :
    ‖principalTopWordL2 F g0 μ C word hw i j B Q‖ ≤
      ‖principalTopWordL2 F g0 μ C word hw i j‖ * ‖B‖ * ‖Q‖ :=
  (principalTopWordL2 F g0 μ C word hw i j).le_opNorm₂ B Q

theorem principalTopWordL2_ae_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {k : ℕ} (word : List iota) (hw : word.length ≤ k) (i j : Fin n)
    (B : C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : NativeProbeL2 (iota := iota) μ (k + 2)) (g : RiemannianMetric n M)
    (hQ : ∀ ab w (hw : w.length ≤ k + 2),
      Q ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) :
    principalTopWordL2 F g0 μ C word hw i j B Q =ᵐ[μ] fun x =>
      ∑ c : Fin n, ∑ d : Fin n, B x c d *
        directionalWord (combinedFields F C)
          (word.map Sum.inr ++ [Sum.inl c, Sum.inl d])
          (fun y => C.matrix g y i j - C.matrix g0 y i j) x := by
  let q (c d : Fin n) : Lp ℝ 2 μ :=
    spatialCoefficientAction μ (ContinuousLinearMap.mul ℝ ℝ)
      (matrixEntryContinuous c d B) (principalHighWordL2 F g0 μ C word hw c d i j Q)
  have hq (c d : Fin n) : q c d =ᵐ[μ] fun x => B x c d *
      directionalWord (combinedFields F C)
        (word.map Sum.inr ++ [Sum.inl c, Sum.inl d])
        (fun y => C.matrix g y i j - C.matrix g0 y i j) x := by
    filter_upwards [spatialCoefficientAction_coe μ (ContinuousLinearMap.mul ℝ ℝ)
      (matrixEntryContinuous c d B) (principalHighWordL2 F g0 μ C word hw c d i j Q),
      matrixDifferenceWordL2_ae_eq F C g0 μ hF
        (word.map Sum.inr ++ [Sum.inl c, Sum.inl d])
        (by simpa only [List.length_append, List.length_map, List.length_cons, List.length_nil]
          using Nat.add_le_add_right hw 2) i j Q g g0 hQ] with x hmul hderiv
    change q c d x = B x c d * (principalHighWordL2 F g0 μ C word hw c d i j Q) x at hmul
    exact hmul.trans (congrArg (fun z : ℝ => B x c d * z) hderiv)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun c : Fin n => ∑ d, q c d),
    ae_all_iff.mpr (fun c : Fin n => Lp.coeFn_fun_finsetSum Finset.univ (q c)),
    ae_all_iff.mpr (fun c : Fin n => ae_all_iff.mpr (hq c))] with x houter hinner hterms
  rw [principalTopWordL2_apply]
  change (∑ c : Fin n, ∑ d : Fin n, q c d) x = _
  rw [houter]
  simp only [hinner, hterms]


def operatorPi {I : Type*} [Fintype I] {Z : Type*} {W : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W] :
    (I → Z →L[ℝ] W) →L[ℝ] (Z →L[ℝ] I → W) :=
  LinearMap.mkContinuous
    { toFun := ContinuousLinearMap.pi
      map_add' := by intros; ext z i; rfl
      map_smul' := by intros; ext z i; rfl }
    1 (fun f => by
      change ‖ContinuousLinearMap.pi f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact ContinuousLinearMap.norm_pi_le_of_le
        (fun i => norm_le_pi_norm f i) (norm_nonneg f))

@[simp] theorem operatorPi_apply {I : Type*} [Fintype I] {Z : Type*} {W : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : I → Z →L[ℝ] W) (z : Z) (i : I) :
    operatorPi (I := I) (Z := Z) (W := W) f z i = f i z := rfl

def principalChartTopL2 (k : ℕ) :
    (A.centers → C(M, Matrix (Fin n) (Fin n) ℝ)) →L[ℝ]
      NativeProbeL2 (iota := iota) μ (k + 2) →L[ℝ] ChartSourceTuples (iota := iota) A μ k := by
  let entry (a : A.centers) (ij : Fin n × Fin n) :
      (A.centers → C(M, Matrix (Fin n) (Fin n) ℝ)) →L[ℝ]
        NativeProbeL2 (iota := iota) μ (k + 2) →L[ℝ] (WordIndex iota k → Lp ℝ 2 μ) :=
    operatorPi.comp (ContinuousLinearMap.pi (fun w =>
      (principalTopWordL2 F g0 μ (A.cutoffs a) (List.ofFn w.2)
        (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt) ij.1 ij.2).comp
          (ContinuousLinearMap.proj a)))
  let patch (a : A.centers) :
      (A.centers → C(M, Matrix (Fin n) (Fin n) ℝ)) →L[ℝ]
        NativeProbeL2 (iota := iota) μ (k + 2) →L[ℝ]
          ((Fin n × Fin n) → WordIndex iota k → Lp ℝ 2 μ) :=
    operatorPi.comp (ContinuousLinearMap.pi (entry a))
  exact operatorPi.comp (ContinuousLinearMap.pi patch)

theorem principalChartTopL2_apply (k : ℕ)
    (B : A.centers → C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : NativeProbeL2 (iota := iota) μ (k + 2))
    (a : A.centers) (ij : Fin n × Fin n) (w : WordIndex iota k) :
    principalChartTopL2 F A g0 μ k B Q a ij w =
      principalTopWordL2 F g0 μ (A.cutoffs a) (List.ofFn w.2)
        (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ w.1.isLt) ij.1 ij.2 (B a) Q := rfl


def principalOutputL2 (k : ℕ) :
    (A.centers → C(M, Matrix (Fin n) (Fin n) ℝ)) →L[ℝ]
      NativeProbeL2 (iota := iota) μ (k + 2) →L[ℝ] NativeProbeL2 (iota := iota) μ k :=
  ((ContinuousLinearMap.compL ℝ (NativeProbeL2 (iota := iota) μ (k + 2))
    (ChartSourceTuples (iota := iota) A μ k) (NativeProbeL2 (iota := iota) μ k))
      (sourceOutputL2 F A g0 μ k)).comp (principalChartTopL2 F A g0 μ k)

theorem principalOutputL2_apply (k : ℕ)
    (B : A.centers → C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : NativeProbeL2 (iota := iota) μ (k + 2)) :
    principalOutputL2 F A g0 μ k B Q =
      sourceOutputL2 F A g0 μ k (principalChartTopL2 F A g0 μ k B Q) := rfl

@[simp] theorem principalOutputL2_zero (k : ℕ) :
    principalOutputL2 F A g0 μ k 0 = 0 := map_zero _

theorem principalOutputL2_norm_le (k : ℕ)
    (B : A.centers → C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : NativeProbeL2 (iota := iota) μ (k + 2)) :
    ‖principalOutputL2 F A g0 μ k B Q‖ ≤
      ‖principalOutputL2 F A g0 μ k‖ * ‖B‖ * ‖Q‖ :=
  (principalOutputL2 F A g0 μ k).le_opNorm₂ B Q

end PrincipalTop

section ActualCoefficientMaps

open DeTurckMetricProducerNative DeTurckPrincipalForcingNative
open scoped Matrix.Norms.Elementwise

variable [SecondCountableTopology M]
  (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
    (∑ a, g0.inner x (F a x) v • F a x) = v)

include hF in

theorem exists_smooth_cover_inverse_difference (m : ℕ) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ B : NativeProbeContinuous (M := M) (iota := iota) m →
          A.centers → C(M, Matrix (Fin n) (Fin n) ℝ),
      ContDiff ℝ ∞ B ∧ B 0 = 0 ∧
      ∀ Q : NativeProbeContinuous (M := M) (iota := iota) m, ‖Q‖ < delta →
        ∀ g : RiemannianMetric n M,
        (∀ ab w (hw : w.length ≤ m) x,
          Q ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x) →
        ∀ a x, B Q a x = ((A.cutoffs a).matrix g x)⁻¹ -
          ((A.cutoffs a).matrix g0 x)⁻¹ := by
  classical
  choose delta hdelta B hB hB0 hBeq using fun a : A.centers =>
    exists_smooth_native_inverse_difference F (A.cutoffs a) g0 hF m
  obtain ⟨r, hr, hrd⟩ := exists_common_positive_time Finset.univ delta
    (fun a _ => hdelta a)
  refine ⟨r, hr, fun Q a => B a Q, contDiff_pi.mpr hB, ?_, ?_⟩
  · funext a
    exact hB0 a
  · intro Q hQsmall g hQ a x
    exact hBeq a Q (hQsmall.trans_le (hrd a (Finset.mem_univ a))) g hQ x

include hF in

theorem exists_smooth_chart_trace_action (k m : ℕ) (hkm : k + 2 ≤ 2 * m) :
    ∃ delta : ℝ, 0 < delta ∧
      ∃ Phi : (NativeProbeContinuous (M := M) (iota := iota) m ×
          NativeProbeL2 (iota := iota) μ (k + 1)) →
          ChartSourceTuples (iota := iota) A μ k,
      ContDiff ℝ ∞ Phi ∧
      ∀ Q : NativeProbeContinuous (M := M) (iota := iota) m, ‖Q‖ < delta →
        ∀ H : NativeProbeL2 (iota := iota) μ (k + 1), ∀ g : RiemannianMetric n M,
        (∀ ab w (hw : w.length ≤ m) x,
          Q ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x) →
        (∀ ab w (hw : w.length ≤ k + 1),
          H ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) →
        ∀ a ij w (hw : w.length ≤ k),
          Phi (Q, H) a ij (wordIndex w hw) =ᵐ[μ] fun x =>
            (residualTraceExpr Sum.inl ij.1 ij.2 (w.map Sum.inr)).eval
              (nativeValues (combinedFields F (A.cutoffs a))
                (compatibleMatrix (A.cutoffs a) g0 g) x) := by
  classical
  have hdata (a : A.centers) (ij : Fin n × Fin n) (w : WordIndex iota k) :=
    exists_smooth_native_jet_action μ F (A.cutoffs a) g0 hF
      (residualTraceExpr Sum.inl ij.1 ij.2 ((List.ofFn w.2).map Sum.inr)) m (k + 1)
      (by
        have hd := degree_residualTraceExpr_le
          (iota := Fin n ⊕ iota) Sum.inl ij.1 ij.2 ((List.ofFn w.2).map Sum.inr)
        simp only [List.length_map, List.length_ofFn] at hd
        have hw := w.1.isLt
        omega)
      (by
        have hd := currentOrder_residualTraceExpr_le
          (iota := Fin n ⊕ iota) Sum.inl ij.1 ij.2 ((List.ofFn w.2).map Sum.inr)
        simp only [List.length_map, List.length_ofFn] at hd
        have hw := w.1.isLt
        omega)
  choose delta hdelta Phi hPhi hPhieq using hdata
  obtain ⟨r, hr, hrd⟩ := exists_common_positive_time
    (Finset.univ : Finset (A.centers × (Fin n × Fin n) × WordIndex iota k))
    (fun z => delta z.1 z.2.1 z.2.2) (fun z _ => hdelta z.1 z.2.1 z.2.2)
  refine ⟨r, hr, fun z a ij w => Phi a ij w z,
    contDiff_pi.mpr (fun a => contDiff_pi.mpr (fun ij => contDiff_pi.mpr (hPhi a ij))), ?_⟩
  intro Q hQsmall H g hQ hH a ij w hw
  have heq := hPhieq a ij (wordIndex w hw) Q
    (hQsmall.trans_le (hrd (a, ij, wordIndex w hw) (Finset.mem_univ _))) H g hQ hH
  simpa only [wordIndex_word] using heq

include hF in

theorem principalChartTopL2_add_trace_ae_eq {k : ℕ}
    (B : A.centers → C(M, Matrix (Fin n) (Fin n) ℝ))
    (H : NativeProbeL2 (iota := iota) μ (k + 2))
    (R : ChartSourceTuples (iota := iota) A μ k) (g : RiemannianMetric n M)
    (hB : ∀ a x, B a x = ((A.cutoffs a).matrix g x)⁻¹ -
      ((A.cutoffs a).matrix g0 x)⁻¹)
    (hH : ∀ ab w (hw : w.length ≤ k + 2),
      H ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab))
    (hR : ∀ a ij w (hw : w.length ≤ k),
      R a ij (wordIndex w hw) =ᵐ[μ] fun x =>
        (residualTraceExpr Sum.inl ij.1 ij.2 (w.map Sum.inr)).eval
          (nativeValues (combinedFields F (A.cutoffs a))
            (compatibleMatrix (A.cutoffs a) g0 g) x))
    (a : A.centers) (ij : Fin n × Fin n) (word : List iota) (hw : word.length ≤ k) :
    (principalChartTopL2 F A g0 μ k B H + R) a ij (wordIndex word hw) =ᵐ[μ]
      directionalWord F word (fun x => (A.cutoffs a).residual g0 g x ij.1 ij.2) := by
  simp only [Pi.add_apply, principalChartTopL2_apply, wordIndex_word]
  filter_upwards [Lp.coeFn_add
      (principalTopWordL2 F g0 μ (A.cutoffs a) word hw ij.1 ij.2 (B a) H)
      (R a ij (wordIndex word hw)),
    principalTopWordL2_ae_eq F g0 μ (A.cutoffs a) hF word hw ij.1 ij.2 (B a) H g hH,
    hR a ij word hw] with x hadd htop htrace
  rw [hadd, Pi.add_apply, htop, htrace,
    residual_top_trace_compatible F (A.cutoffs a) g0 g]
  congr 1
  simpa only [compatibleMatrix, hB, Matrix.sub_apply] using
    (eval_principalTopExpr (combinedFields F (A.cutoffs a))
      (compatibleMatrix (A.cutoffs a) g0 g)
      (compatibleMatrix_contMDiff (A.cutoffs a) g0 g)
      (compatibleMatrix_det_ne_zero (A.cutoffs a) g0 g)
      Sum.inl ij.1 ij.2 (word.map Sum.inr) x).symm

end ActualCoefficientMaps

end CompletedOutput

end PoincareConjecture.DeTurckTensorForcingNative

end
