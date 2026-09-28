import PoincareConjecture.Proofs.M03.Existence.DeTurckRationalJetNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetCoordinatesNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckSourceJetNative
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped ContDiff

namespace PoincareConjecture.DeTurckJetAffineNative

open DeTurckRationalJetNative

universe u v w

variable {iota : Type u} {n : ℕ}

def constantPart (m : ℕ) (low : Atom iota n → ℝ) : Expr iota n → ℝ
  | .constant c => c
  | .atom a => if a.weight ≤ m then low a else 0
  | .add p q => constantPart m low p + constantPart m low q
  | .mul p q => constantPart m low p * constantPart m low q
  | .neg p => -constantPart m low p

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

def linearPart (m : ℕ) (low : Atom iota n → ℝ)
    (high : Atom iota n → E →L[ℝ] ℝ) : Expr iota n → E →L[ℝ] ℝ
  | .constant _ => 0
  | .atom a => if a.weight ≤ m then 0 else high a
  | .add p q => linearPart m low high p + linearPart m low high q
  | .mul p q => constantPart m low p • linearPart m low high q +
      constantPart m low q • linearPart m low high p
  | .neg p => -linearPart m low high p

theorem linearPart_eq_zero (m : ℕ) (low : Atom iota n → ℝ)
    (high : Atom iota n → E →L[ℝ] ℝ) (p : Expr iota n) :
    p.degree ≤ m → linearPart m low high p = 0 := by
  induction p with
  | constant c => intro _; rfl
  | atom a =>
    intro ha
    exact if_pos ha
  | add p q hp hq =>
    intro h
    change max p.degree q.degree ≤ m at h
    simp only [linearPart, hp (le_trans (le_max_left _ _) h),
      hq (le_trans (le_max_right _ _) h), add_zero]
  | mul p q hp hq =>
    intro h
    change p.degree + q.degree ≤ m at h
    have hp0 := hp (show p.degree ≤ m by omega)
    have hq0 := hq (show q.degree ≤ m by omega)
    simp only [linearPart, hp0, hq0, smul_zero, add_zero]
  | neg p hp =>
    intro h
    simp only [linearPart, hp h, neg_zero]

theorem linearPart_mul_eq_zero (m : ℕ) (low : Atom iota n → ℝ)
    (high : Atom iota n → E →L[ℝ] ℝ) (p q : Expr iota n)
    (h : p.degree + q.degree ≤ 2 * m) (z : E) :
    linearPart m low high p z * linearPart m low high q z = 0 := by
  by_cases hp : p.degree ≤ m
  · rw [linearPart_eq_zero m low high p hp, ContinuousLinearMap.zero_apply, zero_mul]
  · have hq : q.degree ≤ m := by omega
    rw [linearPart_eq_zero m low high q hq, ContinuousLinearMap.zero_apply, mul_zero]

theorem eval_eq_constantPart_add_linearPart (m : ℕ) (low : Atom iota n → ℝ)
    (high : Atom iota n → E →L[ℝ] ℝ) (z : E) (p : Expr iota n) :
    p.degree ≤ 2 * m →
      p.eval (fun a => if a.weight ≤ m then low a else high a z) =
        constantPart m low p + linearPart m low high p z := by
  induction p with
  | constant c =>
    intro _
    simp only [Expr.eval, constantPart, linearPart, ContinuousLinearMap.zero_apply,
      add_zero]
  | atom a =>
    intro _
    by_cases ha : a.weight ≤ m <;>
      simp only [Expr.eval, constantPart, linearPart, ha, if_true, if_false,
        ContinuousLinearMap.zero_apply, add_zero, zero_add]
  | add p q hp hq =>
    intro h
    change max p.degree q.degree ≤ 2 * m at h
    rw [Expr.eval, hp (le_trans (le_max_left _ _) h),
      hq (le_trans (le_max_right _ _) h)]
    simp only [constantPart, linearPart, ContinuousLinearMap.add_apply]
    ring
  | mul p q hp hq =>
    intro h
    change p.degree + q.degree ≤ 2 * m at h
    have hp' := hp (show p.degree ≤ 2 * m by omega)
    have hq' := hq (show q.degree ≤ 2 * m by omega)
    have hzero := linearPart_mul_eq_zero m low high p q h z
    rw [Expr.eval, hp', hq']
    simp only [constantPart, linearPart, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    nlinarith only [hzero]
  | neg p hp =>
    intro h
    rw [Expr.eval, hp h]
    simp only [constantPart, linearPart, ContinuousLinearMap.neg_apply]
    ring

theorem contDiff_constantPart {P : Type w} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (m : ℕ) (low : Atom iota n → P → ℝ)
    (hlow : ∀ a, a.weight ≤ m → ContDiff ℝ ∞ (low a)) (p : Expr iota n) :
    ContDiff ℝ ∞ (fun x => constantPart m (fun a => low a x) p) := by
  induction p with
  | constant c => exact contDiff_const
  | atom a =>
    by_cases ha : a.weight ≤ m
    · simpa only [constantPart, if_pos ha] using hlow a ha
    · simpa only [constantPart, if_neg ha] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : P => (0 : ℝ)))
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq
  | neg p hp => exact hp.neg

theorem contDiff_linearPart {P : Type w} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (m : ℕ) (low : Atom iota n → P → ℝ)
    (hlow : ∀ a, a.weight ≤ m → ContDiff ℝ ∞ (low a))
    (high : Atom iota n → E →L[ℝ] ℝ) (p : Expr iota n) :
    ContDiff ℝ ∞ (fun x => linearPart m (fun a => low a x) high p) := by
  induction p with
  | constant c => exact contDiff_const
  | atom a =>
    by_cases ha : a.weight ≤ m
    · simpa only [linearPart, if_pos ha] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : P => (0 : E →L[ℝ] ℝ)))
    · simpa only [linearPart, if_neg ha] using
        (contDiff_const : ContDiff ℝ ∞ (fun _ : P => high a))
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq =>
    exact ((contDiff_constantPart m low hlow p).smul hq).add
      ((contDiff_constantPart m low hlow q).smul hp)
  | neg p hp => exact hp.neg

theorem contDiff_affineEvaluation {P : Type w} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (m : ℕ) (low : Atom iota n → P → ℝ)
    (hlow : ∀ a, a.weight ≤ m → ContDiff ℝ ∞ (low a))
    (high : Atom iota n → E →L[ℝ] ℝ) (p : Expr iota n) :
    ContDiff ℝ ∞ (fun z : P × E => constantPart m (fun a => low a z.1) p +
      linearPart m (fun a => low a z.1) high p z.2) := by
  exact ((contDiff_constantPart m low hlow p).comp contDiff_fst).add
    (((contDiff_linearPart m low hlow high p).comp contDiff_fst).clm_apply contDiff_snd)

theorem orderedDerivative_eval_eq_constantPart_add_linearPart
    (r : ℕ) (low : Atom iota n → ℝ) (high : Atom iota n → E →L[ℝ] ℝ)
    (z : E) (p : Expr iota n) (hp : p.degree ≤ 2) (word : List iota)
    (hword : word.length ≤ 2 * r) :
    (p.orderedDerivative word).eval
        (fun a => if a.weight ≤ r + 1 then low a else high a z) =
      constantPart (r + 1) low (p.orderedDerivative word) +
        linearPart (r + 1) low high (p.orderedDerivative word) z := by
  apply eval_eq_constantPart_add_linearPart
  have hdegree := p.degree_orderedDerivative_le word
  omega

abbrev LowAtom (p : Expr iota n) (m : ℕ) :=
  {a : p.atoms // a.val.weight ≤ m}

abbrev HighAtom (p : Expr iota n) (m : ℕ) :=
  {a : p.atoms // ¬a.val.weight ≤ m}

def lowProjection (p : Expr iota n) (m : ℕ) (a : Atom iota n) :
    (LowAtom p m → ℝ) →L[ℝ] ℝ := by
  classical
  exact if ha : a ∈ p.atoms then
    if hw : a.weight ≤ m then ContinuousLinearMap.proj ⟨⟨a, ha⟩, hw⟩ else 0
    else 0

def highProjection (p : Expr iota n) (m : ℕ) (a : Atom iota n) :
    (HighAtom p m → ℝ) →L[ℝ] ℝ := by
  classical
  exact if ha : a ∈ p.atoms then
    if hw : a.weight ≤ m then 0 else ContinuousLinearMap.proj ⟨⟨a, ha⟩, hw⟩
    else 0

theorem highAtom_is_metric (p : Expr iota n) (m : ℕ) (a : HighAtom p m) :
    ∃ (b : Bool) (word : List iota) (i j : Fin n),
      a.val.val = Atom.metric b word i j ∧ m < word.length ∧
        word.length ≤ p.metricOrder b := by
  cases h : a.val.val with
  | metric b word i j =>
    refine ⟨b, word, i, j, rfl, ?_, ?_⟩
    · simpa only [h, Atom.weight] using Nat.lt_of_not_ge a.property
    · apply p.word_length_le_metricOrder_of_mem
      rw [← h]
      exact a.val.property
  | inverse b i j =>
    have hh := a.property
    simp only [h, Atom.weight, Nat.zero_le, not_true_eq_false] at hh

def finiteConstantPart (p : Expr iota n) (m : ℕ) (low : LowAtom p m → ℝ) : ℝ :=
  constantPart m (fun a => lowProjection p m a low) p

def finiteLinearPart (p : Expr iota n) (m : ℕ) (low : LowAtom p m → ℝ) :
    (HighAtom p m → ℝ) →L[ℝ] ℝ :=
  linearPart m (fun a => lowProjection p m a low) (highProjection p m) p

theorem contDiff_finiteConstantPart (p : Expr iota n) (m : ℕ) :
    ContDiff ℝ ∞ (finiteConstantPart p m) :=
  contDiff_constantPart m (fun a x => lowProjection p m a x)
    (fun a _ => (lowProjection p m a).contDiff) p

theorem contDiff_finiteLinearPart (p : Expr iota n) (m : ℕ) :
    ContDiff ℝ ∞ (finiteLinearPart p m) :=
  contDiff_linearPart m (fun a x => lowProjection p m a x)
    (fun a _ => (lowProjection p m a).contDiff) (highProjection p m) p

theorem contDiff_finiteAffineEvaluation (p : Expr iota n) (m : ℕ) :
    ContDiff ℝ ∞ (fun z : (LowAtom p m → ℝ) × (HighAtom p m → ℝ) =>
      finiteConstantPart p m z.1 + finiteLinearPart p m z.1 z.2) :=
  ((contDiff_finiteConstantPart p m).comp contDiff_fst).add
    (((contDiff_finiteLinearPart p m).comp contDiff_fst).clm_apply contDiff_snd)

theorem eval_eq_finiteParts (p : Expr iota n) (m : ℕ) (hp : p.degree ≤ 2 * m)
    (values : Atom iota n → ℝ) :
    p.eval values = finiteConstantPart p m (fun a => values a.val.val) +
      finiteLinearPart p m (fun a => values a.val.val) (fun a => values a.val.val) := by
  classical
  let low : LowAtom p m → ℝ := fun a => values a.val.val
  let high : HighAtom p m → ℝ := fun a => values a.val.val
  change p.eval values = finiteConstantPart p m low + finiteLinearPart p m low high
  calc
    p.eval values = p.eval (fun a => if a.weight ≤ m then lowProjection p m a low
        else highProjection p m a high) := by
      apply p.eval_congr_atoms
      intro a ha
      by_cases hw : a.weight ≤ m <;>
        simp [lowProjection, highProjection, ha, hw, low, high]
    _ = _ := eval_eq_constantPart_add_linearPart m
      (fun a => lowProjection p m a low) (highProjection p m) high p hp

theorem orderedDerivative_eval_eq_finiteParts (r : ℕ) (p : Expr iota n)
    (hp : p.degree ≤ 2) (word : List iota) (hword : word.length ≤ 2 * r)
    (values : Atom iota n → ℝ) :
    (p.orderedDerivative word).eval values =
      finiteConstantPart (p.orderedDerivative word) (r + 1)
        (fun a => values a.val.val) +
      finiteLinearPart (p.orderedDerivative word) (r + 1)
        (fun a => values a.val.val) (fun a => values a.val.val) := by
  apply eval_eq_finiteParts
  have hdegree := Expr.degree_orderedDerivative_le word p
  omega

section NativeProbeWords

set_option backward.isDefEq.respectTransparency false

open TensorProbeNative DeTurckCompatibleJetNative DeTurckJetCoordinatesNative
open DeTurckInverseCompositionNative MeasureTheory Set Filter
open scoped Manifold Bundle BigOperators

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [Fintype iota] {jota : Type*}

section WeightedWords

variable (F : iota → SmoothField (n := n) (M := M))
  (coefficient : jota → iota → M → ℝ)
  (hcoefficient : ∀ a i, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (coefficient a i))

def weightedWordTerms (c : M → ℝ) (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c) :
    List jota → List (DirectionalTerm (n := n) (M := M) (iota := iota))
  | [] => [⟨c, hc, []⟩]
  | a :: word => expandedDerivative F coefficient hcoefficient a
      (weightedWordTerms c hc word)

theorem weightedWordTerms_order (c : M → ℝ)
    (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c) (word : List jota) :
    ∀ t ∈ weightedWordTerms F coefficient hcoefficient c hc word,
      t.word.length ≤ word.length := by
  induction word with
  | nil =>
    intro t ht
    have ht' : t = ⟨c, hc, []⟩ := List.mem_singleton.mp ht
    subst t
    exact le_rfl
  | cons a word ih => exact expandedDerivative_order F coefficient hcoefficient a _ ih

theorem weightedWordTerms_eq
    (V : jota → SmoothField (n := n) (M := M))
    (hV : ∀ a x, V a x = ∑ i, coefficient a i x • F i x)
    (c : M → ℝ) (hc : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ c)
    (word : List jota) {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalTerms F (weightedWordTerms F coefficient hcoefficient c hc word) f x =
      directionalWord V word (fun y => c y * f y) x := by
  induction word generalizing x with
  | nil => simp [weightedWordTerms, directionalTerms]
  | cons a word ih =>
    rw [weightedWordTerms, expandedDerivative_eq F coefficient hcoefficient V hV _ _ hf]
    exact congrArg (fun h : M → ℝ => scalarDirectional (V a) h x) (funext ih)

end WeightedWords

variable [T2Space M] [CompactSpace M]
  (F : iota → SmoothField (n := n) (M := M))
  {base : M} {K : Set M} (C : Cutoffs (n := n) base K) (g0 : RiemannianMetric n M)

def probeDifference (g h : RiemannianMetric n M) (ab : iota × iota) (x : M) : ℝ :=
  g.inner x (F ab.1 x) (F ab.2 x) - h.inner x (F ab.1 x) (F ab.2 x)

theorem probeDifference_contMDiff (g h : RiemannianMetric n M) (ab : iota × iota) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (probeDifference F g h ab) :=
  (contMDiff_pairing (metricTensor g) (F ab.1) (F ab.2)).sub
    (contMDiff_pairing (metricTensor h) (F ab.1) (F ab.2))

def probeWordTerms (i j : Fin n) (ab : iota × iota) (word : List (Fin n ⊕ iota)) :
    List (DirectionalTerm (n := n) (M := M) (iota := iota)) :=
  weightedWordTerms F (combinedCoefficient F C g0) (combinedCoefficient_contMDiff F C g0)
    (C.probeCoefficient g0 F i j ab.1 ab.2)
    (C.probeCoefficient_contMDiff g0 F i j ab.1 ab.2) word

theorem probeWordTerms_order (i j : Fin n) (ab : iota × iota)
    (word : List (Fin n ⊕ iota)) :
    ∀ t ∈ probeWordTerms F C g0 i j ab word, t.word.length ≤ word.length :=
  weightedWordTerms_order F (combinedCoefficient F C g0)
    (combinedCoefficient_contMDiff F C g0) (C.probeCoefficient g0 F i j ab.1 ab.2)
    (C.probeCoefficient_contMDiff g0 F i j ab.1 ab.2) word

theorem probeWordTerms_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (i j : Fin n) (ab : iota × iota) (word : List (Fin n ⊕ iota))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    directionalTerms F (probeWordTerms F C g0 i j ab word) f x =
      directionalWord (combinedFields F C) word
        (fun y => C.probeCoefficient g0 F i j ab.1 ab.2 y * f y) x :=
  weightedWordTerms_eq F (combinedCoefficient F C g0)
    (combinedCoefficient_contMDiff F C g0) (combinedFields F C)
    (combinedFields_eq_sum F C g0 hF) (C.probeCoefficient g0 F i j ab.1 ab.2)
    (C.probeCoefficient_contMDiff g0 F i j ab.1 ab.2) word hf x

theorem matrixDifferenceWord_eq_sum
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (g h : RiemannianMetric n M) (word : List (Fin n ⊕ iota))
    (i j : Fin n) (x : M) :
    directionalWord (combinedFields F C) word
        (fun y => C.matrix g y i j - C.matrix h y i j) x =
      ∑ ab : iota × iota, directionalTerms F (probeWordTerms F C g0 i j ab word)
        (probeDifference F g h ab) x := by
  have heq : (fun y => C.matrix g y i j - C.matrix h y i j) =
      fun y => ∑ ab : iota × iota, C.probeCoefficient g0 F i j ab.1 ab.2 y *
        probeDifference F g h ab y := by
    funext y
    simpa only [Fintype.sum_prod_type, probeDifference] using
      C.matrix_sub_eq_sum_probes g0 g h F hF y i j
  have hs (ab : iota × iota) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => C.probeCoefficient g0 F i j ab.1 ab.2 y * probeDifference F g h ab y) :=
    (C.probeCoefficient_contMDiff g0 F i j ab.1 ab.2).mul
      (probeDifference_contMDiff F g h ab)
  rw [heq, directionalWord_sum Finset.univ (combinedFields F C) word _ (fun ab _ => hs ab)]
  apply Finset.sum_congr rfl
  intro ab _
  exact (probeWordTerms_eq F C g0 hF i j ab word
    (probeDifference_contMDiff F g h ab) x).symm

abbrev NativeProbeContinuous (k : ℕ) :=
  (iota × iota) → WordIndex iota k → C(M, ℝ)

def matrixDifferenceWordContinuous {k : ℕ} (word : List (Fin n ⊕ iota))
    (hw : word.length ≤ k) (i j : Fin n) :
    NativeProbeContinuous (M := M) (iota := iota) k →L[ℝ] C(M, ℝ) :=
  ∑ ab : iota × iota,
    (termsContinuous (probeWordTerms F C g0 i j ab word)
      (fun t ht => (probeWordTerms_order F C g0 i j ab word t ht).trans hw)).comp
        (ContinuousLinearMap.proj ab)

theorem matrixDifferenceWordContinuous_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {k : ℕ} (word : List (Fin n ⊕ iota)) (hw : word.length ≤ k) (i j : Fin n)
    (Q : NativeProbeContinuous (M := M) (iota := iota) k)
    (g h : RiemannianMetric n M)
    (hQ : ∀ ab w (hword : w.length ≤ k) x,
      Q ab (wordIndex w hword) x = directionalWord F w (probeDifference F g h ab) x)
    (x : M) :
    matrixDifferenceWordContinuous F C g0 word hw i j Q x =
      directionalWord (combinedFields F C) word
        (fun y => C.matrix g y i j - C.matrix h y i j) x := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  rw [matrixDifferenceWord_eq_sum F C g0 hF g h word i j x]
  simp only [matrixDifferenceWordContinuous, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, ContinuousMap.sum_apply]
  apply Finset.sum_congr rfl
  intro ab _
  exact termsContinuous_eq F (probeWordTerms F C g0 i j ab word)
    (fun t ht => (probeWordTerms_order F C g0 i j ab word t ht).trans hw)
    (Q ab) (probeDifference F g h ab) (hQ ab) x

def backgroundWordContinuous (word : List (Fin n ⊕ iota)) (i j : Fin n) : C(M, ℝ) :=
  ⟨directionalWord (combinedFields F C) word (fun y => C.matrix g0 y i j),
    (directionalWord_contMDiff (combinedFields F C) word
      (C.matrix_entry_contMDiff g0 i j)).continuous⟩

def matrixWordContinuous {k : ℕ} (word : List (Fin n ⊕ iota))
    (hw : word.length ≤ k) (i j : Fin n)
    (Q : NativeProbeContinuous (M := M) (iota := iota) k) : C(M, ℝ) :=
  backgroundWordContinuous F C g0 word i j +
    matrixDifferenceWordContinuous F C g0 word hw i j Q

theorem contDiff_matrixWordContinuous {k : ℕ} (word : List (Fin n ⊕ iota))
    (hw : word.length ≤ k) (i j : Fin n) :
    ContDiff ℝ ∞ (matrixWordContinuous F C g0 word hw i j) :=
  contDiff_const.add (matrixDifferenceWordContinuous F C g0 word hw i j).contDiff

theorem matrixWordContinuous_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {k : ℕ} (word : List (Fin n ⊕ iota)) (hw : word.length ≤ k) (i j : Fin n)
    (Q : NativeProbeContinuous (M := M) (iota := iota) k) (g : RiemannianMetric n M)
    (hQ : ∀ ab w (hword : w.length ≤ k) x,
      Q ab (wordIndex w hword) x = directionalWord F w (probeDifference F g g0 ab) x)
    (x : M) :
    matrixWordContinuous F C g0 word hw i j Q x =
      directionalWord (combinedFields F C) word (fun y => C.matrix g y i j) x := by
  simp only [matrixWordContinuous, ContinuousMap.add_apply]
  rw [matrixDifferenceWordContinuous_eq F C g0 hF word hw i j Q g g0 hQ]
  rw [congrFun (C.directionalWord_matrix_sub g g0 (combinedFields F C) word i j) x]
  change directionalWord (combinedFields F C) word (fun y => C.matrix g0 y i j) x +
    (directionalWord (combinedFields F C) word (fun y => C.matrix g y i j) x -
      directionalWord (combinedFields F C) word (fun y => C.matrix g0 y i j) x) = _
  ring

variable {A : Type*} [Fintype A]

def matrixTupleContinuous {k : ℕ} (label : A → Bool)
    (word : A → List (Fin n ⊕ iota)) (entry : A → Fin n × Fin n)
    (hword : ∀ a, label a = false → (word a).length ≤ k)
    (Q : NativeProbeContinuous (M := M) (iota := iota) k) : C(M, A → ℝ) :=
  packContinuous (fun a => if ha : label a = false then
    matrixWordContinuous F C g0 (word a) (hword a ha) (entry a).1 (entry a).2 Q
    else backgroundWordContinuous F C g0 (word a) (entry a).1 (entry a).2)

theorem contDiff_matrixTupleContinuous {k : ℕ} (label : A → Bool)
    (word : A → List (Fin n ⊕ iota)) (entry : A → Fin n × Fin n)
    (hword : ∀ a, label a = false → (word a).length ≤ k) :
    ContDiff ℝ ∞ (matrixTupleContinuous F C g0 label word entry hword) := by
  apply (packContinuous (M := M) (A := A)).contDiff.comp
  apply contDiff_pi.mpr
  intro a
  by_cases ha : label a = false
  · simpa only [dif_pos ha] using
      contDiff_matrixWordContinuous F C g0 (word a) (hword a ha) (entry a).1 (entry a).2
  · simp only [dif_neg ha]
    exact contDiff_const

theorem matrixTupleContinuous_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {k : ℕ} (label : A → Bool) (word : A → List (Fin n ⊕ iota))
    (entry : A → Fin n × Fin n) (hword : ∀ a, label a = false → (word a).length ≤ k)
    (Q : NativeProbeContinuous (M := M) (iota := iota) k) (g : RiemannianMetric n M)
    (hQ : ∀ ab w (hw : w.length ≤ k) x,
      Q ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x)
    (x : M) (a : A) :
    matrixTupleContinuous F C g0 label word entry hword Q x a =
      if label a = false then directionalWord (combinedFields F C) (word a)
        (fun y => C.matrix g y (entry a).1 (entry a).2) x
      else directionalWord (combinedFields F C) (word a)
        (fun y => C.matrix g0 y (entry a).1 (entry a).2) x := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  rw [matrixTupleContinuous, packContinuous_apply]
  by_cases ha : label a = false
  · simp only [dif_pos ha, if_pos ha]
    exact matrixWordContinuous_eq F C g0 hF (word a) (hword a ha)
      (entry a).1 (entry a).2 Q g hQ x
  · simp only [dif_neg ha, if_neg ha]
    rfl

open scoped Matrix.Norms.Elementwise

private def matrixUnflatten : ((Fin n × Fin n) → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.pi (fun j =>
    ContinuousLinearMap.proj (i, j)))

def matrixDifferenceValueContinuous {k : ℕ} :
    NativeProbeContinuous (M := M) (iota := iota) k →L[ℝ]
      C(M, Matrix (Fin n) (Fin n) ℝ) :=
  ((matrixUnflatten (n := n)).compLeftContinuous ℝ M).comp
    (packContinuous.comp (ContinuousLinearMap.pi (fun ij : Fin n × Fin n =>
      matrixDifferenceWordContinuous F C g0 [] (Nat.zero_le k) ij.1 ij.2)))

theorem matrixDifferenceValueContinuous_apply {k : ℕ}
    (Q : NativeProbeContinuous (M := M) (iota := iota) k) (x : M) (i j : Fin n) :
    matrixDifferenceValueContinuous F C g0 Q x i j =
      matrixDifferenceWordContinuous F C g0 [] (Nat.zero_le k) i j Q x := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  change packContinuous (fun ij : Fin n × Fin n =>
      matrixDifferenceWordContinuous F C g0 [] (Nat.zero_le k) ij.1 ij.2 Q) x (i, j) = _
  exact packContinuous_apply _ x (i, j)

def backgroundMatrixContinuous : C(M, Matrix (Fin n) (Fin n) ℝ) :=
  ⟨C.matrix g0, (C.matrix_contMDiff g0).continuous⟩

def matrixValueContinuous {k : ℕ}
    (Q : NativeProbeContinuous (M := M) (iota := iota) k) :
    C(M, Matrix (Fin n) (Fin n) ℝ) :=
  backgroundMatrixContinuous C g0 + matrixDifferenceValueContinuous F C g0 Q

theorem contDiff_matrixValueContinuous {k : ℕ} :
    ContDiff ℝ ∞ (matrixValueContinuous (k := k) F C g0) := by
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ :
    NativeProbeContinuous (M := M) (iota := iota) k => backgroundMatrixContinuous C g0)).add
      (matrixDifferenceValueContinuous (k := k) F C g0).contDiff

theorem matrixValueContinuous_sub {k : ℕ}
    (Q : NativeProbeContinuous (M := M) (iota := iota) k) :
    matrixValueContinuous F C g0 Q - backgroundMatrixContinuous C g0 =
      matrixDifferenceValueContinuous F C g0 Q := by
  simp only [matrixValueContinuous, add_sub_cancel_left]

theorem matrixValueContinuous_apply {k : ℕ}
    (Q : NativeProbeContinuous (M := M) (iota := iota) k) (x : M) (i j : Fin n) :
    matrixValueContinuous F C g0 Q x i j =
      matrixWordContinuous F C g0 [] (Nat.zero_le k) i j Q x := by
  change C.matrix g0 x i j + matrixDifferenceValueContinuous F C g0 Q x i j = _
  rw [matrixDifferenceValueContinuous_apply]
  rfl

theorem matrixValueContinuous_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {k : ℕ} (Q : NativeProbeContinuous (M := M) (iota := iota) k)
    (g : RiemannianMetric n M)
    (hQ : ∀ ab w (hw : w.length ≤ k) x,
      Q ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x)
    (x : M) : matrixValueContinuous F C g0 Q x = C.matrix g x := by
  ext i j
  rw [matrixValueContinuous_apply]
  exact matrixWordContinuous_eq F C g0 hF [] (Nat.zero_le k) i j Q g hQ x

private def matrixEntry (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ))

def backgroundInverseContinuous (i j : Fin n) : C(M, ℝ) :=
  ⟨fun x => (C.matrix g0 x)⁻¹ i j,
    (inverse_entry_contMDiff (C.matrix g0) (C.matrix_contMDiff g0)
      (fun x => ((C.matrix g0 x).isUnit_iff_isUnit_det.mp
        (C.matrix_posDef g0 x).isUnit).ne_zero) i j).continuous⟩

def inverseEntryContinuous
    (Inv : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    {k : ℕ} (i j : Fin n) (Q : NativeProbeContinuous (M := M) (iota := iota) k) : C(M, ℝ) :=
  (matrixEntry i j).compLeftContinuous ℝ M (Inv (matrixValueContinuous F C g0 Q))

theorem contDiff_inverseEntryContinuous
    (Inv : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    (hInv : ContDiff ℝ ∞ Inv) {k : ℕ} (i j : Fin n) :
    ContDiff ℝ ∞ (inverseEntryContinuous (k := k) F C g0 Inv i j) :=
  ((matrixEntry i j).compLeftContinuous ℝ M).contDiff.comp
    (hInv.comp (contDiff_matrixValueContinuous F C g0))

def lowAtomContinuous (p : Expr (Fin n ⊕ iota) n) (m : ℕ)
    (Inv : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ)) :
    LowAtom p m → NativeProbeContinuous (M := M) (iota := iota) m → C(M, ℝ)
  | ⟨⟨.metric false word i j, _⟩, hw⟩, Q => matrixWordContinuous F C g0 word hw i j Q
  | ⟨⟨.metric true word i j, _⟩, _⟩, _ => backgroundWordContinuous F C g0 word i j
  | ⟨⟨.inverse false i j, _⟩, _⟩, Q => inverseEntryContinuous F C g0 Inv i j Q
  | ⟨⟨.inverse true i j, _⟩, _⟩, _ => backgroundInverseContinuous C g0 i j

theorem contDiff_lowAtomContinuous (p : Expr (Fin n ⊕ iota) n) (m : ℕ)
    (Inv : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    (hInv : ContDiff ℝ ∞ Inv) (a : LowAtom p m) :
    ContDiff ℝ ∞ (lowAtomContinuous F C g0 p m Inv a) := by
  rcases a with ⟨⟨a, ha⟩, hw⟩
  cases a with
  | metric b word i j =>
    cases b with
    | false => exact contDiff_matrixWordContinuous F C g0 word hw i j
    | true => exact contDiff_const
  | inverse b i j =>
    cases b with
    | false => exact contDiff_inverseEntryContinuous F C g0 Inv hInv i j
    | true => exact contDiff_const

def lowAtomTupleContinuous (p : Expr (Fin n ⊕ iota) n) (m : ℕ)
    (Inv : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : NativeProbeContinuous (M := M) (iota := iota) m) : C(M, LowAtom p m → ℝ) :=
  packContinuous (fun a => lowAtomContinuous F C g0 p m Inv a Q)

theorem contDiff_lowAtomTupleContinuous (p : Expr (Fin n ⊕ iota) n) (m : ℕ)
    (Inv : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    (hInv : ContDiff ℝ ∞ Inv) :
    ContDiff ℝ ∞ (lowAtomTupleContinuous F C g0 p m Inv) := by
  apply (packContinuous (M := M) (A := LowAtom p m)).contDiff.comp
  exact contDiff_pi.mpr (contDiff_lowAtomContinuous F C g0 p m Inv hInv)

theorem lowAtomTupleContinuous_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (p : Expr (Fin n ⊕ iota) n) (m : ℕ)
    (Inv : C(M, Matrix (Fin n) (Fin n) ℝ) → C(M, Matrix (Fin n) (Fin n) ℝ))
    (Q : NativeProbeContinuous (M := M) (iota := iota) m) (g : RiemannianMetric n M)
    (hQ : ∀ ab w (hw : w.length ≤ m) x,
      Q ab (wordIndex w hw) x = directionalWord F w (probeDifference F g g0 ab) x)
    (hInv : ∀ x, Inv (matrixValueContinuous F C g0 Q) x =
      (matrixValueContinuous F C g0 Q x)⁻¹) (x : M) (a : LowAtom p m) :
    lowAtomTupleContinuous F C g0 p m Inv Q x a =
      nativeValues (combinedFields F C) (DeTurckSourceJetNative.compatibleMatrix C g0 g)
        x a.val.val := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  rw [lowAtomTupleContinuous, packContinuous_apply]
  rcases a with ⟨⟨a, ha⟩, hw⟩
  cases a with
  | metric b word i j =>
    cases b with
    | false => exact matrixWordContinuous_eq F C g0 hF word hw i j Q g hQ x
    | true => rfl
  | inverse b i j =>
    cases b with
    | false =>
      change Inv (matrixValueContinuous F C g0 Q) x i j = (C.matrix g x)⁻¹ i j
      rw [hInv, matrixValueContinuous_eq F C g0 hF Q g hQ x]
    | true => rfl

variable [MeasurableSpace M] [BorelSpace M] (μ : Measure M) [IsFiniteMeasure μ]

abbrev NativeProbeL2 (k : ℕ) := (iota × iota) → WordIndex iota k → Lp ℝ 2 μ

def matrixDifferenceWordL2 {k : ℕ} (word : List (Fin n ⊕ iota))
    (hw : word.length ≤ k) (i j : Fin n) :
    NativeProbeL2 (iota := iota) μ k →L[ℝ] Lp ℝ 2 μ :=
  ∑ ab : iota × iota,
    (termsL2 μ (probeWordTerms F C g0 i j ab word)
      (fun t ht => (probeWordTerms_order F C g0 i j ab word t ht).trans hw)).comp
        (ContinuousLinearMap.proj ab)

theorem matrixDifferenceWordL2_ae_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {k : ℕ} (word : List (Fin n ⊕ iota)) (hw : word.length ≤ k) (i j : Fin n)
    (Q : NativeProbeL2 (iota := iota) μ k) (g h : RiemannianMetric n M)
    (hQ : ∀ ab w (hword : w.length ≤ k),
      Q ab (wordIndex w hword) =ᵐ[μ] directionalWord F w (probeDifference F g h ab)) :
    matrixDifferenceWordL2 F C g0 μ word hw i j Q =ᵐ[μ]
      directionalWord (combinedFields F C) word
        (fun y => C.matrix g y i j - C.matrix h y i j) := by
  let q (ab : iota × iota) : Lp ℝ 2 μ :=
    termsL2 μ (probeWordTerms F C g0 i j ab word)
      (fun t ht => (probeWordTerms_order F C g0 i j ab word t ht).trans hw) (Q ab)
  have hq (ab : iota × iota) : q ab =ᵐ[μ]
      directionalTerms F (probeWordTerms F C g0 i j ab word) (probeDifference F g h ab) :=
    termsL2_ae_eq F μ (probeWordTerms F C g0 i j ab word)
      (fun t ht => (probeWordTerms_order F C g0 i j ab word t ht).trans hw)
      (Q ab) (probeDifference F g h ab) (hQ ab)
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ q, ae_all_iff.mpr hq] with x hsum hterms
  simp only [matrixDifferenceWordL2, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change (∑ ab : iota × iota, q ab) x = _
  rw [hsum, matrixDifferenceWord_eq_sum F C g0 hF g h word i j x]
  exact Finset.sum_congr rfl (fun ab _ => hterms ab)

def matrixWordL2 {k : ℕ} (word : List (Fin n ⊕ iota)) (hw : word.length ≤ k)
    (i j : Fin n) (Q : NativeProbeL2 (iota := iota) μ k) : Lp ℝ 2 μ :=
  ContinuousMap.toLp 2 μ ℝ (backgroundWordContinuous F C g0 word i j) +
    matrixDifferenceWordL2 F C g0 μ word hw i j Q

theorem contDiff_matrixWordL2 {k : ℕ} (word : List (Fin n ⊕ iota))
    (hw : word.length ≤ k) (i j : Fin n) :
    ContDiff ℝ ∞ (matrixWordL2 F C g0 μ word hw i j) :=
  contDiff_const.add (matrixDifferenceWordL2 F C g0 μ word hw i j).contDiff

theorem matrixWordL2_ae_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {k : ℕ} (word : List (Fin n ⊕ iota)) (hw : word.length ≤ k) (i j : Fin n)
    (Q : NativeProbeL2 (iota := iota) μ k) (g : RiemannianMetric n M)
    (hQ : ∀ ab w (hword : w.length ≤ k),
      Q ab (wordIndex w hword) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) :
    matrixWordL2 F C g0 μ word hw i j Q =ᵐ[μ]
      directionalWord (combinedFields F C) word (fun y => C.matrix g y i j) := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℝ)
    (backgroundWordContinuous F C g0 word i j),
    matrixDifferenceWordL2_ae_eq F C g0 μ hF word hw i j Q g g0 hQ,
    Lp.coeFn_add
      (ContinuousMap.toLp 2 μ ℝ (backgroundWordContinuous F C g0 word i j))
      (matrixDifferenceWordL2 F C g0 μ word hw i j Q)] with x hb hd hadd
  change (ContinuousMap.toLp 2 μ ℝ (backgroundWordContinuous F C g0 word i j) +
    matrixDifferenceWordL2 F C g0 μ word hw i j Q) x = _
  rw [hadd, Pi.add_apply, hb, hd]
  rw [congrFun (C.directionalWord_matrix_sub g g0 (combinedFields F C) word i j) x]
  change directionalWord (combinedFields F C) word (fun y => C.matrix g0 y i j) x +
    (directionalWord (combinedFields F C) word (fun y => C.matrix g y i j) x -
      directionalWord (combinedFields F C) word (fun y => C.matrix g0 y i j) x) = _
  ring

def matrixTupleL2 {k : ℕ} (label : A → Bool)
    (word : A → List (Fin n ⊕ iota)) (entry : A → Fin n × Fin n)
    (hword : ∀ a, label a = false → (word a).length ≤ k)
    (Q : NativeProbeL2 (iota := iota) μ k) : Lp (A → ℝ) 2 μ :=
  packL2 μ (fun a => if ha : label a = false then
    matrixWordL2 F C g0 μ (word a) (hword a ha) (entry a).1 (entry a).2 Q
    else ContinuousMap.toLp 2 μ ℝ
      (backgroundWordContinuous F C g0 (word a) (entry a).1 (entry a).2))

theorem contDiff_matrixTupleL2 {k : ℕ} (label : A → Bool)
    (word : A → List (Fin n ⊕ iota)) (entry : A → Fin n × Fin n)
    (hword : ∀ a, label a = false → (word a).length ≤ k) :
    ContDiff ℝ ∞ (matrixTupleL2 F C g0 μ label word entry hword) := by
  apply (packL2 (A := A) μ).contDiff.comp
  apply contDiff_pi.mpr
  intro a
  by_cases ha : label a = false
  · simpa only [dif_pos ha] using
      contDiff_matrixWordL2 F C g0 μ (word a) (hword a ha) (entry a).1 (entry a).2
  · simp only [dif_neg ha]
    exact contDiff_const

theorem matrixTupleL2_ae_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    {k : ℕ} (label : A → Bool) (word : A → List (Fin n ⊕ iota))
    (entry : A → Fin n × Fin n) (hword : ∀ a, label a = false → (word a).length ≤ k)
    (Q : NativeProbeL2 (iota := iota) μ k) (g : RiemannianMetric n M)
    (hQ : ∀ ab w (hw : w.length ≤ k),
      Q ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) :
    matrixTupleL2 F C g0 μ label word entry hword Q =ᵐ[μ] fun x a =>
      if label a = false then directionalWord (combinedFields F C) (word a)
        (fun y => C.matrix g y (entry a).1 (entry a).2) x
      else directionalWord (combinedFields F C) (word a)
        (fun y => C.matrix g0 y (entry a).1 (entry a).2) x := by
  apply packL2_ae_eq
  intro a
  by_cases ha : label a = false
  · simpa only [dif_pos ha, if_pos ha] using
      matrixWordL2_ae_eq F C g0 μ hF (word a) (hword a ha)
        (entry a).1 (entry a).2 Q g hQ
  · simp only [dif_neg ha, if_neg ha]
    change ContinuousMap.toLp 2 μ ℝ
        (backgroundWordContinuous F C g0 (word a) (entry a).1 (entry a).2) =ᵐ[μ]
      (backgroundWordContinuous F C g0 (word a) (entry a).1 (entry a).2)
    exact ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℝ)
      (backgroundWordContinuous F C g0 (word a) (entry a).1 (entry a).2)

def highAtomL2 (p : Expr (Fin n ⊕ iota) n) (m k : ℕ)
    (hp : p.metricOrder false ≤ k) :
    HighAtom p m → NativeProbeL2 (iota := iota) μ k → Lp ℝ 2 μ
  | ⟨⟨.metric false word i j, ha⟩, _⟩, Q =>
      matrixWordL2 F C g0 μ word
        ((p.word_length_le_metricOrder_of_mem false word i j ha).trans hp) i j Q
  | ⟨⟨.metric true word i j, _⟩, _⟩, _ =>
      ContinuousMap.toLp 2 μ ℝ (backgroundWordContinuous F C g0 word i j)
  | ⟨⟨.inverse _ _ _, _⟩, hw⟩, _ => False.elim (hw (Nat.zero_le m))

theorem contDiff_highAtomL2 (p : Expr (Fin n ⊕ iota) n) (m k : ℕ)
    (hp : p.metricOrder false ≤ k) (a : HighAtom p m) :
    ContDiff ℝ ∞ (highAtomL2 F C g0 μ p m k hp a) := by
  rcases a with ⟨⟨a, ha⟩, hw⟩
  cases a with
  | metric b word i j =>
    cases b with
    | false =>
      exact contDiff_matrixWordL2 F C g0 μ word
        ((p.word_length_le_metricOrder_of_mem false word i j ha).trans hp) i j
    | true => exact contDiff_const
  | inverse b i j => exact False.elim (hw (Nat.zero_le m))

def highAtomTupleL2 (p : Expr (Fin n ⊕ iota) n) (m k : ℕ)
    (hp : p.metricOrder false ≤ k) (Q : NativeProbeL2 (iota := iota) μ k) :
    Lp (HighAtom p m → ℝ) 2 μ :=
  packL2 μ (fun a => highAtomL2 F C g0 μ p m k hp a Q)

theorem contDiff_highAtomTupleL2 (p : Expr (Fin n ⊕ iota) n) (m k : ℕ)
    (hp : p.metricOrder false ≤ k) :
    ContDiff ℝ ∞ (highAtomTupleL2 F C g0 μ p m k hp) := by
  apply (packL2 (A := HighAtom p m) μ).contDiff.comp
  exact contDiff_pi.mpr (contDiff_highAtomL2 F C g0 μ p m k hp)

theorem highAtomTupleL2_ae_eq
    (hF : ∀ (x : M) (v : TangentSpace (𝓡 n) x),
      (∑ a, g0.inner x (F a x) v • F a x) = v)
    (p : Expr (Fin n ⊕ iota) n) (m k : ℕ) (hp : p.metricOrder false ≤ k)
    (Q : NativeProbeL2 (iota := iota) μ k) (g : RiemannianMetric n M)
    (hQ : ∀ ab w (hw : w.length ≤ k),
      Q ab (wordIndex w hw) =ᵐ[μ] directionalWord F w (probeDifference F g g0 ab)) :
    highAtomTupleL2 F C g0 μ p m k hp Q =ᵐ[μ] fun x a =>
      nativeValues (combinedFields F C) (DeTurckSourceJetNative.compatibleMatrix C g0 g)
        x a.val.val := by
  apply packL2_ae_eq
  intro a
  rcases a with ⟨⟨a, ha⟩, hw⟩
  cases a with
  | metric b word i j =>
    cases b with
    | false =>
      exact matrixWordL2_ae_eq F C g0 μ hF word
        ((p.word_length_le_metricOrder_of_mem false word i j ha).trans hp) i j Q g hQ
    | true =>
      change ContinuousMap.toLp 2 μ ℝ (backgroundWordContinuous F C g0 word i j) =ᵐ[μ]
        (backgroundWordContinuous F C g0 word i j)
      exact ContinuousMap.coeFn_toLp (p := (2 : ENNReal)) (μ := μ) (𝕜 := ℝ)
        (backgroundWordContinuous F C g0 word i j)
  | inverse b i j => exact False.elim (hw (Nat.zero_le m))

end NativeProbeWords

end PoincareConjecture.DeTurckJetAffineNative

end
