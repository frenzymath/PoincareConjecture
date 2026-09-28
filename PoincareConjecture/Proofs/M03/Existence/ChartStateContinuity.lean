import PoincareConjecture.Proofs.M03.Existence.ChartJetSource

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

@[fun_prop]
theorem continuousAt_finset_sum
    {ι X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommMonoid Y] [ContinuousAdd Y]
    (s : Finset ι) {f : ι → X → Y} {p : X}
    (hf : ∀ i ∈ s, ContinuousAt (f i) p) :
    ContinuousAt (fun q => ∑ i ∈ s, f i q) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (continuousAt_const : ContinuousAt (fun _ : X => (0 : Y)) p)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))

abbrev ChartState :=
  Matrix (Fin n) (Fin n) ℝ ×
    (Fin n → Matrix (Fin n) (Fin n) ℝ) ×
    (Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)

def chartStateJet (p : ChartState (n := n)) : MetricJet2 (n := n) :=
  { value := p.1
    first := p.2.1
    second := p.2.2 }

def chartStateSource (background : MetricJet2 (n := n))
    (p : ChartState (n := n)) (i j : Fin n) : ℝ :=
  ricciDeTurckSource background (chartStateJet p) i j

theorem continuousAt_chartStateSource
    (background : MetricJet2 (n := n))
    (p : ChartState (n := n))
    (hpos : p.1.PosDef) (i j : Fin n) :
    ContinuousAt (fun q : ChartState (n := n) => chartStateSource background q i j) p := by
  have hinv : ContinuousAt (fun q : ChartState (n := n) => q.1⁻¹) p := by
    exact (continuousAt_matrix_inv_of_posDef p.1 hpos).comp continuousAt_fst
  have hinvEntry (k l : Fin n) :
      ContinuousAt (fun q : ChartState (n := n) => q.1⁻¹ k l) p := by
    exact (continuousAt_apply l _).comp ((continuousAt_apply k _).comp hinv)
  have hchrist (k i j : Fin n) :
      ContinuousAt (fun q : ChartState (n := n) =>
        christoffelJet (chartStateJet q) k i j) p := by
    unfold christoffelJet chartStateJet
    apply ContinuousAt.mul continuousAt_const
    apply continuousAt_finset_sum
    intro l hl
    apply ContinuousAt.mul
    · exact hinvEntry k l
    · apply ContinuousAt.add
      · fun_prop
      · apply ContinuousAt.neg
        fun_prop
  have hinverseFirst (a k l : Fin n) :
      ContinuousAt (fun q : ChartState (n := n) =>
        inverseFirst (chartStateJet q) a k l) p := by
    unfold inverseFirst chartStateJet
    apply ContinuousAt.neg
    apply continuousAt_finset_sum
    intro u hu
    apply continuousAt_finset_sum
    intro v hv
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · exact hinvEntry k u
      · fun_prop
    · exact hinvEntry v l
  have hchristSecond (a k i j : Fin n) :
      ContinuousAt (fun q : ChartState (n := n) =>
        christoffelSecond (chartStateJet q) a k i j) p := by
    unfold christoffelSecond chartStateJet
    apply ContinuousAt.mul continuousAt_const
    apply continuousAt_finset_sum
    intro l hl
    apply ContinuousAt.add
    · apply ContinuousAt.mul
      · exact hinverseFirst a k l
      · fun_prop
    · apply ContinuousAt.mul
      · exact hinvEntry k l
      · fun_prop
  have hmixed (i j k l : Fin n) :
      ContinuousAt (fun q : ChartState (n := n) =>
        mixedCurvatureJet (chartStateJet q) i j k l) p := by
    unfold mixedCurvatureJet
    apply ContinuousAt.add
    · apply ContinuousAt.sub
      · exact hchristSecond i l j k
      · exact hchristSecond j l i k
    · apply continuousAt_finset_sum
      intro m hm
      apply ContinuousAt.sub
      · apply ContinuousAt.mul
        · exact hchrist m j k
        · exact hchrist l i m
      · apply ContinuousAt.mul
        · exact hchrist m i k
        · exact hchrist l j m
  have hricci (i j : Fin n) :
      ContinuousAt (fun q : ChartState (n := n) =>
        ricciJet (chartStateJet q) i j) p := by
    unfold ricciJet chartStateJet
    apply continuousAt_finset_sum
    intro k hk
    exact hmixed k i j k
  have hdeTurck (k : Fin n) :
      ContinuousAt (fun q : ChartState (n := n) =>
        deTurckVector background (chartStateJet q) k) p := by
    unfold deTurckVector chartStateJet
    apply continuousAt_finset_sum
    intro a ha
    apply continuousAt_finset_sum
    intro b hb
    apply ContinuousAt.mul
    · exact hinvEntry a b
    · apply ContinuousAt.sub
      · simpa [chartStateJet] using hchrist k a b
      · exact continuousAt_const
  have hdeTurckFirst (a k : Fin n) :
      ContinuousAt (fun q : ChartState (n := n) =>
        deTurckVectorFirst background (chartStateJet q) a k) p := by
    unfold deTurckVectorFirst chartStateJet
    apply continuousAt_finset_sum
    intro u hu
    apply continuousAt_finset_sum
    intro v hv
    apply ContinuousAt.add
    · apply ContinuousAt.mul
      · exact hinverseFirst a u v
      · apply ContinuousAt.sub
        · simpa [chartStateJet] using hchrist k u v
        · exact continuousAt_const
    · apply ContinuousAt.mul
      · exact hinvEntry u v
      · apply ContinuousAt.sub
        · simpa [chartStateJet] using hchristSecond a k u v
        · exact continuousAt_const
  unfold chartStateSource chartStateJet ricciDeTurckSource ricciJet
  apply ContinuousAt.add
  · apply ContinuousAt.mul continuousAt_const
    exact hricci i j
  · unfold lieDerivativeJet
    apply continuousAt_finset_sum
    intro k hk
    apply ContinuousAt.add
    · apply ContinuousAt.add
      · apply ContinuousAt.mul
        · exact hdeTurck k
        · fun_prop
      · apply ContinuousAt.mul
        · fun_prop
        · exact hdeTurckFirst i k
    · apply ContinuousAt.mul
      · fun_prop
      · exact hdeTurckFirst j k

end PoincareConjecture.DeTurckNative
