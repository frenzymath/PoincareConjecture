import PoincareConjecture.Proofs.M03.Existence.ChartStateSmoothness
import Mathlib.Analysis.Calculus.ContDiff.Operations











set_option autoImplicit false
set_option maxHeartbeats 10000000

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}

private theorem contDiffAt_finset_sum
    {ι X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (s : Finset ι) {f : ι → X → Y} {p : X}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 1 (f i) p) :
    ContDiffAt ℝ 1 (fun q => s.sum (fun i => f i q)) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (contDiffAt_const :
        ContDiffAt ℝ 1 (fun _ : X => (0 : Y)) p)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (by simp)).add
        (ih (fun i hi => hf i (by simp [hi])))

theorem contDiffAt_chartStateSource
    (background : MetricJet2 (n := n))
    (p : ChartState (n := n))
    (hpos : p.1.PosDef) (i j : Fin n) :
    ContDiffAt ℝ 1
      (fun q : ChartState (n := n) => chartStateSource background q i j) p := by
  have hinv : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) => q.1⁻¹) p := by
    have hdet : p.1.det ≠ 0 :=
      (p.1.isUnit_iff_isUnit_det.mp hpos.isUnit).ne_zero
    exact (contDiffAt_matrix_inv_of_nonsingular p.1 hdet).comp
      p contDiffAt_fst
  have hinvEntry (k l : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) => q.1⁻¹ k l) p := by
    convert (contDiffAt_apply ℝ _ l _).comp p
      ((contDiffAt_apply ℝ _ k _).comp p hinv) using 1
    rfl
  have hvalue (i j : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) => q.1 i j) p := by
    fun_prop
  have hfirst (a i j : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) => q.2.1 a i j) p := by
    fun_prop
  have hsecond (a b i j : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) => q.2.2 a b i j) p := by
    fun_prop
  have hchrist (k i j : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) =>
        christoffelJet (chartStateJet q) k i j) p := by
    unfold christoffelJet chartStateJet
    apply ContDiffAt.mul contDiffAt_const
    apply contDiffAt_finset_sum
    intro l hl
    apply ContDiffAt.mul
    · exact hinvEntry k l
    · apply ContDiffAt.sub
      · exact (hfirst i l j).add (hfirst j l i)
      · exact hfirst l i j
  have hinverseFirst (a k l : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) =>
        inverseFirst (chartStateJet q) a k l) p := by
    unfold inverseFirst chartStateJet
    apply ContDiffAt.neg
    apply contDiffAt_finset_sum
    intro u hu
    apply contDiffAt_finset_sum
    intro v hv
    apply ContDiffAt.mul
    · exact (hinvEntry k u).mul (hfirst a u v)
    · exact hinvEntry v l
  have hchristSecond (a k i j : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) =>
        christoffelSecond (chartStateJet q) a k i j) p := by
    unfold christoffelSecond chartStateJet
    apply ContDiffAt.mul contDiffAt_const
    apply contDiffAt_finset_sum
    intro l hl
    apply ContDiffAt.add
    · apply ContDiffAt.mul
      · exact hinverseFirst a k l
      · exact (hfirst i l j).add (hfirst j l i) |>.sub (hfirst l i j)
    · apply ContDiffAt.mul
      · exact hinvEntry k l
      · exact (hsecond a i l j).add (hsecond a j l i) |>.sub
          (hsecond a l i j)
  have hmixed (i j k l : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) =>
        mixedCurvatureJet (chartStateJet q) i j k l) p := by
    unfold mixedCurvatureJet
    apply ContDiffAt.add
    · exact (hchristSecond i l j k).sub (hchristSecond j l i k)
    · apply contDiffAt_finset_sum
      intro m hm
      apply ContDiffAt.sub
      · exact (hchrist m j k).mul (hchrist l i m)
      · exact (hchrist m i k).mul (hchrist l j m)
  have hricci (i j : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) => ricciJet (chartStateJet q) i j) p := by
    unfold ricciJet
    apply contDiffAt_finset_sum
    intro k hk
    exact hmixed k i j k
  have hdeTurck (k : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) =>
        deTurckVector background (chartStateJet q) k) p := by
    unfold deTurckVector chartStateJet
    apply contDiffAt_finset_sum
    intro a ha
    apply contDiffAt_finset_sum
    intro b hb
    apply ContDiffAt.mul
    · exact hinvEntry a b
    · exact (hchrist k a b).sub contDiffAt_const
  have hdeTurckFirst (a k : Fin n) : ContDiffAt ℝ 1
      (fun q : ChartState (n := n) =>
        deTurckVectorFirst background (chartStateJet q) a k) p := by
    unfold deTurckVectorFirst chartStateJet
    apply contDiffAt_finset_sum
    intro u hu
    apply contDiffAt_finset_sum
    intro v hv
    apply ContDiffAt.add
    · exact (hinverseFirst a u v).mul
        ((hchrist k u v).sub contDiffAt_const)
    · exact (hinvEntry u v).mul
        ((hchristSecond a k u v).sub contDiffAt_const)
  unfold chartStateSource chartStateJet ricciDeTurckSource
    ricciJet mixedCurvatureJet christoffelSecond inverseFirst christoffelJet
    lieDerivativeJet deTurckVector deTurckVectorFirst
  apply ContDiffAt.add
  · apply ContDiffAt.mul contDiffAt_const
    exact hricci i j
  · apply contDiffAt_finset_sum
    intro k hk
    apply ContDiffAt.add
    · apply ContDiffAt.add
      · exact (hdeTurck k).mul (hfirst k i j)
      · exact (hvalue k j).mul (hdeTurckFirst i k)
    · exact (hvalue i k).mul (hdeTurckFirst j k)

end PoincareConjecture.DeTurckNative
