import PoincareConjecture.Proofs.M35.Uniqueness.Heat.JetFamilyContinuity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def HasContinuousWeakJet (u : ι → L2) (s : ℕ) : Prop :=
  ∃ q : ι → List (Fin n) → L2, (∀ t, q t [] = u t) ∧
    (∀ t, IsWeakSchwartzJet (q t) s) ∧
    ∀ w, w.length ≤ s → Continuous (fun t => q t w)

theorem HasContinuousWeakJet.mono {u : ι → L2} {s r : ℕ}
    (hu : HasContinuousWeakJet u s) (hrs : r ≤ s) : HasContinuousWeakJet u r := by
  obtain ⟨q, hq0, hq, hqc⟩ := hu
  exact ⟨q, hq0, fun t => (hq t).mono hrs, fun w hw => hqc w (hw.trans hrs)⟩

theorem HasContinuousWeakJet.continuous {u : ι → L2} {s : ℕ}
    (hu : HasContinuousWeakJet u s) : Continuous u := by
  obtain ⟨q, hq0, _hq, hqc⟩ := hu
  simpa only [hq0] using hqc [] (by simp)

theorem HasContinuousWeakJet.slice {u : ι → L2} {s : ℕ}
    (hu : HasContinuousWeakJet u s) (t : ι) : HasFiniteWeakJet (u t) s := by
  obtain ⟨q, hq0, hq, _hqc⟩ := hu
  exact ⟨q t, hq0 t, hq t⟩

theorem HasContinuousWeakJet.zero (s : ℕ) :
    HasContinuousWeakJet (fun _ : ι => (0 : L2)) s :=
  ⟨fun _ _ => 0, fun _ => rfl,
    fun _ _ _ i => HasWeakSchwartzDerivative.zero (EuclideanSpace.single i (1 : ℝ)),
    fun _ _ => continuous_const⟩

theorem HasContinuousWeakJet.add {u v : ι → L2} {s : ℕ}
    (hu : HasContinuousWeakJet u s) (hv : HasContinuousWeakJet v s) :
    HasContinuousWeakJet (fun t => u t + v t) s := by
  obtain ⟨q, hq0, hq, hqc⟩ := hu
  obtain ⟨p, hp0, hp, hpc⟩ := hv
  exact ⟨fun t w => q t w + p t w, fun t => congrArg₂ (· + ·) (hq0 t) (hp0 t),
    fun t w hw i => (hq t w hw i).add (hp t w hw i),
    fun w hw => (hqc w hw).add (hpc w hw)⟩

theorem HasContinuousWeakJet.sub {u v : ι → L2} {s : ℕ}
    (hu : HasContinuousWeakJet u s) (hv : HasContinuousWeakJet v s) :
    HasContinuousWeakJet (fun t => u t - v t) s := by
  obtain ⟨q, hq0, hq, hqc⟩ := hu
  obtain ⟨p, hp0, hp, hpc⟩ := hv
  exact ⟨fun t w => q t w - p t w, fun t => congrArg₂ (· - ·) (hq0 t) (hp0 t),
    fun t w hw i => weakSchwartzDerivative_sub (hq t w hw i) (hp t w hw i),
    fun w hw => (hqc w hw).sub (hpc w hw)⟩

theorem HasContinuousWeakJet.sum {κ : Type*} [Fintype κ]
    (u : κ → ι → L2) {s : ℕ} (hu : ∀ i, HasContinuousWeakJet (u i) s) :
    HasContinuousWeakJet (fun t => ∑ i, u i t) s := by
  classical
  choose q hq0 hq hqc using hu
  refine ⟨fun t w => ∑ i, q i t w,
    fun t => Finset.sum_congr rfl (fun i _ => hq0 i t), ?_, ?_⟩
  · intro t w hw j
    exact HasWeakSchwartzDerivative.finset_sum Finset.univ _ _ _
      (fun i _ => hq i t w hw j)
  · intro w hw
    exact continuous_finsetSum _ (fun i _ => hqc i w hw)

theorem HasContinuousWeakJet.nsmul {u : ι → L2} {s : ℕ}
    (hu : HasContinuousWeakJet u s) (c : ℕ) :
    HasContinuousWeakJet (fun t => c • u t) s := by
  induction c with
  | zero => simpa only [zero_smul] using HasContinuousWeakJet.zero (ι := ι) (n := n) s
  | succ c ih => simpa only [succ_nsmul] using ih.add hu

theorem HasContinuousWeakJet.mul {u : ι → L2} {s : ℕ}
    (hu : HasContinuousWeakJet u s) (A : ι → 𝓢(V, ℝ))
    (hA : ∀ w, w.length ≤ s →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t)))) :
    HasContinuousWeakJet (fun t => schwartzMultiplier (A t) (u t)) s := by
  obtain ⟨q, hq0, hq, hqc⟩ := hu
  let e := fun t => JetExpression.term (A t) []
  have he (t : ι) : (e t).orderLE 0 := Nat.zero_le 0
  refine ⟨fun t w => ((e t).iteratedDerivative w).eval (q t), ?_, ?_, ?_⟩
  · intro t
    exact congrArg (schwartzMultiplier (A t)) (hq0 t)
  · intro t
    exact (e t).isWeakJet_eval_iteratedDerivative (he t) (q t)
      (by simpa only [Nat.add_zero] using hq t)
  · intro w hw
    exact continuous_iterated_productJet A q hA hqc w hw

theorem HasContinuousWeakJet.exists_derivative {u : ι → L2} {s : ℕ}
    (hu : HasContinuousWeakJet u (s + 1)) (i : Fin n) :
    ∃ d : ι → L2,
      (∀ t, HasWeakSchwartzDerivative (u t) (d t) (EuclideanSpace.single i (1 : ℝ))) ∧
      HasContinuousWeakJet d s := by
  obtain ⟨q, hq0, hq, hqc⟩ := hu
  refine ⟨fun t => q t [i], ?_, fun t w => q t (w ++ [i]), fun _ => rfl, ?_, ?_⟩
  · intro t
    simpa only [hq0 t] using hq t [] (by simp) i
  · intro t w hw j
    exact hq t (w ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega) j
  · intro w hw
    exact hqc (w ++ [i]) (by simp only [List.length_append, List.length_singleton]; omega)

end PoincareConjecture.M35.Uniqueness.Heat
