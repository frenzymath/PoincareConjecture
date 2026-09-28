import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorSmoothRealization
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.WeakJetTimeDerivative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv BoundedContinuousFunction

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckHigherDomainNative DeTurckDomainRegularityNative
  DeTurckMetricDomainNative DeTurckJetCoordinatesNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem schwartz_ordered_isWeakJet (φ : 𝓢(V, ℝ)) (m : ℕ) :
    IsWeakSchwartzJet (fun w => (orderedSchwartzDerivative w φ).toLp 2 volume) m := by
  intro w _ i ψ
  have h := inner_schwartzLineDeriv
    (orderedSchwartzDerivative w φ) ψ (EuclideanSpace.single i (1 : ℝ))
  change inner ℝ ((∂_{EuclideanSpace.single i (1 : ℝ)}
    (orderedSchwartzDerivative w φ)).toLp 2 volume) (ψ.toLp 2 volume) = _
  linarith only [h]

theorem finiteJetContinuous_eq_schwartz_of_nil_eq
    (q : List (Fin n) → L2) (φ : 𝓢(V, ℝ)) (m p : ℕ)
    (w : List (Fin n)) (hw : 2 * p + w.length ≤ m)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ))) (hq : IsWeakSchwartzJet q m)
    (hq0 : q [] = φ.toLp 2 volume) :
    finiteJetContinuous m p w hw hp (fun v => q (List.ofFn v.2)) =
      (orderedSchwartzDerivative w φ).toBoundedContinuousFunction := by
  have he : (fun v : WordIndex (Fin n) m => q (List.ofFn v.2)) = schwartzWordTuple m φ := by
    funext v
    exact hq.eq_of_nil_eq (schwartz_ordered_isWeakJet φ m) hq0 (List.ofFn v.2)
      (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ v.1.isLt)
  rw [he, finiteJetContinuous_schwartz]

theorem continuous_schwartzDerivative_of_weak_jets
    (φ : ι → 𝓢(V, ℝ)) (q : ι → List (Fin n) → L2) (m p : ℕ)
    (w : List (Fin n)) (hw : 2 * p + w.length ≤ m)
    (hp : (n : ℝ) < 2 * (2 * (p : ℝ)))
    (hq : ∀ t, IsWeakSchwartzJet (q t) m) (hq0 : ∀ t, q t [] = (φ t).toLp 2 volume)
    (hqc : ∀ v, v.length ≤ m → Continuous (fun t => q t v)) :
    Continuous (fun t => (orderedSchwartzDerivative w (φ t)).toBoundedContinuousFunction) := by
  have htuple : Continuous (fun t => fun v : WordIndex (Fin n) m => q t (List.ofFn v.2)) :=
    continuous_pi (fun v => hqc _
      (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ v.1.isLt))
  have he (t : ι) := finiteJetContinuous_eq_schwartz_of_nil_eq
    (q t) (φ t) m p w hw hp (hq t) (hq0 t)
  simpa only [Function.comp_def, he] using
    (finiteJetContinuous m p w hw hp).continuous.comp htuple

theorem hasDerivAt_schwartzDerivative_of_weak_jets
    (φ ψ : ℝ → 𝓢(V, ℝ)) (q p : ℝ → List (Fin n) → L2)
    {a b t : ℝ} (ht : t ∈ Ioo a b) (m r : ℕ) (w : List (Fin n))
    (hw : 2 * r + w.length ≤ m) (hr : (n : ℝ) < 2 * (2 * (r : ℝ)))
    (hq : ∀ s ∈ Ioo a b, IsWeakSchwartzJet (q s) m)
    (hp : ∀ s ∈ Ioo a b, IsWeakSchwartzJet (p s) m)
    (hq0 : ∀ s ∈ Ioo a b, q s [] = (φ s).toLp 2 volume)
    (hp0 : ∀ s ∈ Ioo a b, p s [] = (ψ s).toLp 2 volume)
    (hpc : ∀ v, v.length ≤ m → ContinuousOn (fun s => p s v) (Ioo a b))
    (hd : ∀ s ∈ Ioo a b, HasDerivAt (fun y => q y []) (p s []) s) :
    HasDerivAt (fun s => (orderedSchwartzDerivative w (φ s)).toBoundedContinuousFunction)
      (orderedSchwartzDerivative w (ψ t)).toBoundedContinuousFunction t := by
  have htuple : HasDerivAt (fun s => fun v : WordIndex (Fin n) m => q s (List.ofFn v.2))
      (fun v => p t (List.ofFn v.2)) t :=
    hasDerivAt_pi.mpr (fun v => weakJet_hasDerivAt_of_nil q p hq hp hpc hd
      (List.ofFn v.2) (by simpa only [List.length_ofFn] using Nat.le_of_lt_succ v.1.isLt) ht)
  have h := (finiteJetContinuous m r w hw hr).hasFDerivAt.comp_hasDerivAt t htuple
  rw [finiteJetContinuous_eq_schwartz_of_nil_eq (p t) (ψ t) m r w hw hr
    (hp t ht) (hp0 t ht)] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
  exact (finiteJetContinuous_eq_schwartz_of_nil_eq (q s) (φ s) m r w hw hr
    (hq s hs) (hq0 s hs)).symm

end PoincareConjecture.M35.Uniqueness.Heat
