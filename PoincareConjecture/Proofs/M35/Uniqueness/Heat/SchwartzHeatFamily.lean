import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SchwartzRepresentative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped SchwartzMap Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

open DeTurckHigherDomainNative DeTurckDomainRegularityNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem exists_regular_schwartz_heat_family
    (u : ℕ → ℝ → L2) {a b : ℝ} {K : Set V} (hK : IsCompact K)
    (huK : ∀ j t, t ∈ Ioo a b → ∀ᵐ x ∂volume, x ∉ K → u j t x = 0)
    (hu : ∀ j s, HasContinuousWeakJet (fun t : Ioo a b => u j t) s)
    (hd : ∀ j t, t ∈ Ioo a b → HasDerivAt (u j) (u (j + 1) t) t) :
    ∃ φ : ℕ → ℝ → 𝓢(V, ℝ),
      (∀ j t, t ∈ Ioo a b → (φ j t).toLp 2 volume = u j t) ∧
      (∀ j t x, x ∉ K → φ j t x = 0) ∧
      (∀ j w, ContinuousOn (fun t =>
        (orderedSchwartzDerivative w (φ j t)).toBoundedContinuousFunction) (Ioo a b)) ∧
      ∀ j w t, t ∈ Ioo a b → HasDerivAt
        (fun s => (orderedSchwartzDerivative w (φ j s)).toBoundedContinuousFunction)
        (orderedSchwartzDerivative w (φ (j + 1) t)).toBoundedContinuousFunction t := by
  classical
  choose Φ hΦ0 hΦK hΦc using fun j => exists_continuous_schwartz_representative
    (fun t : Ioo a b => u j t) hK (fun t => huK j t t.property) (hu j)
  choose Q hQ0 hQ hQc using fun j => exists_continuous_coherent_weakJet
    (fun t : Ioo a b => u j t) (hu j)
  let φ : ℕ → ℝ → 𝓢(V, ℝ) := fun j t => if ht : t ∈ Ioo a b then Φ j ⟨t, ht⟩ else 0
  let q : ℕ → ℝ → List (Fin n) → L2 :=
    fun j t w => if ht : t ∈ Ioo a b then Q j ⟨t, ht⟩ w else 0
  have hφ (j : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) : φ j t = Φ j ⟨t, ht⟩ := dif_pos ht
  have hq (j : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) (w : List (Fin n)) :
      q j t w = Q j ⟨t, ht⟩ w := dif_pos ht
  have hq0 (j : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) : q j t [] = u j t := by
    rw [hq j ht]
    exact hQ0 j ⟨t, ht⟩
  have hqd (j : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) :
      HasDerivAt (fun s => q j s []) (q (j + 1) t []) t := by
    rw [hq0 (j + 1) ht]
    apply (hd j t ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hq0 j hs
  have hqweak (j : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) (m : ℕ) :
      IsWeakSchwartzJet (q j t) m := by
    simpa only [q, dif_pos ht] using hQ j ⟨t, ht⟩ m
  have hqc (j : ℕ) (w : List (Fin n)) : ContinuousOn (fun t => q j t w) (Ioo a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (hQc j w).congr (fun t => (hq j t.property w).symm)
  have hqφ (j : ℕ) {t : ℝ} (ht : t ∈ Ioo a b) : q j t [] = (φ j t).toLp 2 volume := by
    rw [hq0 j ht, hφ j ht]
    exact (hΦ0 j ⟨t, ht⟩).symm
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro j t ht
    rw [hφ j ht]
    exact hΦ0 j ⟨t, ht⟩
  · intro j t x hx
    by_cases ht : t ∈ Ioo a b
    · rw [hφ j ht]
      exact hΦK j ⟨t, ht⟩ x hx
    · simp only [φ, dif_neg ht, zero_apply]
  · intro j w
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply (hΦc j w).congr
    intro t
    simp only [Set.domRestrict, hφ j t.property]
  · intro j w t ht
    let r := n + 1
    have hr : (n : ℝ) < 2 * (2 * (r : ℝ)) := by
      dsimp only [r]
      push_cast
      nlinarith [show (0 : ℝ) ≤ n by positivity]
    exact hasDerivAt_schwartzDerivative_of_weak_jets (φ j) (φ (j + 1))
      (q j) (q (j + 1)) ht (2 * r + w.length) r w le_rfl hr
      (fun s hs => hqweak j hs _) (fun s hs => hqweak (j + 1) hs _)
      (fun s hs => hqφ j hs) (fun s hs => hqφ (j + 1) hs)
      (fun v _ => hqc (j + 1) v) (fun s hs => hqd j hs)

end PoincareConjecture.M35.Uniqueness.Heat
