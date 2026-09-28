import PoincareConjecture.Proofs.M08.IntervalSolutionUnique

set_option autoImplicit false

open Set Filter Topology

namespace PoincareConjecture.M14

structure DependentIntervalSolutionLocality {X : ℝ → Type*}
    (Sol : ℝ → ℝ → (∀ s, X s) → Prop) : Prop where
  restrict : ∀ {a b c d : ℝ} {f : ∀ s, X s},
    a ≤ c → c < d → d ≤ b → Sol a b f → Sol c d f
  paste : ∀ {a l c r : ℝ} {f g : ∀ s, X s},
    a ≤ l → l < c → c < r → Sol a c f → Sol l r g →
      (∀ s ∈ Icc l c, f s = g s) →
      Sol a r (fun s => if s ≤ c then f s else g s)

variable {X : ℝ → Type*} {E : Type*}
  (Sol : ℝ → ℝ → (∀ s, X s) → Prop)
  (hSol : DependentIntervalSolutionLocality Sol) (e : ∀ s, E ≃ X s)

include hSol e

private theorem encoded_locality :
    M08.IntervalSolutionLocality (fun a b f => Sol a b (fun s => e s (f s))) where
  restrict hac hcd hdb hf := hSol.restrict hac hcd hdb hf
  paste hal hlc hcr hf hg heq := by
    have h := hSol.paste hal hlc hcr hf hg (fun s hs => congrArg (e s) (heq hs))
    convert h using 1
    funext s
    dsimp only
    split_ifs <;> rfl

theorem exists_dependent_interval_solution_of_overlapping_cover
    {a b : ℝ} (hab : a < b) {m : ℕ} (hm : 0 < m)
    (t : Fin (m + 1) → ℝ) (l r : Fin m → ℝ)
    (ht : Monotone t) (hta : t 0 = a) (htb : t (Fin.last m) = b)
    (hpieces : ∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b ∧ l i ≤ t i.castSucc ∧
      t i.succ ≤ r i ∧ ∀ s ∈ Icc (t i.castSucc) (t i.succ),
        Icc (l i) (r i) ∈ 𝓝[Icc a b] s)
    (hlocal : ∀ i s, s ∈ Icc (l i) (r i) → ∀ z : X s,
      ∃ f : ∀ s, X s, Sol (l i) (r i) f ∧ f s = z)
    (hunique : ∀ i {c d : ℝ}, l i ≤ c → c < d → d ≤ r i →
      ∀ {f g : ∀ s, X s}, Sol c d f → Sol c d g →
        ∀ s ∈ Icc c d, f s = g s → ∀ r ∈ Icc c d, f r = g r)
    (z₀ : X a) : ∃ f : ∀ s, X s, Sol a b f ∧ f a = z₀ := by
  let Enc : ℝ → ℝ → (ℝ → E) → Prop := fun a b f => Sol a b (fun s => e s (f s))
  obtain ⟨f, hf, hf₀⟩ := M08.exists_interval_solution_of_overlapping_cover Enc
    (encoded_locality Sol hSol e) hab hm t l r ht hta htb hpieces
    (fun i s hs z => by
      obtain ⟨g, hg, hg₀⟩ := hlocal i s hs (e s z)
      refine ⟨fun r => (e r).symm (g r), ?_, ?_⟩
      · simpa only [Enc, Equiv.apply_symm_apply] using hg
      · simpa only [Equiv.symm_apply_apply] using congrArg (e s).symm hg₀)
    (fun i _ _ hlc hcd hdr f g hf hg s hs hinit => by
      have heq := hunique i hlc hcd hdr hf hg s hs (congrArg (e s) hinit)
      exact fun r hr => (e r).injective (heq r hr)) ((e a).symm z₀)
  refine ⟨fun s => e s (f s), hf, ?_⟩
  simpa only [Equiv.apply_symm_apply] using congrArg (e a) hf₀

theorem dependent_interval_solution_unique_of_cover
    {a b : ℝ} {m : ℕ} (hm : 0 < m)
    (t : Fin (m + 1) → ℝ) (l r : Fin m → ℝ)
    (ht : Monotone t) (hta : t 0 = a) (htb : t (Fin.last m) = b)
    (hpieces : ∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b ∧
      l i ≤ t i.castSucc ∧ t i.succ ≤ r i)
    (hunique : ∀ i {f g : ∀ s, X s}, Sol (l i) (r i) f → Sol (l i) (r i) g →
      ∀ s ∈ Icc (l i) (r i), f s = g s → ∀ u ∈ Icc (l i) (r i), f u = g u)
    {f g : ∀ s, X s} (hf : Sol a b f) (hg : Sol a b g) (hinit : f a = g a) :
    ∀ s ∈ Icc a b, f s = g s := by
  let Enc : ℝ → ℝ → (ℝ → E) → Prop := fun a b f => Sol a b (fun s => e s (f s))
  have hf' : Enc a b (fun s => (e s).symm (f s)) := by
    simpa only [Enc, Equiv.apply_symm_apply] using hf
  have hg' : Enc a b (fun s => (e s).symm (g s)) := by
    simpa only [Enc, Equiv.apply_symm_apply] using hg
  have heq := M08.interval_solution_unique_of_cover Enc (encoded_locality Sol hSol e)
    hm t l r ht hta htb hpieces
    (fun i f g hf hg s hs hinit => by
      have h := hunique i hf hg s hs (congrArg (e s) hinit)
      exact fun r hr => (e r).injective (h r hr)) hf' hg'
    (congrArg (e a).symm hinit)
  exact fun s hs => (e s).symm.injective (heq hs)

end PoincareConjecture.M14
