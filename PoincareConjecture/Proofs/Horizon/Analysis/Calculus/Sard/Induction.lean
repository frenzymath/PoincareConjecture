import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.Coordinate
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.FlatResidual
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Sard.HigherDerivativeWitness
import Mathlib.LinearAlgebra.Dual.Lemmas










open MeasureTheory Set Function
open scoped ContDiff Topology

universe u

namespace Poincare.Analysis


theorem scalarCriticalImage_null_on
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {V : Set E} (hV : IsOpen V)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f V) :
    volume (f '' {x | x ∈ V ∧ fderiv ℝ f x = 0}) = 0 := by
  classical
  have local_null {E : Type u} [TopologicalSpace E] [SecondCountableTopology E]
      (f : E → ℝ) (s : Set E)
      (h : ∀ x ∈ s, ∃ t ∈ nhdsWithin x s, volume (f '' t) = 0) :
      volume (f '' s) = 0 := by
    apply (IsLindelof.of_coe (s := s)).induction_on
      (p := fun t => volume (f '' t) = 0)
    · intro s t hst ht
      exact measure_mono_null (image_mono hst) ht
    · intro S hS hzero
      rw [image_sUnion, measure_sUnion_null_iff (hS.image _)]
      rintro _ ⟨s, hs, rfl⟩
      exact hzero s hs
    · exact h
  induction hm : Module.finrank ℝ E using Nat.strong_induction_on generalizing E with
  | h m ih =>
    let C : ℕ → Set E := fun k =>
      {x | x ∈ V ∧ fderiv ℝ f x = 0 ∧
        ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0}
    have strata_null (k : ℕ) (hk : 1 ≤ k) : volume (f '' (C k \ C (k + 1))) = 0 := by
      apply local_null f
      intro a ha
      have haV : a ∈ V := ha.1.1
      have hka : iteratedFDeriv ℝ k f a = 0 := ha.1.2.2 k hk le_rfl
      have hnext : iteratedFDeriv ℝ (k + 1) f a ≠ 0 := by
        intro hz
        apply ha.2
        refine ⟨haV, ha.1.2.1, ?_⟩
        intro j hj hjk
        by_cases he : j = k + 1
        · subst j
          exact hz
        · exact ha.1.2.2 j hj (by omega)
      obtain ⟨g, hg, hga, hreg, hgzero⟩ :=
        exists_regular_scalar_of_iteratedFDeriv_ne_zero hV hf haV hka hnext
      obtain ⟨W, U, p, q, hW, haW, hWV, hU, h0U, hp, hq, hp0,
        hbij, hqp, hpq, hfp, hcritical⟩ :=
        exists_regular_level_parametrization hV hf hg haV hga hreg
      let F := (fderiv ℝ g a).ker
      have hLne : (fderiv ℝ g a).toLinearMap ≠ 0 := by
        intro hz
        obtain ⟨v, hv⟩ := hreg 1
        change (fderiv ℝ g a).toLinearMap v = 1 at hv
        simp [hz] at hv
      have hdim : Module.finrank ℝ F < m := by
        have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hLne
        change Module.finrank ℝ F + 1 = Module.finrank ℝ E at hd
        omega
      have hrestricted : volume ((f ∘ p) ''
          {u | u ∈ U ∧ fderiv ℝ (f ∘ p) u = 0}) = 0 :=
        ih (Module.finrank ℝ F) hdim hU hfp rfl
      refine ⟨W ∩ (C k \ C (k + 1)),
        Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds haW)) self_mem_nhdsWithin, ?_⟩
      apply measure_mono_null _ hrestricted
      rintro _ ⟨x, ⟨hxW, hxC, hxnext⟩, rfl⟩
      have hgx : g x = 0 := hgzero x (hxC.2.2 k hk le_rfl)
      obtain ⟨u, hu, hpu⟩ := hbij.surjOn ⟨hxW, hgx⟩
      refine ⟨u, ⟨hu, hcritical u hu ?_⟩, ?_⟩
      · simpa [hpu] using hxC.2.1
      · exact congrArg f hpu
    have hbase : volume (f '' C (m + 1)) = 0 := by
      have hsubset : C (m + 1) ⊆ {x | x ∈ V ∧ ∀ k, 1 ≤ k → k ≤ m + 1 →
          iteratedFDeriv ℝ k f x = 0} := by
        intro x hx
        exact ⟨hx.1, hx.2.2⟩
      exact measure_mono_null (image_mono hsubset)
        (scalarCriticalImage_null_flat_residual hV hf (n := m + 1) (by omega))
    have descending (j : ℕ) (hj : j ≤ m) : volume (f '' C (m + 1 - j)) = 0 := by
      induction j with
      | zero => simpa using hbase
      | succ j hind =>
        have hk : 1 ≤ m + 1 - (j + 1) := by omega
        have hprev := hind (by omega)
        apply measure_mono_null (image_mono (s := C (m + 1 - (j + 1)))
          (t := (C (m + 1 - (j + 1)) \ C (m + 1 - j)) ∪ C (m + 1 - j))
          (fun x hx => by
            by_cases hn : x ∈ C (m + 1 - j)
            · exact Or.inr hn
            · exact Or.inl ⟨hx, hn⟩))
        rw [image_union]
        apply measure_union_null _ hprev
        have he : m + 1 - j = (m + 1 - (j + 1)) + 1 := by omega
        rw [he]
        exact strata_null _ hk
    have hC1 : C 1 = {x | x ∈ V ∧ fderiv ℝ f x = 0} := by
      ext x
      constructor
      · exact fun hx => ⟨hx.1, hx.2.1⟩
      · intro hx
        refine ⟨hx.1, hx.2, ?_⟩
        intro j hj hj1
        have hjone : j = 1 := by omega
        subst j
        ext v
        simp [iteratedFDeriv_one_apply, hx.2]
    simpa [hC1] using descending m le_rfl

end Poincare.Analysis
