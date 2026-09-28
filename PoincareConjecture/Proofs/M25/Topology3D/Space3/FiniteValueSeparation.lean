import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false

open Set Filter
open scoped Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]

theorem exists_ne_of_regular_difference (f g : M → ℝ) {W V : Set M}
    (hV : IsOpen V) (hVne : V.Nonempty) (hVW : V ⊆ W)
    (hregular : ∀ x ∈ W, f x = g x →
      mfderiv I 𝓘(ℝ, ℝ) (fun y => f y - g y) x ≠ 0) :
    ∃ x ∈ V, f x ≠ g x := by
  by_contra h
  have heq : ∀ x ∈ V, f x = g x := by
    intro x hx
    by_contra hne
    exact h ⟨x, hx, hne⟩
  obtain ⟨x, hx⟩ := hVne
  have hevent : (fun y => f y - g y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hV.mem_nhds hx] with y hy
    exact sub_eq_zero.mpr (heq y hy)
  apply hregular x (hVW hx) (heq x hx)
  rw [hevent.mfderiv_eq, mfderiv_const]
  rfl

theorem exists_injective_values_of_regular_differences {ι : Type*} [Finite ι]
    (f : ι → M → ℝ) {W : Set M} (hW : IsOpen W) (hWne : W.Nonempty)
    (hf : ∀ i, ContinuousOn (f i) W)
    (hregular : ∀ i j, i ≠ j → ∀ x ∈ W, f i x = f j x →
      mfderiv I 𝓘(ℝ, ℝ) (fun y => f i y - f j y) x ≠ 0) :
    ∃ x ∈ W, Function.Injective (fun i => f i x) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hopen (i j : ι) : IsOpen (W ∩ {x | f i x ≠ f j x}) :=
    ((hf i).prodMk (hf j)).isOpen_inter_preimage hW
      (isClosed_eq continuous_fst continuous_snd).isOpen_compl
  have haux (s : Finset (ι × ι)) :
      ∃ V : Set M, IsOpen V ∧ V.Nonempty ∧ V ⊆ W ∧
        ∀ p ∈ s, p.1 ≠ p.2 → ∀ x ∈ V, f p.1 x ≠ f p.2 x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨W, hW, hWne, Subset.rfl, by simp⟩
    | @insert p s _ ih =>
      obtain ⟨V, hV, hVne, hVW, hsep⟩ := ih
      by_cases hp : p.1 = p.2
      · refine ⟨V, hV, hVne, hVW, ?_⟩
        intro q hq hqne x hx
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact (hqne hp).elim
        · exact hsep q hq hqne x hx
      · obtain ⟨x, hx, hneq⟩ := exists_ne_of_regular_difference I (f p.1) (f p.2)
          hV hVne hVW (hregular p.1 p.2 hp)
        refine ⟨V ∩ (W ∩ {y | f p.1 y ≠ f p.2 y}), hV.inter (hopen p.1 p.2),
          ⟨x, hx, hVW hx, hneq⟩, fun _ hy => hy.2.1, ?_⟩
        intro q hq hqne y hy
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hy.2.2
        · exact hsep q hq hqne y hy.1
  obtain ⟨V, _, ⟨x, hx⟩, hVW, hsep⟩ := haux Finset.univ
  refine ⟨x, hVW hx, ?_⟩
  intro i j hij
  by_contra hne
  exact hsep (i, j) (Finset.mem_univ _) hne x hx hij

end PoincareConjecture.M25.Topology3D
