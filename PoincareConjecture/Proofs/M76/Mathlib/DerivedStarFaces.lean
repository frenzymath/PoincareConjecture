import PoincareConjecture.Proofs.M76.Mathlib.DerivedSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialStar











set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

open PoincareConjecture.Proofs.M02.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)

omit [Fintype K.faces] in
include hc in



theorem positiveFaceCenter_injective [Finite K.faces] : Function.Injective c := by
  classical
  let : Fintype K.faces := Fintype.ofFinite K.faces
  let e := geometricFlagHomeomorphRange K Subtype.val (fun s => s.property)
    (fun _ _ => Iff.rfl) c hc
  have hmem (s : K.faces) : Pi.single s (1 : ℝ) ∈ (finiteOrderComplex K.faces).space := by
    apply vertices_subset_space
    apply (finiteOrderComplex_faces K.faces _).mpr
    refine ⟨{s}, Finset.singleton_nonempty s, ?_, ?_⟩
    · intro i hi j hj
      have hi' := Finset.mem_singleton.mp hi
      have hj' := Finset.mem_singleton.mp hj
      subst i
      subst j
      exact Or.inl le_rfl
    · rw [Finset.image_singleton]
      congr 1
      funext i
      by_cases h : i = s <;> simp [h]
  have hval (s : K.faces) : (e ⟨Pi.single s (1 : ℝ), hmem s⟩ : E) = c s := by
    change (∑ i, (Pi.single s (1 : ℝ) : K.faces → ℝ) i • c i) = c s
    simp [Pi.single_apply, ite_smul]
  intro s t hst
  have heq : e ⟨Pi.single s (1 : ℝ), hmem s⟩ =
      e ⟨Pi.single t (1 : ℝ), hmem t⟩ :=
    Subtype.ext ((hval s).trans (hst.trans (hval t).symm))
  exact (Pi.linearIndependent_single_one K.faces ℝ).injective
    (congrArg Subtype.val (e.injective heq))

omit [Fintype K.faces] in
include hc in


theorem positiveFaceCenter_singleton {p : E} (hp : {p} ∈ K.faces) :
    c ⟨{p}, hp⟩ = p := by
  obtain ⟨w, _, hsum, hval⟩ := hc ⟨{p}, hp⟩
  have hw : w p = 1 := by simpa only [Finset.sum_singleton] using hsum
  simpa only [Finset.sum_singleton, hw, one_smul] using hval.symm





theorem derivedSubdivision_closedStar_faces [DecidableEq E]
    {p : E} (hp : {p} ∈ K.faces) (t : Finset E) :
    t ∈ ((K.derivedSubdivision c hc).closedStar p).faces ↔
      ∃ a : Finset K.faces, a.Nonempty ∧
        (∀ i ∈ a, ∀ j ∈ a, i ≤ j ∨ j ≤ i) ∧
        t = a.image c ∧ ∀ s ∈ a, p ∈ s.val := by
  classical
  let p₀ : K.faces := ⟨{p}, hp⟩
  have hcp : c p₀ = p := K.positiveFaceCenter_singleton c hc hp
  have hcinj := K.positiveFaceCenter_injective c hc
  constructor
  · intro ht
    obtain ⟨a, ha, hchain, hat⟩ := (K.derivedSubdivision_faces c hc t).mp ht.1
    obtain ⟨b, _, hchainb, hbt⟩ :=
      (K.derivedSubdivision_faces c hc (insert p t)).mp ht.2
    have hpb : p₀ ∈ b := by
      have hmem : c p₀ ∈ b.image c := by
        rw [hcp, ← hbt]
        exact Finset.mem_insert_self p t
      obtain ⟨j, hj, hjp⟩ := Finset.mem_image.mp hmem
      exact hcinj hjp ▸ hj
    refine ⟨a, ha, hchain, hat, ?_⟩
    intro s hs
    have hsimage : c s ∈ insert p t := by
      apply Finset.mem_insert_of_mem
      rw [hat]
      exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp (hbt ▸ hsimage)
    have hsb : s ∈ b := hcinj hjs ▸ hj
    rcases hchainb p₀ hpb s hsb with h | h
    · exact h (Finset.mem_singleton_self p)
    · obtain ⟨z, hz⟩ := K.nonempty_of_mem_faces s.property
      have hzp : z = p := Finset.mem_singleton.mp (h hz)
      exact hzp ▸ hz
  · rintro ⟨a, ha, hchain, rfl, hall⟩
    refine ⟨(K.derivedSubdivision_faces c hc _).mpr ⟨a, ha, hchain, rfl⟩, ?_⟩
    apply (K.derivedSubdivision_faces c hc _).mpr
    refine ⟨insert p₀ a, Finset.insert_nonempty _ _, ?_, ?_⟩
    · intro i hi j hj
      rcases Finset.mem_insert.mp hi with rfl | hi
      · rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inl le_rfl
        · exact Or.inl (Finset.singleton_subset_iff.mpr (hall j hj))
      · rcases Finset.mem_insert.mp hj with rfl | hj
        · exact Or.inr (Finset.singleton_subset_iff.mpr (hall i hi))
        · exact hchain i hi j hj
    · simp only [Finset.image_insert, hcp]

end Geometry.SimplicialComplex
