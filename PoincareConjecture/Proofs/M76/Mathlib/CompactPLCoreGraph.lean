import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLGraphBlock
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPLProduct
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M] [T2Space M]
  [LocallyCompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_locallyPL_graph_separating_compact_core
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    {A W : Set M} (hA : IsCompact A) (hW : IsOpen W) (hAW : A ⊆ W) :
    ∃ (s : Finset A) (c : s → ι) (Q : s → Set M) (F : M → (s → ℝ × E)),
      (∀ i, IsCompact (Q i)) ∧ (∀ i, Q i ⊆ (e (c i)).source ∩ W) ∧
      A ⊆ ⋃ i, interior (Q i) ∧ Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      (∀ i, EqOn (fun x => F x i) (fun x => (1, e (c i) x)) (Q i)) ∧
      ∀ x ∈ ⋃ i, Q i, ∀ y : M, F x = F y → x = y := by
  classical
  have hchoose (x : A) : ∃ (i : ι) (Q : Set M),
      IsCompact Q ∧ (x : M) ∈ interior Q ∧ Q ⊆ (e i).source ∩ W := by
    obtain ⟨i, hxi⟩ := hcover x
    obtain ⟨Q, hQ, hxQ, hQi⟩ := exists_compact_subset
      ((e i).open_source.inter hW) ⟨hxi, hAW x.property⟩
    exact ⟨i, Q, hQ, hxQ, hQi⟩
  choose i Q hQ hxQ hQi using hchoose
  obtain ⟨s, hs⟩ := hA.elim_finite_subcover (fun x : A => interior (Q x))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxQ ⟨x, hx⟩⟩)
  let c : s → ι := fun a => i a
  let Q' : s → Set M := fun a => Q a
  choose f C hC hCe hfcont hfzero hfeq hfbound hfrecover hfPL using
    fun a : s => (e (c a)).exists_compactly_supported_PL_graph_block
      (hQ a) (fun _ hx => (hQi a hx).1)
  let F : M → (s → ℝ × E) := fun x a => f a x
  refine ⟨s, c, Q', F, fun a => hQ a, fun a => hQi a, ?_,
    continuous_pi hfcont, ?_, hfeq, ?_⟩
  · intro x hx
    obtain ⟨a, has, hxQ'⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨a, has⟩, hxQ'⟩
  · intro j
    exact LocallyPiecewiseAffineOn.pi (e j).open_target
      (fun a => hfPL a (e j) (hcompat j (c a)))
  · intro x hx y hxy
    obtain ⟨a, hxa⟩ := mem_iUnion.mp hx
    have hblock : f a x = f a y := congrFun hxy a
    have hfx : f a x = (1, e (c a) x) := hfeq a hxa
    have hfy : (f a y).1 = 1 := by rw [← hblock, hfx]
    obtain ⟨hye, hycoord⟩ := hfrecover a y hfy
    apply (e (c a)).injOn (hQi a hxa).1 hye
    have hcoord := congrArg Prod.snd hblock
    simpa only [hfx, hycoord] using hcoord

end OpenPartialHomeomorph
