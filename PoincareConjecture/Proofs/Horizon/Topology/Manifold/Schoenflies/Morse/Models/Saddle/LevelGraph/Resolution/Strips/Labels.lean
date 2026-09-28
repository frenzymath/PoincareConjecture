import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Resolution.Strips.Coordinates

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)

def stripEndpoint (a b : Fin 2 → Real) (k : Fin 2 × Fin 2) : Real :=
  if k.2 = 0 then a k.1 else b k.1

@[simp] theorem stripEndpoint_left (a b : Fin 2 → Real) (i : Fin 2) :
    stripEndpoint a b (i, 0) = a i := rfl

@[simp] theorem stripEndpoint_right (a b : Fin 2 → Real) (i : Fin 2) :
    stripEndpoint a b (i, 1) = b i := rfl

theorem exists_strip_contact_labels {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph E2 M) (r : Real)
    (F : Fin 2 → OpenPartialHomeomorph (Real × Real) M)
    (a b : Fin 2 → Real) (hab : ∀ i, a i < b i)
    (hsource : ∀ i, Icc (a i) (b i) ×ˢ ({0} : Set Real) ⊆ (F i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i).target (F j).target))
    (hends : ∀ i, range (fun j : Fin 2 × Fin 2 => e (contact r j)) ∩
      (F i '' (Icc (a i) (b i) ×ˢ ({0} : Set Real))) =
        {F i (a i, 0), F i (b i, 0)}) :
    ∃ L : (Fin 2 × Fin 2) ≃ (Fin 2 × Fin 2),
      ∀ k, F k.1 (stripEndpoint a b k, 0) = e (contact r (L k)) := by
  classical
  have hep (k : Fin 2 × Fin 2) : stripEndpoint a b k ∈ Icc (a k.1) (b k.1) := by
    unfold stripEndpoint
    split_ifs <;> exact ⟨by linarith [hab k.1], by linarith [hab k.1]⟩
  have hmem (k : Fin 2 × Fin 2) :
      F k.1 (stripEndpoint a b k, 0) ∈ range (fun j => e (contact r j)) := by
    have hx : F k.1 (stripEndpoint a b k, 0) ∈
        ({F k.1 (a k.1, 0), F k.1 (b k.1, 0)} : Set M) := by
      unfold stripEndpoint
      split_ifs <;> simp
    exact ((hends k.1).superset hx).1
  choose L hL using hmem
  have hLi : Function.Injective L := by
    intro k l hkl
    have heq : F k.1 (stripEndpoint a b k, 0) = F l.1 (stripEndpoint a b l, 0) :=
      (hL k).symm.trans ((congrArg (fun j => e (contact r j)) hkl).trans (hL l))
    have hks : (stripEndpoint a b k, 0) ∈ (F k.1).source :=
      hsource k.1 ⟨hep k, rfl⟩
    have hls : (stripEndpoint a b l, 0) ∈ (F l.1).source :=
      hsource l.1 ⟨hep l, rfl⟩
    have hfirst : k.1 = l.1 := by
      by_contra hn
      exact disjoint_left.mp (hdisjoint hn) ((F k.1).map_source hks)
        (heq ▸ (F l.1).map_source hls)
    rcases k with ⟨i, j⟩
    rcases l with ⟨i', j'⟩
    dsimp only at hfirst
    subst i'
    have hparam := congrArg Prod.fst ((F i).injOn hks hls heq)
    have hsecond : j = j' := by
      have hi := hab i
      fin_cases j <;> fin_cases j' <;>
        norm_num [stripEndpoint] at hparam ⊢ <;>
        first | rfl | (exfalso; linarith)
    exact Prod.ext rfl hsecond
  refine ⟨Equiv.ofBijective L ((Fintype.bijective_iff_injective_and_card L).mpr ⟨hLi, rfl⟩), ?_⟩
  intro k
  exact (hL k).symm

end Poincare.Manifold.Schoenflies.SaddleLevel
