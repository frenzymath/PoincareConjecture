import PoincareConjecture.Proofs.M76.Mathlib.CyclicDiagonalIndices
import PoincareConjecture.Proofs.M76.Mathlib.PolygonReindex
import Mathlib.Data.Fin.Tuple.Basic









set_option autoImplicit false

open Set

namespace Polygon



theorem range_split_subset {E : Type*} {m n : ℕ}
    (u : Fin (m + 1) → E) (v : Fin (n + 1) → E) :
    range (Fin.snoc u (v 0) : Fin ((m + 1) + 1) → E) ⊆ range (Fin.append u v) ∧
      range (Fin.snoc v (u 0) : Fin ((n + 1) + 1) → E) ⊆ range (Fin.append u v) := by
  have hu : range u ⊆ range (Fin.append u v) := by
    rintro x ⟨i, rfl⟩
    exact ⟨i.castAdd (n + 1), Fin.append_left u v i⟩
  have hv : range v ⊆ range (Fin.append u v) := by
    rintro x ⟨i, rfl⟩
    exact ⟨Fin.natAdd (m + 1) i, Fin.append_right u v i⟩
  rw [Fin.range_snoc, Fin.range_snoc]
  exact ⟨insert_subset (hv (mem_range_self 0)) hu,
    insert_subset (hu (mem_range_self 0)) hv⟩




theorem exists_strings_at_diagonal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (P : Polygon E (N + 4)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (a b : Fin (N + 4))
    (hab : a ≠ b) (hba : b ≠ finRotate (N + 4) a)
    (hab' : a ≠ finRotate (N + 4) b) :
    ∃ (m n : ℕ) (u : Fin (m + 2) → E) (v : Fin (n + 2) → E),
      m + 3 < N + 4 ∧ n + 3 < N + 4 ∧
      Function.Injective (Fin.append u v) ∧ (mk (Fin.append u v)).HasSimplicialEdges ∧
      (mk (Fin.append u v)).boundary ℝ = P.boundary ℝ ∧
      (mk (Fin.append u v)).inside = P.inside ∧
      range (Fin.append u v) = range P ∧ u 0 = P a ∧ v 0 = P b := by
  obtain ⟨m, n, e, hm, hn, he, ha, hb⟩ := Fin.exists_cyclic_diagonal_split a b hab hba hab'
  let u : Fin (m + 2) → E := fun i => P (e (i.castAdd (n + 2)))
  let v : Fin (n + 2) → E := fun i => P (e (Fin.natAdd (m + 2) i))
  have hfun : Fin.append u v = P ∘ e := by
    funext i
    induction i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right] <;> rfl
  have hpoly : mk (Fin.append u v) = P.reindex e := congrArg mk hfun
  refine ⟨m, n, u, v, hm, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfun]
    exact hinj.comp e.injective
  · rw [hpoly]
    exact P.hasSimplicialEdges_reindex hP e he
  · rw [hpoly]
    exact P.boundary_reindex e he
  · rw [hpoly]
    exact P.inside_reindex e he
  · rw [hfun]
    exact e.surjective.range_comp P
  · exact congrArg P ha
  · exact congrArg P hb

end Polygon
