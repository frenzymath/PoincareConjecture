import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GraphWalkConcatenation










set_option autoImplicit false

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

private theorem length_concatSequence_single {n : ℕ} (p : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (p i.castSucc) (p i.succ)) :
    (concatSequence p (fun i => Walk.cons (h i) .nil)).length = n := by
  induction n with
  | zero => rw [concatSequence_zero, length_nil]
  | succ n ih =>
    erw [concatSequence_succ, length_append, ih, length_cons, length_nil]

private theorem getVert_concatSequence_single {n : ℕ} (p : Fin (n + 1) → V)
    (h : ∀ i : Fin n, G.Adj (p i.castSucc) (p i.succ)) (i : Fin (n + 1)) :
    (concatSequence p (fun i => Walk.cons (h i) .nil)).getVert i.val = p i := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by have hlt := i.isLt; omega)
    subst i
    rw [concatSequence_zero]
    rfl
  | succ n ih =>
    erw [concatSequence_succ, getVert_append', length_concatSequence_single]
    by_cases hi : i.val ≤ n
    · rw [if_pos hi]
      exact ih (p ∘ Fin.castSucc) (fun j => h j.castSucc) ⟨i.val, by omega⟩
    · rw [if_neg hi]
      have hval : i.val = n + 1 := by omega
      have hlast : i = Fin.last (n + 1) := Fin.ext hval
      subst i
      simp only [Fin.val_last]
      rw [show n + 1 - n = 1 from by omega]
      rfl




theorem concatSequence_original_edges {u v : V} (w : G.Walk u v) :
    concatSequence (fun i : Fin (w.length + 1) => w.getVert i.val)
      (fun i : Fin w.length => Walk.cons (w.adj_getVert_succ i.isLt) .nil) =
        w.copy w.getVert_zero.symm w.getVert_length.symm := by
  apply ext_getVert_le_length
  · erw [length_concatSequence_single, length_copy]
  · intro k hk
    rw [length_concatSequence_single] at hk
    erw [getVert_copy]
    exact getVert_concatSequence_single _ _ ⟨k, by omega⟩

private theorem realizePath_copy_endpoints {X : Type*} [TopologicalSpace X]
    (a : V → X) (edge : ∀ {u v : V}, G.Adj u v → _root_.Path (a u) (a v))
    {u v u' v' : V} (w : G.Walk u v) (hu : u = u') (hv : v = v') :
    realizePath a edge (w.copy hu hv) =
      (realizePath a edge w).cast (congrArg a hu.symm) (congrArg a hv.symm) := by
  subst u'
  subst v'
  rfl




theorem realizePath_homotopic_original_edges {X : Type*} [TopologicalSpace X]
    (a : V → X) (edge : ∀ {u v : V}, G.Adj u v → _root_.Path (a u) (a v))
    {u v : V} (w : G.Walk u v) :
    ((realizePath a edge w).cast (congrArg a w.getVert_zero)
      (congrArg a w.getVert_length)).Homotopic
        (_root_.Path.concat (fun i : Fin (w.length + 1) => a (w.getVert i.val))
          (fun i : Fin w.length => edge (w.adj_getVert_succ i.isLt))) := by
  let p : Fin (w.length + 1) → V := fun i => w.getVert i.val
  let h (i : Fin w.length) := w.adj_getVert_succ i.isLt
  have hreal := Path.Homotopic.Quotient.eq.mp
    (realizePath_concatSequence a edge p (fun i => Walk.cons (h i) .nil))
  erw [concatSequence_original_edges, realizePath_copy_endpoints] at hreal
  exact hreal.trans (Path.Homotopic.concat_hcomp (a ∘ p)
    (fun i => realizePath a edge (Walk.cons (h i) .nil)) (fun i => edge (h i))
    (fun i => Path.Homotopic.trans_refl (edge (h i))))

end SimpleGraph.Walk
