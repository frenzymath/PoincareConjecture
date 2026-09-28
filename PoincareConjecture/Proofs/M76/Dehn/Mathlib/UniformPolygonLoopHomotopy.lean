import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonBoundaryLoop

set_option autoImplicit false

open Set
open scoped unitInterval

namespace Path

private theorem concat_cast_vertices {X : Type*} [TopologicalSpace X] {n : ℕ}
    (a b : Fin (n + 1) → X) (h : ∀ i, a i = b i)
    (p : (i : Fin n) → Path (b i.castSucc) (b i.succ)) :
    concat a (fun i => (p i).cast (h i.castSucc) (h i.succ)) =
      (concat b p).cast (h 0) (h (Fin.last n)) := by
  have hab : a = b := funext h
  subst b
  rfl

end Path

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  (P : Polygon E (n + 3))

theorem homotopic_boundaryLoop_of_uniform
    (gamma : Path (⟨P 0, P.vertex_mem_boundary 0⟩ : P.boundary ℝ)
      ⟨P 0, P.vertex_mem_boundary 0⟩)
    (hformula : ∀ (i : Fin (n + 3)) (u s : unitInterval),
      (n + 3 : ℝ) * (s : ℝ) = (i : ℝ) + (u : ℝ) →
      (gamma s : E) = AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) (u : ℝ)) :
    gamma.Homotopic P.boundaryLoop := by
  have hden : (0 : ℝ) < n + 3 := by positivity
  let t : Fin (n + 4) → unitInterval := fun i =>
    ⟨(i : ℝ) / (n + 3 : ℝ), div_nonneg (by positivity) hden.le,
      (div_le_one hden).mpr (by exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩
  have ht0 : t 0 = 0 := Subtype.ext (by simp [t])
  have ht1 : t (Fin.last (n + 3)) = 1 := Subtype.ext (by
    simp [t, Nat.cast_add, Nat.cast_ofNat, hden.ne'])
  have hvertex (i : Fin (n + 4)) : gamma (t i) = P.closedBoundaryVertices i := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [ht1, gamma.target, P.closedBoundaryVertices_last]
    · apply Subtype.ext
      rw [P.closedBoundaryVertices_castSucc]
      have h := hformula j 0 (t j.castSucc) (by
        change (n + 3 : ℝ) * ((j : ℝ) / (n + 3 : ℝ)) = (j : ℝ) + 0
        field_simp
        simp)
      simpa only [Set.Icc.coe_zero, AffineMap.lineMap_apply_zero] using h
  have hpiece (i : Fin (n + 3)) :
      gamma.subpath (t i.castSucc) (t i.succ) =
        (P.closedBoundaryEdgePath i).cast (hvertex i.castSucc) (hvertex i.succ) := by
    apply Path.ext
    funext u
    apply Subtype.ext
    change (gamma (Icc.convexComb (t i.castSucc) (t i.succ) u) : E) =
      AffineMap.lineMap (P.closedBoundaryVertices i.castSucc : E)
        (P.closedBoundaryVertices i.succ : E) (u : ℝ)
    rw [P.closedBoundaryVertices_castSucc, P.closedBoundaryVertices_succ]
    apply hformula
    simp only [Icc.coe_convexComb, t, Fin.val_castSucc, Fin.val_succ,
      Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have hpaths :
      (fun i : Fin (n + 3) =>
        (P.closedBoundaryEdgePath i).cast (hvertex i.castSucc) (hvertex i.succ)) =
      (fun i : Fin (n + 3) => gamma.subpath (t i.castSucc) (t i.succ)) :=
    funext fun i => (hpiece i).symm
  have hjoined :
      (Path.concat (gamma ∘ t) (fun i =>
        (P.closedBoundaryEdgePath i).cast (hvertex i.castSucc) (hvertex i.succ))).Homotopic
          (gamma.subpath (t 0) (t (Fin.last (n + 3)))) := by
    rw [hpaths]
    exact Path.Homotopic.concat_subpath gamma t
  rw [Path.concat_cast_vertices] at hjoined
  have hstart : gamma (t 0) = (⟨P 0, P.vertex_mem_boundary 0⟩ : P.boundary ℝ) := by
    rw [ht0]
    exact gamma.source
  have hend : gamma (t (Fin.last (n + 3))) =
      (⟨P 0, P.vertex_mem_boundary 0⟩ : P.boundary ℝ) := by
    rw [ht1]
    exact gamma.target
  have hfinal := hjoined.pathCast hstart.symm hend.symm
  change P.boundaryLoop.Homotopic
    ((gamma.subpath (t 0) (t (Fin.last (n + 3)))).cast hstart.symm hend.symm) at hfinal
  have heq : (gamma.subpath (t 0) (t (Fin.last (n + 3)))).cast
      hstart.symm hend.symm = gamma := by
    apply Path.ext
    funext u
    change gamma (Icc.convexComb (t 0) (t (Fin.last (n + 3))) u) = gamma u
    rw [ht0, ht1]
    simp
  erw [heq] at hfinal
  exact hfinal.symm

end Polygon
