import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangleTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.PolygonTriangulationGluing
import PoincareConjecture.Proofs.M76.Mathlib.PolygonInteriorDiagonal

set_option autoImplicit false

open Set Geometry

namespace Polygon

theorem exists_triangulation {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    ∃ K : SimplicialComplex ℝ (ℝ × ℝ), P.IsTriangulation K := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact P.exists_triangle_triangulation hP hinj
    | succ N =>
      obtain ⟨a, b, hab, hba, hab', hd⟩ := P.exists_interior_diagonal hP hinj
      obtain ⟨m, n, e, hm, hn, he, ha, hb⟩ :=
        Fin.exists_cyclic_diagonal_split a b hab hba hab'
      let u : Fin (m + 2) → ℝ × ℝ := fun i => P (e (i.castAdd (n + 2)))
      let v : Fin (n + 2) → ℝ × ℝ := fun i => P (e (Fin.natAdd (m + 2) i))
      have hfun : Fin.append u v = P ∘ e := by
        funext i
        induction i using Fin.addCases <;>
          simp only [Fin.append_left, Fin.append_right] <;> rfl
      have hpoly : mk (Fin.append u v) = P.reindex e := congrArg mk hfun
      have hs : (mk (Fin.append u v)).HasSimplicialEdges := by
        rw [hpoly]
        exact P.hasSimplicialEdges_reindex hP e he
      have hi : Function.Injective (Fin.append u v) := by
        rw [hfun]
        exact hinj.comp e.injective
      have hua : u 0 = P a := congrArg P ha
      have hvb : v 0 = P b := congrArg P hb
      have hdiagonal : openSegment ℝ (u 0) (v 0) ⊆ (mk (Fin.append u v)).inside := by
        rw [hua, hvb, hpoly, P.inside_reindex e he]
        exact hd
      have hchord : segment ℝ (u 0) (v 0) ∩ (mk (Fin.append u v)).boundary ℝ ⊆
          {u 0, v 0} := by
        rintro x ⟨hx, hxb⟩
        rw [← insert_endpoints_openSegment] at hx
        rcases hx with rfl | rfl | hx
        · simp
        · simp
        · exact ((hdiagonal hx).1 hxb).elim
      obtain ⟨hsQ, hsR⟩ := hasSimplicialEdges_split u v hs hi hchord
      obtain ⟨hiQ, hiR⟩ := injective_split u v hi
      obtain ⟨C, hC⟩ := ih m (by omega) (mk (Fin.snoc u (v 0))) hsQ hiQ
      obtain ⟨D, hD⟩ := ih n (by omega) (mk (Fin.snoc v (u 0))) hsR hiR
      obtain ⟨K, hK⟩ := exists_triangulation_of_split u v hs hi hdiagonal C D hC hD
      rw [hpoly] at hK
      exact ⟨K, hK.of_reindex e he⟩

end Polygon
