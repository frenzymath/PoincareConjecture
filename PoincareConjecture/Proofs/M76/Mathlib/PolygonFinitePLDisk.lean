import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLDiskGluing
import PoincareConjecture.Proofs.M76.Mathlib.PolygonDiagonalStrings











set_option autoImplicit false

open Set

namespace Polygon




theorem isFinitePLBallPair_closed_inside {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P) :
    IsFinitePLBallPair (ℝ × ℝ) (closure P.inside) (P.boundary ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact P.isFinitePLBallPair_triangle hP hinj
    | succ N =>
      obtain ⟨a, b, hab, hba, hab', hd⟩ := P.exists_interior_diagonal hP hinj
      obtain ⟨m, n, u, v, hm, hn, hi, hs, hboundary, hins, _, hua, hvb⟩ :=
        P.exists_strings_at_diagonal hP hinj a b hab hba hab'
      have hdiagonal : openSegment ℝ (u 0) (v 0) ⊆ (mk (Fin.append u v)).inside := by
        rw [hua, hvb, hins]
        exact hd
      have hchord : segment ℝ (u 0) (v 0) ∩ (mk (Fin.append u v)).boundary ℝ ⊆ {u 0, v 0} := by
        rintro x ⟨hx, hxb⟩
        rw [← insert_endpoints_openSegment] at hx
        rcases hx with rfl | rfl | hx
        · simp
        · simp
        · exact ((hdiagonal hx).1 hxb).elim
      obtain ⟨hsQ, hsR⟩ := hasSimplicialEdges_split u v hs hi hchord
      obtain ⟨hiQ, hiR⟩ := injective_split u v hi
      have hQ := ih m (by omega) (mk (Fin.snoc u (v 0))) hsQ hiQ
      have hR := ih n (by omega) (mk (Fin.snoc v (u 0))) hsR hiR
      simpa only [hins, hboundary] using isFinitePLBallPair_of_split u v hs hi hdiagonal hQ hR





theorem exists_finitePL_closed_inside_extension {m n : ℕ}
    (P : Polygon (ℝ × ℝ) (m + 3)) (Q : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinjP : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hinjQ : Function.Injective Q)
    (eb : P.boundary ℝ ≃ₜ Q.boundary ℝ) (heb : eb.IsFinitePL) :
    ∃ e : closure P.inside ≃ₜ closure Q.inside, e.IsFinitePL ∧
      (∀ (x : P.boundary ℝ) (hx : (x : ℝ × ℝ) ∈ closure P.inside),
        (e ⟨x, hx⟩ : ℝ × ℝ) = eb x) ∧
      (∀ x : closure P.inside, (x : ℝ × ℝ) ∈ P.boundary ℝ ↔
        (e x : ℝ × ℝ) ∈ Q.boundary ℝ) := by
  obtain ⟨e, hePL, he, hi⟩ := (P.isFinitePLBallPair_closed_inside hP hinjP).exists_extension
    (Q.isFinitePLBallPair_closed_inside hQ hinjQ) eb heb
  exact ⟨e, hePL, fun x _ => congrArg (fun z : closure Q.inside => (z : ℝ × ℝ)) (he x), hi⟩

end Polygon
