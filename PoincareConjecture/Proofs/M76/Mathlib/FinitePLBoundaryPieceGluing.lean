import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections

set_option autoImplicit false

open Set Geometry

namespace Set

variable {V X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

theorem IsFinitePLBallPair.exists_union_homeomorph_of_boundary_piece
    {b d q : Set X} {B D Q : Set Y}
    (hb : IsFinitePLBallPair V b q) (hB : IsFinitePLBallPair V B Q)
    (hinter : b ∩ d = q) (hInter : B ∩ D = Q)
    (e : d ≃ₜ D) (he : e.IsFinitePL)
    (hmem : ∀ x : d, (x : X) ∈ q ↔ (e x : Y) ∈ Q) :
    ∃ H : (b ∪ d : Set X) ≃ₜ (B ∪ D : Set Y), H.IsFinitePL ∧
      (∀ x : d, H ⟨x, Or.inr x.property⟩ = ⟨e x, Or.inr (e x).property⟩) ∧
      (∀ x : (b ∪ d : Set X), (x : X) ∈ b ↔ (H x : Y) ∈ B) ∧
      (∀ x : (b ∪ d : Set X), (x : X) ∈ d ↔ (H x : Y) ∈ D) := by
  have hbcopy := hb
  have hecopy := he
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKb, _⟩, _⟩, _⟩ := hbcopy
  obtain ⟨_, ⟨J, hJ, hJd, _⟩, _⟩ := hecopy
  obtain ⟨L, hL, hLq⟩ := K.exists_finite_triangulation_inter J hK hJ
  rw [hKb, hJd, hinter] at hLq
  have hqd : q ⊆ d := by rw [← hinter]; exact inter_subset_right
  have hQD : Q ⊆ D := by rw [← hInter]; exact inter_subset_right
  let eq := e.restrictSubsets hqd hQD hmem
  have heq : eq.IsFinitePL := he.restrictSubsets hqd hQD hmem L hL hLq
  obtain ⟨eb, heb, hebq, hebmem⟩ := hb.exists_extension hB eq heq
  have hoverlap (x : b) : (x : X) ∈ d ↔ (eb x : Y) ∈ D := by
    have hx : (x : X) ∈ d ↔ (x : X) ∈ q := by
      rw [← hinter]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (eb x : Y) ∈ Q ↔ (eb x : Y) ∈ D := by
      rw [← hInter]
      simp only [mem_inter_iff, (eb x).property, true_and]
    exact hx.trans ((hebmem x).trans hy)
  have hagree (x : X) (hxb : x ∈ b) (hxd : x ∈ d) :
      (eb ⟨x, hxb⟩ : Y) = e ⟨x, hxd⟩ := by
    have hxq : x ∈ q := hinter ▸ And.intro hxb hxd
    exact congrArg (fun y : B => (y : Y)) (hebq ⟨x, hxq⟩)
  obtain ⟨H, hH, hHb, hHd⟩ := Homeomorph.exists_union_finitePL eb e heb he hoverlap hagree
  have hkeep (x : d) : H ⟨x, Or.inr x.property⟩ =
      ⟨e x, Or.inr (e x).property⟩ := Subtype.ext (hHd x)
  exact ⟨H, hH, hkeep,
    H.mem_subset_iff_of_extension eb subset_union_left subset_union_left
      (fun x => Subtype.ext (hHb x)),
    H.mem_subset_iff_of_extension e subset_union_right subset_union_right hkeep⟩

end Set
