import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension
import PoincareConjecture.Proofs.M76.Mathlib.TriangularBipyramid
import PoincareConjecture.Proofs.M76.Mathlib.BoundaryUnionMembership










set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]







theorem IsFinitePLBallPair.union_of_disk_attachment {s u b c d q : Set X}
    (hs : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) s (b ∪ d))
    (hu : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) u (c ∪ d))
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q) (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hbd : b ∩ d = q) (hcd : c ∩ d = q) (hsu : s ∩ u = d)
    (e : d ≃ₜ disk) (he : e.IsFinitePL)
    (hq : ∀ x : d, (x : X) ∈ q ↔ (e x : (ℝ × ℝ) × ℝ) ∈ rim) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (s ∪ u) (b ∪ c) := by
  have hpos := isFinitePLBallPair_halfBall (h := 1) (Or.inl rfl)
  have hneg := isFinitePLBallPair_halfBall (h := -1) (Or.inr rfl)
  have hpi : cap 1 ∩ disk = rim := cap_inter_disk one_ne_zero
  have hni : cap (-1) ∩ disk = rim := cap_inter_disk (by norm_num)
  obtain ⟨H, hH, hHd, hHb, hHD⟩ := hs.exists_extension_of_boundary_piece hpos
    hb (isFinitePLBallPair_cap 1) hbd hpi e he hq
  obtain ⟨G, hG, hGd, hGc, _⟩ := hu.exists_extension_of_boundary_piece hneg
    hc (isFinitePLBallPair_cap (-1)) hcd hni e he hq
  have hoverlap (x : s) : (x : X) ∈ u ↔
      (H x : (ℝ × ℝ) × ℝ) ∈ halfBall (-1) := by
    have hx : (x : X) ∈ u ↔ (x : X) ∈ d := by
      rw [← hsu]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (H x : (ℝ × ℝ) × ℝ) ∈ disk ↔
        (H x : (ℝ × ℝ) × ℝ) ∈ halfBall (-1) := by
      rw [← halfBall_inter]
      simp only [mem_inter_iff, (H x).property, true_and]
    exact hx.trans ((hHD x).trans hy)
  have hagree (x : X) (hxs : x ∈ s) (hxu : x ∈ u) :
      (H ⟨x, hxs⟩ : (ℝ × ℝ) × ℝ) = G ⟨x, hxu⟩ := by
    have hxd : x ∈ d := hsu ▸ And.intro hxs hxu
    exact (congrArg (fun y : halfBall 1 => (y : (ℝ × ℝ) × ℝ)) (hHd ⟨x, hxd⟩)).trans
      (congrArg (fun y : halfBall (-1) => (y : (ℝ × ℝ) × ℝ)) (hGd ⟨x, hxd⟩)).symm
  obtain ⟨E, hE, hEH, hEG⟩ := Homeomorph.exists_union_finitePL H G hH hG hoverlap hagree
  have ht : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (halfBall 1 ∪ halfBall (-1)) (cap 1 ∪ cap (-1)) := by
    rw [← wholeBall_eq_union]
    exact isFinitePLBallPair_wholeBall
  have hbs : b ⊆ s := fun _ hx => hs.1 (Or.inl hx)
  have hcu : c ⊆ u := fun _ hx => hu.1 (Or.inl hx)
  have hP : cap 1 ⊆ halfBall 1 := fun _ hx => hpos.1 (Or.inl hx)
  have hN : cap (-1) ⊆ halfBall (-1) := fun _ hx => hneg.1 (Or.inl hx)
  apply ht.of_homeomorph (union_subset_union hbs hcu) E hE
  intro x
  rcases x.property with hxs | hxu
  · have hval : (E x : (ℝ × ℝ) × ℝ) = H ⟨x, hxs⟩ := hEH ⟨x, hxs⟩
    rw [hval]
    exact (mem_union_iff_of_intersections hcu hb.1 hsu hcd hxs).trans
      ((hHb ⟨x, hxs⟩).trans
        (mem_union_iff_of_intersections hN (isFinitePLBallPair_cap 1).1
          halfBall_inter hni (H ⟨x, hxs⟩).property).symm)
  · have hval : (E x : (ℝ × ℝ) × ℝ) = G ⟨x, hxu⟩ := hEG ⟨x, hxu⟩
    rw [hval, union_comm b c, union_comm (cap 1) (cap (-1))]
    have hus : u ∩ s = d := by rwa [inter_comm]
    have hnp : halfBall (-1) ∩ halfBall 1 = disk := by rw [inter_comm, halfBall_inter]
    exact (mem_union_iff_of_intersections hbs hc.1 hus hbd hxu).trans
      ((hGc ⟨x, hxu⟩).trans
        (mem_union_iff_of_intersections hP (isFinitePLBallPair_cap (-1)).1
          hnp hpi (G ⟨x, hxu⟩).property).symm)

end Set
