import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleDiskAttachmentModel
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps
import PoincareConjecture.Proofs.M76.Mathlib.BoundaryUnionMembership










set_option autoImplicit false

open Set TriangleDiskModel

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]





theorem IsFinitePLBallPair.union_of_interval_attachment {s u b c d q : Set X}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s (b ∪ d))
    (hu : IsFinitePLBallPair (ℝ × ℝ) u (c ∪ d))
    (hb : IsFinitePLBallPair ℝ b q) (hc : IsFinitePLBallPair ℝ c q)
    (hd : IsFinitePLBallPair ℝ d q)
    (hbd : b ∩ d = q) (hcd : c ∩ d = q) (hsu : s ∩ u = d) :
    IsFinitePLBallPair (ℝ × ℝ) (s ∪ u) (b ∪ c) := by
  obtain ⟨B, C, hR, hL, hB, hC, hBI, hCI, htarget⟩ := exists_disk_attachment_model
  obtain ⟨e, he, heq⟩ := hd.exists_homeomorph isFinitePLBallPair_common_edge
  obtain ⟨H, hH, hHd, hHb, hHD⟩ := hs.exists_extension_of_boundary_piece hR
    hb hB hbd hBI e he heq
  obtain ⟨G, hG, hGd, hGc, _⟩ := hu.exists_extension_of_boundary_piece hL
    hc hC hcd hCI e he heq
  have hoverlap (x : s) : (x : X) ∈ u ↔
      (H x : ℝ × ℝ) ∈ convexHull ℝ (range leftTriangle) := by
    have hx : (x : X) ∈ u ↔ (x : X) ∈ d := by
      rw [← hsu]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (H x : ℝ × ℝ) ∈ segment ℝ (0, 1) (0, 0) ↔
        (H x : ℝ × ℝ) ∈ convexHull ℝ (range leftTriangle) := by
      rw [← region_inter]
      simp only [mem_inter_iff, (H x).property, true_and]
    exact hx.trans ((hHD x).trans hy)
  have hagree (x : X) (hxs : x ∈ s) (hxu : x ∈ u) :
      (H ⟨x, hxs⟩ : ℝ × ℝ) = G ⟨x, hxu⟩ := by
    have hxd : x ∈ d := hsu ▸ And.intro hxs hxu
    exact (congrArg (fun y : convexHull ℝ (range rightTriangle) => (y : ℝ × ℝ))
      (hHd ⟨x, hxd⟩)).trans
      (congrArg (fun y : convexHull ℝ (range leftTriangle) => (y : ℝ × ℝ))
        (hGd ⟨x, hxd⟩)).symm
  obtain ⟨E, hE, hEH, hEG⟩ := Homeomorph.exists_union_finitePL H G hH hG hoverlap hagree
  have hbs : b ⊆ s := fun _ hx => hs.1 (Or.inl hx)
  have hcu : c ⊆ u := fun _ hx => hu.1 (Or.inl hx)
  have hBR : B ⊆ convexHull ℝ (range rightTriangle) := fun _ hx => hR.1 (Or.inl hx)
  have hCL : C ⊆ convexHull ℝ (range leftTriangle) := fun _ hx => hL.1 (Or.inl hx)
  apply htarget.of_homeomorph (union_subset_union hbs hcu) E hE
  intro x
  rcases x.property with hxs | hxu
  · have hval : (E x : ℝ × ℝ) = H ⟨x, hxs⟩ := hEH ⟨x, hxs⟩
    rw [hval]
    exact (mem_union_iff_of_intersections hcu hb.1 hsu hcd hxs).trans
      ((hHb ⟨x, hxs⟩).trans
        (mem_union_iff_of_intersections hCL hB.1 region_inter hCI
          (H ⟨x, hxs⟩).property).symm)
  · have hval : (E x : ℝ × ℝ) = G ⟨x, hxu⟩ := hEG ⟨x, hxu⟩
    rw [hval, union_comm b c, union_comm B C]
    have hus : u ∩ s = d := by rwa [inter_comm]
    have hLR : convexHull ℝ (range leftTriangle) ∩ convexHull ℝ (range rightTriangle) =
        segment ℝ (0, 1) (0, 0) := by rw [inter_comm, region_inter]
    exact (mem_union_iff_of_intersections hbs hc.1 hus hbd hxu).trans
      ((hGc ⟨x, hxu⟩).trans
        (mem_union_iff_of_intersections hBR hC.1 hLR hBI (G ⟨x, hxu⟩).property).symm)





theorem IsFinitePLBallPair.union_of_boundary_interval {s u b c d : Set X} {a z : X}
    (hs : IsFinitePLBallPair (ℝ × ℝ) s b)
    (hu : IsFinitePLBallPair (ℝ × ℝ) u c)
    (hd : IsFinitePLBallPair ℝ d {a, z}) (hdb : d ⊆ b) (hdc : d ⊆ c)
    (haz : a ≠ z) (hsu : s ∩ u = d) :
    IsFinitePLBallPair (ℝ × ℝ) (s ∪ u) ((b ∪ c) \ (d \ {a, z})) := by
  obtain ⟨b', hb', hdb', hiDb⟩ := hs.exists_boundary_arc_complement hd hdb haz
  obtain ⟨c', hc', hdc', hiDc⟩ := hu.exists_boundary_arc_complement hd hdc haz
  have hs' : IsFinitePLBallPair (ℝ × ℝ) s (b' ∪ d) := by rwa [union_comm, hdb']
  have hu' : IsFinitePLBallPair (ℝ × ℝ) u (c' ∪ d) := by rwa [union_comm, hdc']
  have hb'd : b' ∩ d = {a, z} := by rwa [inter_comm]
  have hc'd : c' ∩ d = {a, z} := by rwa [inter_comm]
  have hboundary : (b ∪ c) \ (d \ {a, z}) = b' ∪ c' := by
    ext x
    have hendsb : x ∈ ({a, z} : Set X) → x ∈ b' := fun hx => hb'.1 hx
    have hendsc : x ∈ ({a, z} : Set X) → x ∈ c' := fun hx => hc'.1 hx
    have hmeetb : x ∈ d → x ∈ b' → x ∈ ({a, z} : Set X) :=
      fun hx hb => hiDb.subset ⟨hx, hb⟩
    have hmeetc : x ∈ d → x ∈ c' → x ∈ ({a, z} : Set X) :=
      fun hx hc => hiDc.subset ⟨hx, hc⟩
    rw [← hdb', ← hdc']
    simp only [mem_sdiff, mem_union]
    tauto
  rw [hboundary]
  exact hs'.union_of_interval_attachment hu' hb' hc' hd hb'd hc'd hsu

end Set
