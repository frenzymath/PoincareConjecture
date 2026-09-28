import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedBallBoundaryPush
import PoincareConjecture.Proofs.M76.Triangulation.PLBallBoundaryDiskComplement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension










set_option autoImplicit false

open Set Geometry

namespace Set

variable {V X Y : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]





theorem IsFinitePLBallPair.exists_inward_extension_of_boundary_disk
    {s b d c : Set X} {C S G q : Set Y}
    (hs : IsFinitePLBallPair V s (b ∪ d)) (hC : IsFinitePLBallPair V C S)
    (hdim : Module.finrank ℝ V = 3) (hb : IsFinitePLBallPair (ℝ × ℝ) b c)
    (hG : IsFinitePLBallPair (ℝ × ℝ) G q) (hGS : G ⊆ S) (hout : (S \ G).Nonempty)
    (hinter : b ∩ d = c) (e : d ≃ₜ G) (he : e.IsFinitePL)
    (hmem : ∀ x : d, (x : X) ∈ c ↔ (e x : Y) ∈ q) :
    ∃ F : X → Y, FinitePiecewiseAffineOn F s ∧ InjOn F s ∧ MapsTo F s C ∧
      (∀ x : d, F x = e x) ∧ ∀ x ∈ s, F x ∈ S ↔ x ∈ d := by
  let B := S \ (G \ q)
  have hB : IsFinitePLBallPair (ℝ × ℝ) B q :=
    hC.boundary_disk_complement hdim hG hGS hout
  have hBC : B ⊆ C := sdiff_subset.trans hC.1
  have hGC : G ⊆ C := hGS.trans hC.1
  have hBG : B ∩ G = q := by
    ext x
    change ((x ∈ S ∧ ¬ (x ∈ G ∧ x ∉ q)) ∧ x ∈ G) ↔ x ∈ q
    constructor
    · rintro ⟨⟨_, hn⟩, hxG⟩
      exact by_contra fun hnq => hn ⟨hxG, hnq⟩
    · intro hxq
      exact ⟨⟨hGS (hG.1 hxq), fun h => h.2 hxq⟩, hG.1 hxq⟩
  have hcover : B ∪ G = S := by
    apply Subset.antisymm (union_subset sdiff_subset hGS)
    intro x hx
    by_cases hxG : x ∈ G
    · exact Or.inr hxG
    · exact Or.inl ⟨hx, fun h => hxG h.1⟩
  have hGcopy := hG
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJG, _⟩, _⟩, _⟩ := hGcopy
  obtain ⟨p, hp, hpi, hpm, hpfix, hpb⟩ :=
    hC.exists_push_fixing_boundary_polyhedron hdim J hJ (hJG.subset.trans hGS)
  have hpG : EqOn p id G := fun x hx => hpfix (hJG.symm ▸ hx)
  have himage (A : Set Y) (hAG : A ⊆ G) : p '' A = A := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      simpa only [hpG (hAG hx), id_eq] using hx
    · intro x hx
      exact ⟨x, hx, hpG (hAG hx)⟩
  have hpGimage : p '' G = G := himage G Subset.rfl
  have hpqimage : p '' q = q := himage q hG.1
  have hnewC : IsFinitePLBallPair V (p '' C) ((p '' B) ∪ G) := by
    have h := hC.image hp hpi
    have hboundary : p '' S = (p '' B) ∪ G := by
      rw [← hcover, image_union, hpGimage]
    rwa [hboundary] at h
  have hnewB : IsFinitePLBallPair (ℝ × ℝ) (p '' B) q := by
    simpa only [hpqimage] using hB.image_of_subset hp hBC hpi
  have hnewBG : (p '' B) ∩ G = q := by
    calc
      (p '' B) ∩ G = (p '' B) ∩ (p '' G) := by rw [hpGimage]
      _ = p '' (B ∩ G) := (hpi.image_inter hBC hGC).symm
      _ = q := by rw [hBG, hpqimage]
  obtain ⟨H, hH, hHe, _, hHd⟩ :=
    hs.exists_extension_of_boundary_piece hnewC hb hnewB hinter hnewBG e he hmem
  have hHcopy := hH
  obtain ⟨F, hF, hHF⟩ := hHcopy
  have hFinj : InjOn F s := by
    intro x hx y hy hxy
    have hHeq : H ⟨x, hx⟩ = H ⟨y, hy⟩ :=
      Subtype.ext ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective hHeq)
  have hFimage (x : X) (hx : x ∈ s) : F x ∈ p '' C := by
    rw [← hHF ⟨x, hx⟩]
    exact (H ⟨x, hx⟩).property
  have hcontact (y : Y) (hy : y ∈ p '' C) : y ∈ S ↔ y ∈ G := by
    obtain ⟨x, hx, rfl⟩ := hy
    constructor
    · intro hpS
      have hxG : x ∈ G := hJG ▸ (hpb x hx).mp hpS
      simpa only [hpG hxG, id_eq] using hxG
    · exact fun h => hGS h
  refine ⟨F, hF, hFinj, fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨y, hy, heq⟩ := hFimage x hx
    exact heq ▸ hpm hy
  · intro x
    have hv := congrArg (fun y : p '' C => (y : Y)) (hHe x)
    rw [hHF] at hv
    exact hv
  · intro x hx
    have hd := hHd ⟨x, hx⟩
    rw [hHF] at hd
    exact (hcontact _ (hFimage x hx)).trans hd.symm

end Set
