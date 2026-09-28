import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneShellBoundary
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneDomainCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPreimages











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "W" => (ℝ × (ℝ × ℝ))
local notation "V3" => (Fin 3 → ℝ)

private theorem plDomain_of_shell_frontier {R : Set V3}
    (hR : IsClosed R) (hreg : closure (interior R) = R)
    (e : frontier R ≃ₜ frontier squareShell) (he : e.IsFinitePL) :
    PLDomain (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) R := by
  have htri := he
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := htri
  have hlocal (x : frontier R) : ∃ d q : Set V3,
      IsFinitePLBallPair (ℝ × ℝ) d q ∧ d ⊆ frontier R ∧ (x : V3) ∈ d \ q ∧
        IsOpen ((Subtype.val : frontier R → V3) ⁻¹' (d \ q)) := by
    obtain ⟨D, Q, hD, hDS, hxDQ, hopen⟩ :=
      exists_square_shell_frontier_disk_patch (e x).property
    have hcopy := he
    obtain ⟨f, _, hf⟩ := hcopy
    let d := frontier R ∩ f ⁻¹' D
    let q := frontier R ∩ f ⁻¹' Q
    have hd : IsFinitePLBallPair (ℝ × ℝ) d q := he.preimage_ballPair hD hDS hf
    have hx : (x : V3) ∈ d \ q := by
      refine ⟨⟨x.property, ?_⟩, ?_⟩
      · change f x ∈ D
        rw [← hf]
        exact hxDQ.1
      · intro hxq
        apply hxDQ.2
        rw [hf x]
        exact hxq.2
    refine ⟨d, q, hd, inter_subset_left, hx, ?_⟩
    have heq : (Subtype.val : frontier R → V3) ⁻¹' (d \ q) =
        e ⁻¹' ((Subtype.val : frontier squareShell → W) ⁻¹' (D \ Q)) := by
      ext y
      change (((y : V3) ∈ frontier R ∧ f y ∈ D) ∧
        ¬ ((y : V3) ∈ frontier R ∧ f y ∈ Q)) ↔
        ((e y : W) ∈ D ∧ (e y : W) ∉ Q)
      simp only [y.property, true_and, hf]
    rw [heq]
    exact hopen.preimage e.continuous
  apply plDomain_of_regular_closed_local_ball_pairs hR hreg K hK hKs
  rw [hKs]
  exact hlocal







theorem plDomain_affineImage_complementaryRegion
    (a : W ≃ᴬ[ℝ] V3) {B T : Set W}
    (hB : IsClosed B) (hBreg : closure (interior B) = B) (hBL : B ⊆ squareBlock)
    (hT : IsClosed T) (hfront : frontier B = T ∪ squareAttachingDisks)
    (hcontact : B ∩ frontier squareBlock = squareAttachingDisks)
    (hrims : T ∩ frontier squareBlock = squareRims)
    (tau : squareInnerAnnulus ≃ₜ T) (htau : tau.IsFinitePL)
    (hfix : ∀ x : squareInnerAnnulus, (x : W) ∈ squareRims → (tau x : W) = x) :
    IsCompact (a '' complementaryRegion B) ∧
      PLDomain (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph)
        (a '' complementaryRegion B) := by
  obtain ⟨hEcpt, hEreg, hEfront⟩ :=
    complementaryRegion_geometry hB hBreg hBL hT hfront hcontact hrims
  obtain ⟨e, he, _, _⟩ := exists_marked_shell_frontier_map tau htau hrims hfix
  let ea := a.toHomeomorph.image (T ∪ squareOuterAnnulus)
  have hea : ea.IsFinitePL := by
    obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := he.symm
    exact ⟨a, ⟨K, hK, hKs, K.affineOnFaces_affine a.toContinuousAffineMap⟩,
      fun _ => rfl⟩
  have himage : a '' (T ∪ squareOuterAnnulus) = frontier (a '' complementaryRegion B) := by
    rw [← hEfront]
    exact a.toHomeomorph.image_frontier _
  let H := (e.trans ea).trans (Homeomorph.setCongr himage)
  have hH : H.IsFinitePL := by
    obtain ⟨f, hf, hfeq⟩ := he.trans hea
    exact ⟨f, hf, hfeq⟩
  have hRcpt : IsCompact (a '' complementaryRegion B) := hEcpt.image a.continuous
  refine ⟨hRcpt, plDomain_of_shell_frontier hRcpt.isClosed ?_ H.symm hH.symm⟩
  change closure (interior (a.toHomeomorph '' complementaryRegion B)) =
    a.toHomeomorph '' complementaryRegion B
  rw [← a.toHomeomorph.image_interior, ← a.toHomeomorph.image_closure, hEreg]

end PoincareConjecture.M76.HamiltonIndexOne
