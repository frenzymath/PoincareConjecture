import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallNormalization
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBoundaryPieceGluing
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Regions.PLBallAttachment

/-!
# Standard sphere and ball models for disk surgery

Two disks joined exactly at their common boundary have a finite
PL sphere model. Three-ball attachment needs only a certificate
for its shared PL disk. See Alexander 1924, p. 7, Hamilton 1976,
p. 66 and M76 derivation 133.
-/

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- Two finite PL disks meeting exactly in their common
boundary form a finite PL sphere, modeled on the whole frontier
of the standard half-ball. Both disks correspond exactly to its
two standard boundary pieces. See Alexander p. 7 and derivation 133. -/
theorem IsFinitePLBallPair.exists_sphere_model_of_disk_union {b d q : Set X}
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q) (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hinter : b ∩ d = q) :
    ∃ H : (b ∪ d : Set X) ≃ₜ frontier (halfBall 1), H.IsFinitePL ∧
      (∀ x : (b ∪ d : Set X), (x : X) ∈ b ↔ (H x : (ℝ × ℝ) × ℝ) ∈ cap 1) ∧
      (∀ x : (b ∪ d : Set X), (x : X) ∈ d ↔ (H x : (ℝ × ℝ) × ℝ) ∈ disk) := by
  obtain ⟨e, he, heb⟩ := hd.exists_homeomorph isFinitePLBallPair_disk
  obtain ⟨H, hH, _, hHb, hHd⟩ := hb.exists_union_homeomorph_of_boundary_piece
    (isFinitePLBallPair_cap 1) hinter (cap_inter_disk one_ne_zero) e he heb
  have hfront : cap 1 ∪ disk = frontier (halfBall 1) :=
    (frontier_halfBall (Or.inl rfl)).symm
  let G := (Homeomorph.setCongr (rfl : b ∪ d = b ∪ d)).trans
    (H.trans (Homeomorph.setCongr hfront))
  exact ⟨G, hH.setCongr rfl hfront, hHb, hHd⟩

/-- Attaching finite PL three-balls along a finite PL disk
with complementary PL boundary disks gives a PL three-ball with
the exact outer boundary. The shared disk's standard chart is
constructed internally. See Alexander p. 7 and derivation 133. -/
theorem IsFinitePLBallPair.union_of_ball_disk_attachment {s u b c d q : Set X}
    (hs : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) s (b ∪ d))
    (hu : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) u (c ∪ d))
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q) (hc : IsFinitePLBallPair (ℝ × ℝ) c q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (hbd : b ∩ d = q) (hcd : c ∩ d = q) (hsu : s ∩ u = d) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (s ∪ u) (b ∪ c) := by
  obtain ⟨e, he, heb⟩ := hd.exists_homeomorph isFinitePLBallPair_disk
  exact hs.union_of_disk_attachment hu hb hc hbd hcd hsu e he heb

end Set
