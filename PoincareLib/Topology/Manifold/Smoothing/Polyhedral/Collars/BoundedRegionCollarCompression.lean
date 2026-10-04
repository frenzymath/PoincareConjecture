import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Disks.PLDiskSurgeryModels
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallTopology

/-!
# Compressing an attached ball into a boundary collar

Attach the old ball and its actual collar along the exposed
disk. The marked-piece extension maps this union onto the
collar, fixing the collar's inner boundary disk pointwise.
This is the local compression in Hudson 1969, Lemma 2.14,
pp. 60--61; see M76 derivation 247.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- An actual ball attached to its ball collar compresses
into that collar by a finite PL homeomorphism fixing the
exposed inner disk and sending the old remaining disk to
the collar base. All overlaps are exact, explicit data.
See Hudson pp. 60--61 and M76 derivation 247. -/
theorem IsFinitePLBallPair.exists_boundary_collar_compression
    {s C b d e q : Set X}
    (hs : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) s (b ∪ d))
    (hC : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C (b ∪ e))
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d q)
    (he : IsFinitePLBallPair (ℝ × ℝ) e q)
    (hbd : b ∩ d = q) (hbe : b ∩ e = q) (hsC : s ∩ C = b) :
    ∃ H : (s ∪ C : Set X) ≃ₜ C, H.IsFinitePL ∧
      (∀ x : e, (H ⟨x, Or.inr (hC.1 (Or.inr x.property))⟩ : X) = x) ∧
      (∀ x : (s ∪ C : Set X), (x : X) ∈ d ↔ (H x : X) ∈ b) ∧
      ∀ x : (s ∪ C : Set X), (x : X) ∈ e ↔ (H x : X) ∈ e := by
  have hs' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) s (d ∪ b) := by
    simpa only [union_comm] using hs
  have hC' : IsFinitePLBallPair ((ℝ × ℝ) × ℝ) C (e ∪ b) := by
    simpa only [union_comm] using hC
  have hdb : d ∩ b = q := (inter_comm _ _).trans hbd
  have heb : e ∩ b = q := (inter_comm _ _).trans hbe
  have hde : d ∩ e = q := by
    apply Subset.antisymm
    · intro x hx
      have hxb : x ∈ b := hsC.subset
        ⟨hs.1 (Or.inr hx.1), hC.1 (Or.inr hx.2)⟩
      exact hbd.subset ⟨hxb, hx.1⟩
    · exact subset_inter hd.1 he.1
  have hunion := hs'.union_of_ball_disk_attachment hC' hd he hb hdb heb hsC
  have hecopy := he
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKe, _⟩, _⟩, _⟩ := hecopy
  have hid : (Homeomorph.refl e).IsFinitePL :=
    ⟨id, ⟨K, hK, hKe, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ X)⟩,
      fun _ => rfl⟩
  obtain ⟨H, hH, hHe, hHd, hHeq⟩ := hunion.exists_extension_of_boundary_piece
    hC hd hb hde hbe (Homeomorph.refl e) hid (fun _ => Iff.rfl)
  exact ⟨H, hH, fun x => congrArg Subtype.val (hHe x), hHd, hHeq⟩

end Set
