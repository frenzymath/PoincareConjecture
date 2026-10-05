import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Reflection
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.TerminalData

/-!
# Reflected transport for the isolated planar review

The accepted terminal and cap leaves are intentionally not imported here.  This
file records the pointwise transport identity used by the eventual reflected
consumer: a planar family over the reflected height coordinate is conjugate to
the original family by the ambient height reflection.  Keeping this identity
separate makes the four-model migration reviewable without changing the
two-model APIs.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

/- The reflected parameter is the negative of the old height.  The planar
   coordinates are unchanged, so the lifted map commutes with `Rz` up to this
   parameter change. -/
def reflectedPlanarFamily
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) :
    Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ :=
  fun t z => Φ t (-z)

theorem reflectedPlanarFamily_apply
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (t z : Real) (x : E2) :
    reflectedPlanarFamily Φ t z x = Φ t (-z) x := rfl

theorem reflectedPlanarHeightMap
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (t : Real) (y : E3) :
    planarHeightMap (reflectedPlanarFamily Φ) t (Rz y) =
      Rz (planarHeightMap Φ t y) := by
  change Saddle.toE3 (Φ t (-(Rz y 2)) (Saddle.toE2 (Rz y))) (Rz y 2) = _
  simp only [Rz_two, neg_neg]
  rfl

theorem reflectedPlanarHeightMap_involutive
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (t : Real) (y : E3) :
    Rz (planarHeightMap (reflectedPlanarFamily Φ) t (Rz y)) =
      planarHeightMap Φ t y := by
  rw [reflectedPlanarHeightMap]
  exact Rz_involutive _

theorem reflectedPlanarHeightMap_image
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (t : Real) (S : Set E3) :
    planarHeightMap (reflectedPlanarFamily Φ) t '' (Rz '' S) =
      Rz '' (planarHeightMap Φ t '' S) := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨planarHeightMap Φ t z, ⟨z, hz, rfl⟩,
      (reflectedPlanarHeightMap Φ t z).symm⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Rz z, ⟨z, hz, rfl⟩, ?_⟩
    exact reflectedPlanarHeightMap Φ t z

theorem reflectedPlanarFamily_smooth
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2)) :
    ContDiff Real ∞ (fun q : Real × Real × E2 =>
      reflectedPlanarFamily Φ q.1 q.2.1 q.2.2) := by
  exact hΦ.comp (contDiff_fst.prodMk
    ((contDiff_fst.comp contDiff_snd).neg.prodMk (contDiff_snd.comp contDiff_snd)))

theorem reflectedPlanarFamily_inverse_smooth
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2)) :
    ContDiff Real ∞ (fun q : Real × Real × E2 =>
      (reflectedPlanarFamily Φ q.1 q.2.1).symm q.2.2) := by
  exact hΦ.comp (contDiff_fst.prodMk
    ((contDiff_fst.comp contDiff_snd).neg.prodMk (contDiff_snd.comp contDiff_snd)))

theorem reflectedPlanarHeightMap_fixed
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {U : Set E3} (hfix : ∀ t, EqOn (planarHeightMap Φ t) id U) :
    ∀ t, EqOn (planarHeightMap (reflectedPlanarFamily Φ) t) id (Rz '' U) := by
  rintro t _ ⟨x, hx, rfl⟩
  rw [reflectedPlanarHeightMap, hfix t hx]
  rfl

theorem Rz_image_inter (S T : Set E3) :
    Rz '' (S ∩ T) = Rz '' S ∩ Rz '' T :=
  Set.image_inter Rz.injective

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
