import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondReflection
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn

noncomputable def signedTubePrismReparametrization
    (d : signedTubeDiamond ≃ₜ signedTubeDiamond) (α β : ℝ) :
    ↥(signedTubeDiamond ×ˢ Icc α β) ≃ₜ ↥(signedTubeDiamond ×ˢ Icc α β) :=
  (Homeomorph.Set.prod signedTubeDiamond (Icc α β)).trans
    ((d.prodCongr (Homeomorph.refl _)).trans
      (Homeomorph.Set.prod signedTubeDiamond (Icc α β)).symm)

theorem signedTubePrismReparametrization_apply
    (d : signedTubeDiamond ≃ₜ signedTubeDiamond) (α β : ℝ)
    (x : ↥(signedTubeDiamond ×ˢ Icc α β)) :
    (signedTubePrismReparametrization d α β x : (ℝ × ℝ) × ℝ) =
      ((d ⟨(x : (ℝ × ℝ) × ℝ).1, x.property.1⟩ : ℝ × ℝ), (x : (ℝ × ℝ) × ℝ).2) := rfl

theorem signedTubePrismReparametrization_isFinitePL
    {d : signedTubeDiamond ≃ₜ signedTubeDiamond} (hd : d.IsFinitePL)
    {α β : ℝ} (hαβ : α < β) :
    (signedTubePrismReparametrization d α β).IsFinitePL := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := isFinitePLBallPair_Icc hαβ
  have hid : (Homeomorph.refl (Icc α β)).IsFinitePL :=
    ⟨id, ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩, fun _ => rfl⟩
  exact hd.prod hid

theorem signedTubePrismReparametrization_center
    (d : signedTubeDiamond ≃ₜ signedTubeDiamond) (α β : ℝ)
    (hzero : d ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩ =
      ⟨(0, 0), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _)⟩)
    (t : Icc α β) :
    signedTubePrismReparametrization d α β
      ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _), t.property⟩ =
      ⟨((0, 0), t), signedTubeRadius_subset_diamond 0 false (left_mem_segment ℝ _ _), t.property⟩ := by
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val hzero) rfl

end PoincareConjecture.M76.Dehn
