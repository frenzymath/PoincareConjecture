import PoincareConjecture.Proofs.M35.RadialGauge.EvenNormFamily
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicInverseFamily
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicSpatialCoordinate











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial RadialGauge

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

include hrotation in


theorem raw_intrinsicSpatialCoordinate_contDiffOn :
    ContDiffOn ℝ ∞
      (fun p : ℝ × StandardCapSpace => intrinsicSpatialCoordinate (G.flow.metric p.1) p.2)
      (Ioo 0 G.lifetime ×ˢ univ) := by
  have hq := axisDivision_family_contDiffOn
    (f := fun t => radialArclength (G.flow.metric t))
    isOpen_Ioo (raw_radialArclength_contDiffOn G)
  have he (t : ℝ) (ht : t ∈ Ioo 0 G.lifetime) :
      Function.Even (axisDivision (radialArclength (G.flow.metric t))) :=
    axisDivision_even_of_odd (radialArclength_contDiff (G.flow.metric t))
      (radialArclength_odd (G.flow.metric t) (hrotation t ⟨ht.1.le, ht.2⟩))
  have hlift := evenNorm_family_contDiffOn (E := StandardCapSpace)
    (f := fun t => axisDivision (radialArclength (G.flow.metric t))) isOpen_Ioo hq he
  exact hlift.smul contDiffOn_snd



noncomputable def rawIntrinsicSpatialDiffeomorph (t : ℝ) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ :=
  if ht : t ∈ Ico 0 G.lifetime then
    intrinsicSpatialDiffeomorph (G.flow.metric t) (hrotation t ht) (G.complete P ht)
  else Diffeomorph.refl (𝓡 3) StandardCapSpace ∞

theorem rawIntrinsicSpatialDiffeomorph_apply {t : ℝ}
    (ht : t ∈ Ico 0 G.lifetime) (x : StandardCapSpace) :
    rawIntrinsicSpatialDiffeomorph P G hrotation t x =
      intrinsicSpatialCoordinate (G.flow.metric t) x := by
  simp only [rawIntrinsicSpatialDiffeomorph, dif_pos ht]
  rfl

theorem rawIntrinsicSpatialDiffeomorph_symm_apply {t : ℝ}
    (ht : t ∈ Ico 0 G.lifetime) (x : StandardCapSpace) :
    (rawIntrinsicSpatialDiffeomorph P G hrotation t).symm x =
      axisDivision (rawInverseRadius P G hrotation t) ‖x‖ • x := by
  have heq : rawInverseRadius P G hrotation t =
      (radialArclengthOrderIso (G.flow.metric t) (hrotation t ht) (G.complete P ht)).symm :=
    funext (rawInverseRadius_eq P G hrotation ht)
  rw [heq]
  simp only [rawIntrinsicSpatialDiffeomorph, dif_pos ht]
  rfl



theorem rawIntrinsicSpatialDiffeomorph_contDiffOn :
    ContDiffOn ℝ ∞
      (fun p : ℝ × StandardCapSpace => rawIntrinsicSpatialDiffeomorph P G hrotation p.1 p.2)
      (Ioo 0 G.lifetime ×ˢ univ) := by
  apply (raw_intrinsicSpatialCoordinate_contDiffOn G hrotation).congr
  intro p hp
  exact rawIntrinsicSpatialDiffeomorph_apply P G hrotation ⟨hp.1.1.le, hp.1.2⟩ p.2



theorem rawIntrinsicSpatialDiffeomorph_symm_contDiffOn :
    ContDiffOn ℝ ∞
      (fun p : ℝ × StandardCapSpace => (rawIntrinsicSpatialDiffeomorph P G hrotation p.1).symm p.2)
      (Ioo 0 G.lifetime ×ˢ univ) := by
  have hs := rawInverseRadius_contDiffOn P G hrotation
  have hq := axisDivision_family_contDiffOn isOpen_Ioo hs
  have he (t : ℝ) (ht : t ∈ Ioo 0 G.lifetime) :
      Function.Even (axisDivision (rawInverseRadius P G hrotation t)) := by
    have htcc : t ∈ Ico 0 G.lifetime := ⟨ht.1.le, ht.2⟩
    have heq : rawInverseRadius P G hrotation t =
        (radialArclengthOrderIso (G.flow.metric t) (hrotation t htcc)
          (G.complete P htcc)).symm := funext (rawInverseRadius_eq P G hrotation htcc)
    rw [heq]
    exact axisDivision_even_of_odd
      (radialArclengthOrderIso_symm_contDiff (G.flow.metric t)
        (hrotation t htcc) (G.complete P htcc))
      (radialArclengthOrderIso_symm_odd (G.flow.metric t)
        (hrotation t htcc) (G.complete P htcc))
  have hlift := evenNorm_family_contDiffOn (E := StandardCapSpace)
    (f := fun t => axisDivision (rawInverseRadius P G hrotation t)) isOpen_Ioo hq he
  apply (hlift.smul contDiffOn_snd).congr
  intro p hp
  exact rawIntrinsicSpatialDiffeomorph_symm_apply P G hrotation ⟨hp.1.1.le, hp.1.2⟩ p.2

end PoincareConjecture.M35.Uniqueness
