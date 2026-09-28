import PoincareConjecture.Proofs.M83.LocalHomeomorphOrientation
import PoincareConjecture.Proofs.M83.AntipodalOrientation
import PoincareConjecture.Proofs.M83.ShellEmbedding












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set

namespace PoincareConjecture.Proofs.M83

private def shellDeckMap : C(Shell, Shell) :=
  ⟨shellAntipodal, shellAntipodal.continuous⟩

private def shellOrientation : LocalOrientation Shell :=
  euclideanLocalOrientation.pullback shellEmbedding shellEmbedding_open

private theorem shellOrientation_reversed (x : Shell) :
    (shellOrientation.pullback shellDeckMap shellAntipodal.isOpenEmbedding).atPoint x =
      -shellOrientation.atPoint x := by
  let O := euclideanLocalOrientation
  have hc : shellEmbedding.comp shellDeckMap = negation.comp shellEmbedding := by
    ext z : 1
    exact shellEmbedding_antipodal z
  calc
    _ = (O.pullback (shellEmbedding.comp shellDeckMap)
        (shellEmbedding_open.comp shellAntipodal.isOpenEmbedding)).atPoint x :=
      LocalOrientation.pullback_comp O shellDeckMap shellEmbedding
        shellAntipodal.isOpenEmbedding shellEmbedding_open x
    _ = (O.pullback (negation.comp shellEmbedding)
        ((Homeomorph.neg E3).isOpenEmbedding.comp shellEmbedding_open)).atPoint x :=
      LocalOrientation.pullback_congr O _ _ _ _ hc x
    _ = ((O.pullback negation (Homeomorph.neg E3).isOpenEmbedding).pullback
        shellEmbedding shellEmbedding_open).atPoint x :=
      (LocalOrientation.pullback_comp O shellEmbedding negation shellEmbedding_open
        (Homeomorph.neg E3).isOpenEmbedding x).symm
    _ = -shellOrientation.atPoint x := by
      simpa only [O, shellOrientation, neg_one_zsmul] using LocalOrientation.pullback_smul
        (O.pullback negation (Homeomorph.neg E3).isOpenEmbedding) O (-1)
        (fun y => by simpa only [neg_one_zsmul] using negation_pullback O y)
        shellEmbedding shellEmbedding_open x




theorem projectivePlaneThickening_not_orientable
    [T2Space (RealProjectiveTwo × NormalInterval)]
    [LocallyCompactSpace (RealProjectiveTwo × NormalInterval)]
    (O : LocalOrientation (RealProjectiveTwo × NormalInterval)) : False := by
  obtain ⟨Q, hQ⟩ := exists_localOrientation_lift_of_isLocalHomeomorph
    projectivePlaneCover projectivePlaneCover_isLocalHomeomorph O
  let x : Shell := Classical.choice inferInstance
  obtain ⟨a, ha⟩ := Q.exists_smul shellOrientation x
  have hinv : (Q.pullback shellDeckMap shellAntipodal.isOpenEmbedding).atPoint x =
      Q.atPoint x := by
    apply (localHomologyEquiv shellDeckMap shellAntipodal.isOpenEmbedding x 3).injective
    change localHomologyMap shellDeckMap shellAntipodal.injective x 3 _ =
      localHomologyMap shellDeckMap shellAntipodal.injective x 3 _
    rw [LocalOrientation.map_pullback]
    exact (localHomologyMap_eq_of_lift projectivePlaneCover
      projectivePlaneCover_isLocalHomeomorph O Q hQ shellAntipodal
      (fun z => projectivePlaneCover_antipodal z.1 z.2) x).symm
  have hrev := LocalOrientation.pullback_smul Q shellOrientation a ha
    shellDeckMap shellAntipodal.isOpenEmbedding x
  rw [hinv, shellOrientation_reversed, zsmul_neg, ← ha x] at hrev
  exact Q.atPoint_ne_neg x hrev

end PoincareConjecture.Proofs.M83
