import PoincareConjecture.Proofs.M83.Mathlib.LocalLinearization
import PoincareConjecture.Proofs.M83.EuclideanOrientation
import PoincareConjecture.Proofs.M83.PositiveLinearLocal
import PoincareConjecture.Proofs.M02.Topology.PositiveThreeAtlas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory HomologicalComplex Set Filter Metric
open scoped Topology unitInterval

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology

private def affineMap (x y : E3) (L : E3 ≃L[Real] E3) : C(E3, E3) :=
  ⟨fun z => y + L (z - x), by fun_prop⟩

private theorem affineMap_puncture (x y : E3) (L : E3 ≃L[Real] E3) :
    MapsTo (affineMap x y L) ({x}ᶜ : Set E3) ({y}ᶜ : Set E3) := by
  intro z hz he
  change y + L (z - x) = y at he
  have hzL : L (z - x) = 0 :=
    add_left_cancel (show y + L (z - x) = y + 0 by simpa using he)
  exact hz (sub_eq_zero.mp (L.injective (hzL.trans L.map_zero.symm)))

private theorem affineMap_action (O : LocalOrientation E3) (x y : E3)
    (L : E3 ≃L[Real] E3) (hL : 0 < L.toLinearEquiv.toLinearMap.det) :
    homologyMap (integralRelativeMap (affineMap x y L) (affineMap_puncture x y L)) 3
      (O.atPoint x) = O.atPoint y := by
  let l : C(E3, E3) := ⟨L, L.continuous⟩
  have hl : MapsTo l ({0}ᶜ : Set E3) ({0}ᶜ : Set E3) := by
    intro z hz he
    exact hz (L.injective (he.trans L.map_zero.symm))
  have hc : integralRelativeMap (translation x) (translation_puncture x) ≫
      integralRelativeMap (affineMap x y L) (affineMap_puncture x y L) =
      integralRelativeMap l hl ≫ integralRelativeMap (translation y)
        (translation_puncture y) := by
    rw [integralRelativeMap_comp, integralRelativeMap_comp]
    congr 1
    ext z : 1
    change y + L ((z + x) - x) = L z + y
    simp [add_comm]
  have h := congrArg (fun k =>
      (ConcreteCategory.hom (homologyMap k 3)) (O.atPoint 0)) hc
  rw [homologyMap_comp, homologyMap_comp, ModuleCat.comp_apply,
    ModuleCat.comp_apply, translation_preserves_orientation] at h
  have hp := positiveLinear_relativeHomologyMap L hL 3
  change homologyMap (integralRelativeMap l hl) 3 = 𝟙 _ at hp
  rw [hp, ModuleCat.id_apply, translation_preserves_orientation] at h
  exact h

theorem positiveOpenPartialOrientation
    (O : LocalOrientation E3) (c : OpenPartialHomeomorph E3 E3)
    [LocallyCompactSpace c.source] (x : c.source)
    (hdet : 0 < (fderiv Real (fun z : E3 => c z)
      (x : E3)).toLinearMap.det) :
    (O.pullback (⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩ : C(c.source, E3))
      c.isOpenEmbedding_restrict).atPoint x =
      (O.pullback (⟨Subtype.val, continuous_subtype_val⟩ : C(c.source, E3))
        c.open_source.isOpenEmbedding_subtypeVal).atPoint x := by
  let F : E3 → E3 := fun z => c z
  have hdiff : DifferentiableAt Real F (x : E3) := by
    by_contra hn
    rw [fderiv_zero_of_not_differentiableAt hn] at hdet
    simp at hdet
  let L : E3 ≃L[Real] E3 :=
    (fderiv Real F (x : E3)).toContinuousLinearEquivOfDetNeZero (ne_of_gt hdet)
  have hLderiv : HasFDerivAt F L.toContinuousLinearMap (x : E3) := by
    simpa only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
      using hdiff.hasFDerivAt
  have hLdet : 0 < L.toLinearEquiv.toLinearMap.det := by
    change 0 < (fderiv Real F (x : E3)).toLinearMap.det
    exact hdet
  obtain ⟨r, hr, hrU, H, havoid⟩ := exists_ball_linearization_homotopy
    c.open_source x.property c.continuousOn L hLderiv
  let B : Set E3 := ball (x : E3) r
  let z : B := ⟨x, mem_ball_self hr⟩
  let bmap : C(B, c.source) :=
    ⟨fun w => ⟨w.val, hrU w.property⟩, continuous_subtype_val.subtype_mk _⟩
  let incB : C(B, E3) := ⟨Subtype.val, continuous_subtype_val⟩
  let incU : C(c.source, E3) := ⟨Subtype.val, continuous_subtype_val⟩
  have hincU : Function.Injective incU := by
    intro a b hab
    exact Subtype.ext hab
  let cmap : C(c.source, E3) :=
    ⟨c.source.domRestrict c, c.continuousOn.domRestrict⟩
  let cB : C(B, E3) := cmap.comp bmap
  let aB : C(B, E3) := (affineMap x (c x) L).comp incB
  have hbmap : _root_.Topology.IsOpenEmbedding bmap := by
    apply c.open_source.isOpenEmbedding_subtypeVal.of_comp bmap
    exact isOpen_ball.isOpenEmbedding_subtypeVal
  have hpinc : MapsTo incB ({z}ᶜ : Set B) ({(x : E3)}ᶜ : Set E3) := by
    intro w hw he
    exact hw (Subtype.ext he)
  have hpc : MapsTo cB ({z}ᶜ : Set B) ({c (x : E3)}ᶜ : Set E3) := by
    intro w hw he
    exact hw (Subtype.ext (c.injOn (hrU w.property) x.property he))
  have hpa : MapsTo aB ({z}ᶜ : Set B) ({c (x : E3)}ᶜ : Set E3) :=
    (affineMap_puncture x (c x) L).comp hpinc
  have hhom : homologyMap (integralRelativeMap aB hpa) 3 =
      homologyMap (integralRelativeMap cB hpc) 3 := by
    exact relativeHomologyMap_eq_of_homotopy H hpa hpc
      (fun t w hw => havoid t w (fun he => hw (Subtype.ext he))) 3
  let UO := O.pullback incU c.open_source.isOpenEmbedding_subtypeVal
  let b : LocalHomology B z 3 := (localHomologyEquiv bmap hbmap z 3).symm
    (UO.atPoint x)
  have hbu : localHomologyMap bmap hbmap.injective z 3 b = UO.atPoint x := by
    exact (localHomologyEquiv bmap hbmap z 3).apply_symm_apply _
  have hbe : homologyMap (integralRelativeMap incB hpinc) 3 b = O.atPoint (x : E3) := by
    have hh := congrArg (fun k => k b)
      (localHomologyMap_comp bmap incU hbmap.injective hincU z 3)
    have hmapU : localHomologyMap incU hincU (bmap z) 3
        (UO.atPoint x) = O.atPoint (incU (bmap z)) := by
        simpa [UO, bmap, z] using
        (LocalOrientation.map_pullback O incU
          c.open_source.isOpenEmbedding_subtypeVal x)
    rw [ModuleCat.comp_apply, hbu, hmapU] at hh
    have hcomp : incU.comp bmap = incB := by
      ext w
      rfl
    simpa [incB, incU, bmap, z, hcomp, localHomologyMap, localChainsMap] using hh.symm
  have hctarget : localHomologyMap cmap c.isOpenEmbedding_restrict.injective x 3
      (UO.atPoint x) = O.atPoint (cmap x) := by
    have hc := congrArg (fun k => k b)
      (localHomologyMap_comp bmap cmap hbmap.injective
        c.isOpenEmbedding_restrict.injective z 3)
    rw [ModuleCat.comp_apply, hbu] at hc
    change localHomologyMap cmap c.isOpenEmbedding_restrict.injective x 3
      (UO.atPoint x) = homologyMap (integralRelativeMap cB hpc) 3 b at hc
    rw [← hhom] at hc
    have ha : integralRelativeMap incB hpinc ≫
        integralRelativeMap (affineMap x (c x) L) (affineMap_puncture x (c x) L) =
        integralRelativeMap aB hpa := integralRelativeMap_comp _ _ _ _
    rw [← ha, homologyMap_comp, ModuleCat.comp_apply, hbe, affineMap_action O
      (x : E3) (c x) L hLdet] at hc
    exact hc
  apply (localHomologyEquiv cmap c.isOpenEmbedding_restrict x 3).injective
  change localHomologyMap cmap c.isOpenEmbedding_restrict.injective x 3 _ =
    localHomologyMap cmap c.isOpenEmbedding_restrict.injective x 3 _
  rw [LocalOrientation.map_pullback, hctarget]

end PoincareConjecture.Proofs.M83
