import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import PoincareConjecture.Proofs.M12.Geometry.Manifold.VectorField.Product.Coordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle VectorField
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Manifold.VectorField

section Coordinates

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem section_chart_coordinates_smooth
    (V : (q : M) → TangentSpace I q) (p : M)
    (hV : ContMDiffAt I I.tangent ∞ (T% V) p) :
    ContMDiffAt I 𝓘(ℝ, E) ∞
      (fun q => mfderiv I 𝓘(ℝ, E) (extChartAt I p) q (V q)) p := by
  have hc : ContMDiffAt I 𝓘(ℝ, E) ∞ (extChartAt I p) p :=
    contMDiffAt_extChartAt
  have hd := (hc.mfderiv_const (m := ∞) (by simp)).clm_apply_of_inCoordinates hV hc
  have h := (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).contMDiffAt.comp _ hd
  exact h

private theorem section_bracket_coordinates
    (V W : (q : M) → TangentSpace I q) (p : M)
    (hV : ContMDiffAt I I.tangent ∞ (T% V) p)
    (hW : ContMDiffAt I I.tangent ∞ (T% W) p) :
    mlieBracket I V W p =
      (show E from mfderiv I 𝓘(ℝ, E)
        (fun q => mfderiv I 𝓘(ℝ, E) (extChartAt I p) q (W q)) p (V p)) -
      (show E from mfderiv I 𝓘(ℝ, E)
        (fun q => mfderiv I 𝓘(ℝ, E) (extChartAt I p) q (V q)) p (W p)) := by
  let φ := extChartAt I p
  have hcoord (Z : (q : M) → TangentSpace I q)
      (hZ : ContMDiffAt I I.tangent ∞ (T% Z) p) :
      fderivWithin ℝ (mpullbackWithin 𝓘(ℝ, E) I φ.symm Z (range I))
          (range I) (φ p) =
        mfderiv I 𝓘(ℝ, E) (fun q => mfderiv I 𝓘(ℝ, E) φ q (Z q)) p := by
    let zc : M → E := fun q => mfderiv I 𝓘(ℝ, E) φ q (Z q)
    have heq : (zc ∘ φ.symm) =ᶠ[𝓝[range I] (φ p)]
        mpullbackWithin 𝓘(ℝ, E) I φ.symm Z (range I) := by
      filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) p] with y hy
      dsimp [zc, Function.comp_def, mpullbackWithin]
      have hi := isInvertible_mfderivWithin_extChartAt_symm (I := I) hy
      have hinv := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy
      have hid := congrArg (fun L => L
        ((mfderivWithin 𝓘(ℝ, E) I φ.symm (range I) y).inverse (Z (φ.symm y)))) hinv
      dsimp only [φ] at hid ⊢
      change (mfderiv I 𝓘(ℝ, E) (extChartAt I p) ((extChartAt I p).symm y))
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) y)
          ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (range I) y).inverse
            (Z ((extChartAt I p).symm y)))) = _ at hid
      rw [hi.self_apply_inverse] at hid
      simpa only [ContinuousLinearMap.comp_apply, hi.self_apply_inverse,
        ContinuousLinearMap.id_apply] using! hid
    have hs := (section_chart_coordinates_smooth Z p hZ).mdifferentiableAt (by simp)
    rw [mfderiv, if_pos hs]
    have heqp : (zc ∘ φ.symm) (φ p) =
        mpullbackWithin 𝓘(ℝ, E) I φ.symm Z (range I) (φ p) := by
      exact heq.eq_of_nhdsWithin (mem_range_self (chartAt H p p))
    simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, Function.id_comp] using (heq.fderivWithin_eq heqp).symm
  simp only [mlieBracket, mlieBracketWithin_apply, preimage_univ, univ_inter,
    mfderiv_extChartAt_self, ContinuousLinearMap.inverse_id,
    lieBracketWithin]
  rw [hcoord W hW, hcoord V hV]
  simp only [mpullbackWithin,
    mfderivWithin_extChartAt_symm_inverse_apply]
  dsimp only [TangentSpace] at *
  simp only [φ, ContinuousLinearMap.id_apply]
  have hp : (extChartAt I p).symm (extChartAt I p p) = p :=
    (extChartAt I p).left_inv (mem_extChartAt_source p)
  rw [hp]

end Coordinates

section Product

variable {E H M E' H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem mlieBracket_prod_snd
    (A : (t : M) → TangentSpace I t)
    (W V : (t : M) → (x : N) → TangentSpace J x) (p : M × N)
    (hX : ContMDiffAt (I.prod J) (I.prod J).tangent ∞
      (fun q : M × N => (⟨q, (A q.1, W q.1 q.2)⟩ : TangentBundle (I.prod J) (M × N))) p)
    (hY : ContMDiffAt (I.prod J) (I.prod J).tangent ∞
      (fun q : M × N => (⟨q, (0, V q.1 q.2)⟩ : TangentBundle (I.prod J) (M × N))) p) :
    (mlieBracket (I.prod J)
      (fun q : M × N => (A q.1, W q.1 q.2))
      (fun q : M × N => (0, V q.1 q.2)) p).2 =
      (show E' from mfderiv I 𝓘(ℝ, E')
        (fun s : M => (show E' from V s p.2)) p.1 (A p.1)) +
      (show E' from mlieBracket J (W p.1) (V p.1) p.2) := by
  let X : (q : M × N) → TangentSpace (I.prod J) q := fun q => (A q.1, W q.1 q.2)
  let Y : (q : M × N) → TangentSpace (I.prod J) q := fun q => (0, V q.1 q.2)
  let coord (Z : (q : M × N) → TangentSpace (I.prod J) q) : M × N → E × E' :=
    fun q => mfderiv (I.prod J) 𝓘(ℝ, E × E') (extChartAt (I.prod J) p) q (Z q)
  let sc (Z : (q : M × N) → TangentSpace (I.prod J) q) : M × N → E' :=
    fun q => mfderiv J 𝓘(ℝ, E') (extChartAt J p.2) q.2 (Z q).2
  have hproj (Z : (q : M × N) → TangentSpace (I.prod J) q)
      (hZ : ContMDiffAt (I.prod J) (I.prod J).tangent ∞ (T% Z) p) :
      ContMDiffAt (I.prod J) 𝓘(ℝ, E') ∞ (sc Z) p ∧
      ∀ w : TangentSpace (I.prod J) p,
        (mfderiv (I.prod J) 𝓘(ℝ, E × E') (coord Z) p w).2 =
          mfderiv (I.prod J) 𝓘(ℝ, E') (sc Z) p w := by
    have hc : ContMDiffAt (I.prod J) 𝓘(ℝ, E × E') ∞ (coord Z) p :=
      section_chart_coordinates_smooth Z p hZ
    have hs := (ContinuousLinearMap.snd ℝ E E').contDiff.contMDiff.contMDiffAt.comp p hc
    have heq : (fun q => (coord Z q).2) =ᶠ[𝓝 p] sc Z :=
      mfderiv_extChartAt_prod_snd_eventuallyEq Z p
    refine ⟨hs.congr_of_eventuallyEq heq.symm, ?_⟩
    intro w
    have hd := mfderiv_comp_apply (x := p)
      (ContinuousLinearMap.snd ℝ E E').differentiableAt.mdifferentiableAt
      (hc.mdifferentiableAt (by simp)) w
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hd
    change mfderiv (I.prod J) 𝓘(ℝ, E') (fun q => (coord Z q).2) p w =
      (mfderiv (I.prod J) 𝓘(ℝ, E × E') (coord Z) p w).2 at hd
    rw [heq.mfderiv_eq] at hd
    exact hd.symm
  have hZX := hproj X hX
  have hZY := hproj Y hY
  have hprod := congrArg (fun w : TangentSpace (I.prod J) p => w.2)
    (section_bracket_coordinates X Y p hX hY)
  change (mlieBracket (I.prod J) X Y p).2 =
    (mfderiv (I.prod J) 𝓘(ℝ, E × E') (coord Y) p (X p)).2 -
      (mfderiv (I.prod J) 𝓘(ℝ, E × E') (coord X) p (Y p)).2 at hprod
  rw [hZY.2, hZX.2] at hprod
  have hsplitV := mfderiv_prod_eq_add_apply (p := p)
    (hZY.1.mdifferentiableAt (by simp)) (v := X p)
  have hsplitW := mfderiv_prod_eq_add_apply (p := p)
    (hZX.1.mdifferentiableAt (by simp)) (v := Y p)
  have htimeFun : (fun s : M => sc Y (s, p.2)) =
      (fun s : M => (show E' from V s p.2)) := by
    funext s
    dsimp only [sc, Y]
    rw [mfderiv_extChartAt_self]
    rfl
  rw [htimeFun] at hsplitV
  have hprojS := (contMDiff_equivTangentBundleProd
    (I := I) (M := M) (I' := J) (M' := N) (n := ∞)).snd
  have hWt : ContMDiffAt J J.tangent ∞ (T% (W p.1)) p.2 := by
    exact (hprojS.contMDiffAt.comp p hX).comp p.2
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hVt : ContMDiffAt J J.tangent ∞ (T% (V p.1)) p.2 := by
    exact (hprojS.contMDiffAt.comp p hY).comp p.2
      (contMDiffAt_const.prodMk contMDiffAt_id)
  have hspatial := section_bracket_coordinates (W p.1) (V p.1) p.2 hWt hVt
  rw [hprod, hsplitV, hsplitW, hspatial]
  dsimp only [X, Y, sc]
  rw [map_zero, zero_add]
  dsimp only [TangentSpace]
  abel

end Product

end Poincare.Manifold.VectorField
