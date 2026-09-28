import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.LiftedRimPL
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusPLLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
local notation "C" => Dehn.annulusCylinderHomeomorph

theorem exists_hamiltonZero_marked_annulus_covering_PL
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j : (ℝ × ℝ) → X0} (hj : PolyhedralPLInCharts e j Ann)
    {theta : C0} {alpha beta : ℝ}
    (hphase : ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).1.2 = theta)
    (hlower : ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).2 =
        (alpha : C0))
    (D : Ann ≃ₜ Ann) (hD : D.IsFinitePL) :
    ∃ q : (ℝ × ℝ) → X0, PolyhedralPLInCharts d q Ann ∧
      ∀ x : Ann, q x = (Q0).symm
        (((Q0 (hamiltonZeroAmbientMap phi
          (j (Dehn.annulusRimPoint false ((C).symm (D x)).2)))).1.1, theta),
          (((beta - alpha) * (((C).symm (D x)).1 : ℝ) + alpha : ℝ) : C0)) := by
  classical
  let band := rectangle (4 * (8 : ℝ)) 1
  obtain ⟨K, hK, hKs, _⟩ := finitePiecewiseAffineOn_wrappedStripMap
    (L := 8) (d := 1) (by norm_num) (by norm_num)
  let lower : (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
      (ContinuousAffineMap.const ℝ (ℝ × ℝ) (-1))
  have hlowerPL : FinitePiecewiseAffineOn lower band :=
    ⟨K, hK, hKs, K.affineOnFaces_affine lower⟩
  let rim : (ℝ × ℝ) → ℝ × ℝ := fun z =>
    Dehn.annulusRimPoint false (z.1 : Circle)
  have hrim : FinitePiecewiseAffineOn rim band := by
    have h := (finitePiecewiseAffineOn_wrappedStripMap
      (L := 8) (d := 1) (by norm_num) (by norm_num)).comp hlowerPL (by
        intro z hz
        exact ⟨hz.1, by change -1 ≤ -1 ∧ (-1 : ℝ) ≤ 1; norm_num⟩)
    apply h.congr
    intro z hz
    exact (annulusMap_coe (L := 8) (t := -1) (s := z.1)
      (by norm_num) (by norm_num) hz.1).symm
  have hrimK : FinitePiecewiseAffineOn rim K.space := by simpa only [hKs] using hrim
  have hjrim := hj.comp_finitePiecewiseAffineOn K hK hrimK
    (fun z _ => (Dehn.annulusRimPoint false (z.1 : Circle)).property)
  have hY := hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hjrim
  let w : (ℝ × ℝ) →ᴬ[ℝ] ℝ := ((beta - alpha) / 2) •
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ (ℝ × ℝ) 1)
  let Y : (ℝ × ℝ) → X0 := fun z =>
    hamiltonZeroAmbientMap phi (j (rim z))
  let strip : (ℝ × ℝ) → X0 := fun z => hamiltonZeroTargetTranslation (w z, Y z)
  have hstrip : PolyhedralPLInCharts d strip band := by
    have hw : FinitePiecewiseAffineOn w K.space :=
      ⟨K, hK, rfl, K.affineOnFaces_affine w⟩
    change PolyhedralPLInCharts d
      (fun z => hamiltonZeroTargetTranslation (w z, Y z)) (rectangle (4 * (8 : ℝ)) 1)
    simpa only [Y, rim, Function.comp_def, hKs] using
      hd.polyhedralPL_hamiltonZeroTargetTranslation hY hw
  let a : Circle × Icc (-1 : ℝ) 1 → X0 := fun z =>
    (Q0).symm
      (((Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z.1)))).1.1,
        theta), (((beta - alpha) * ((z.2 : ℝ) + 1) / 2 + alpha : ℝ) : C0))
  have ha (s : ℝ) (_hs : s ∈ Icc 0 (4 * (8 : ℝ))) (u : Icc (-1 : ℝ) 1) :
      a ((s : Circle), u) = strip (s, u) := by
    apply (Q0).injective
    rw [Homeomorph.apply_symm_apply]
    rw [hamiltonZeroTargetTranslation_coordinates]
    apply Prod.ext
    · exact Prod.ext rfl (hphase (s : Circle)).symm
    · change (((beta - alpha) * ((u : ℝ) + 1) / 2 + alpha : ℝ) : C0) =
        (Q0 (Y (s, u))).2 + ((w (s, u) : ℝ) : C0)
      rw [show (Q0 (Y (s, u))).2 = (alpha : C0) from hlower (s : Circle)]
      rw [← AddCircle.coe_add]
      congr 1
      change (beta - alpha) * ((u : ℝ) + 1) / 2 + alpha =
        alpha + (beta - alpha) / 2 * ((u : ℝ) + 1)
      ring
  obtain ⟨E, q₀, hE, hq₀, hqE, _, _⟩ :=
    _root_.Dehn.exists_square_annulus_map_of_period hphi.target_domain.compatible
      (by norm_num : (0 : ℝ) < 1) (by norm_num : 4 * (1 : ℝ) < 8) strip hstrip a ha
  have hqC (y : unitInterval × Circle) : q₀ ((C) y) =
      (Q0).symm
        (((Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false y.2)))).1.1,
          theta), (((beta - alpha) * (y.1 : ℝ) + alpha : ℝ) : C0)) := by
    let u : Icc (-1 : ℝ) 1 := ⟨2 * (y.1 : ℝ) - 1, by
      constructor <;> linarith [y.1.property.1, y.1.property.2]⟩
    have hpoint : (C) y = E (y.2, u) := by
      apply Subtype.ext
      rw [hE, Dehn.annulusCylinderHomeomorph_apply]
      rfl
    rw [hpoint, hqE]
    dsimp only [a]
    congr 2
    change (((beta - alpha) * ((2 * (y.1 : ℝ) - 1) + 1) / 2 + alpha : ℝ) : C0) = _
    congr 1
    ring
  obtain ⟨fD, hfD, hfDv⟩ := hD
  obtain ⟨J, hJ, hJs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (by norm_num : (0 : ℝ) < 1) (by norm_num : 4 * (1 : ℝ) < 8)
  have hmap : MapsTo fD J.space Ann := by
    intro x hx
    rw [← hfDv ⟨x, hJs.subset hx⟩]
    exact (D ⟨x, hJs.subset hx⟩).property
  have hcomp := hq₀.comp_finitePiecewiseAffineOn J hJ
    (show FinitePiecewiseAffineOn fD J.space from hJs ▸ hfD) hmap
  refine ⟨q₀ ∘ fD, hJs ▸ hcomp, ?_⟩
  intro x
  rw [Function.comp_apply, ← hfDv x]
  have h := hqC ((C).symm (D x))
  rwa [Homeomorph.apply_symm_apply] at h

theorem exists_hamiltonZero_oriented_marked_annulus_covering_PL
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j : (ℝ × ℝ) → X0} (hj : PolyhedralPLInCharts e j Ann)
    {theta : C0} {alpha beta : ℝ} (reverse : Bool)
    (hphase : ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).1.2 = theta)
    (hlower : ∀ z : Circle,
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).2 =
        ((if reverse then beta else alpha : ℝ) : C0))
    (D : Ann ≃ₜ Ann) (hD : D.IsFinitePL) :
    ∃ q : (ℝ × ℝ) → X0, PolyhedralPLInCharts d q Ann ∧
      ∀ x : Ann, q x = (Q0).symm
        (((Q0 (hamiltonZeroAmbientMap phi
          (j (Dehn.annulusRimPoint false ((C).symm (D x)).2)))).1.1, theta),
          (((beta - alpha) *
            (if reverse then 1 - (((C).symm (D x)).1 : ℝ)
              else (((C).symm (D x)).1 : ℝ)) + alpha : ℝ) : C0)) := by
  cases reverse
  · exact exists_hamiltonZero_marked_annulus_covering_PL hd hphi hj hphase hlower D hD
  · obtain ⟨q, hq, hqval⟩ := exists_hamiltonZero_marked_annulus_covering_PL
      (alpha := beta) (beta := alpha) hd hphi hj hphase hlower D hD
    refine ⟨q, hq, fun x => (hqval x).trans ?_⟩
    congr 2
    change (((alpha - beta) * (((C).symm (D x)).1 : ℝ) + beta : ℝ) : C0) =
      (((beta - alpha) * (1 - (((C).symm (D x)).1 : ℝ)) + alpha : ℝ) : C0)
    congr 1
    ring

end PoincareConjecture.M76
