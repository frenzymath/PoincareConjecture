import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionAxial
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionProfile
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapEmbedding
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem exists_reunion_axial_chart (P : SurgeryCapProfile)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (a lambda ε : ℝ) (ha : 0 < a) (hlambda : 0 < lambda) (hε : 0 < ε) :
    let M := stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞,
      (∀ t Z : ℝ, D (t, Z) = (t, reunionAxialHeight a lambda ε t Z)) ∧
      ∃ e : OpenPartialHomeomorph (ℝ × E3) (ℝ × E3),
        e.source = {p : ℝ × E3 |
          ((M 1 (heightCoordinates p.2)).1,
            a + reunionAxialHeight a lambda ε p.1 (M 1 (heightCoordinates p.2)).2)
              ∈ T.source} ∧
        e.target = univ ×ˢ T.target ∧
        (∀ t : ℝ, ∀ y : E3, e (t, y) =
          (t, T ((M 1 (heightCoordinates y)).1,
            a + reunionAxialHeight a lambda ε t (M 1 (heightCoordinates y)).2))) ∧
        (∀ t : ℝ, ∀ Y : E3, e.symm (t, Y) =
          let w := T.symm Y
          let Z := (D.symm (t, w.2 - a)).2
          let z := Z / P.vertical w.1
          (t, heightCoordinates.symm ((reunionReflectedHorizontal P z)⁻¹ • w.1, z))) ∧
        ContDiffOn ℝ ∞ e e.source ∧
        ContDiffOn ℝ ∞ e.symm e.target ∧
        ∀ t : ℝ, ∀ q : UnitTwoSphere, (t, (q : E3)) ∈ e.source := by
  obtain ⟨hA, hApos, _hAnear, _hAfar, _hAbound, _hAnorth, _hAsouth, _hAoff⟩ :=
    reunionReflectedHorizontal_spec P
  obtain ⟨D, hD, hDi⟩ := exists_reunion_axial_spacetime_diffeomorph a lambda ε ha hlambda hε
  have hg := (reunionAxialHeight_spec a lambda ε ha hlambda hε).1
  let M := stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
    P.vertical P.vertical
  let A := flatCapDiffeomorph (reunionReflectedHorizontal P) P.vertical hA P.vertical_smooth
    (fun z => (hApos z).ne') (fun X => (P.vertical_pos X).ne')
  have hM (p : E2 × ℝ) : M 1 p = A p := by
    simp only [M, stackCapProfilePath, stackProfileBlend_of_one_le _ _ 1 le_rfl,
      A, flatCapDiffeomorph_apply]
  let B : Diffeomorph 𝓘(ℝ, ℝ × (E2 × ℝ)) 𝓘(ℝ, ℝ × (E2 × ℝ))
      (ℝ × (E2 × ℝ)) (ℝ × (E2 × ℝ)) ∞ := {
    toEquiv := {
      toFun := fun p => (p.1, p.2.1, reunionAxialHeight a lambda ε p.1 p.2.2)
      invFun := fun p => (p.1, p.2.1, (D.symm (p.1, p.2.2)).2)
      left_inv := by
        rintro ⟨t, X, Z⟩
        have h := D.symm_apply_apply (t, Z)
        rw [hD] at h
        have hz := congrArg Prod.snd h
        exact Prod.ext rfl (Prod.ext rfl hz)
      right_inv := by
        rintro ⟨t, X, w⟩
        exact Prod.ext rfl (Prod.ext rfl (hDi t w).2.1) }
    contMDiff_toFun :=
      (contDiff_fst.prodMk (contDiff_snd.fst.prodMk
        (hg.comp (contDiff_fst.prodMk contDiff_snd.snd)))).contMDiff
    contMDiff_invFun :=
      (contDiff_fst.prodMk (contDiff_snd.fst.prodMk
        (((D.symm.contMDiff_toFun.contDiff).comp
          (contDiff_fst.prodMk contDiff_snd.snd)).snd))).contMDiff }
  let placement := surgeryCapPlacementDiffeomorph a 1 0 1 one_ne_zero one_ne_zero
  let c := ((((Homeomorph.refl ℝ).prodCongr
    (heightCoordinates.toHomeomorph.trans A.toHomeomorph)).trans B.toHomeomorph).trans
      ((Homeomorph.refl ℝ).prodCongr placement.toHomeomorph))
  let e := c.toOpenPartialHomeomorph.trans ((OpenPartialHomeomorph.refl ℝ).prod T)
  have hc (t : ℝ) (y : E3) : c (t, y) =
      (t, ((M 1 (heightCoordinates y)).1,
        a + reunionAxialHeight a lambda ε t (M 1 (heightCoordinates y)).2)) := by
    change (t, placement ((A (heightCoordinates y)).1,
      reunionAxialHeight a lambda ε t (A (heightCoordinates y)).2)) = _
    rw [hM, surgeryCapPlacementDiffeomorph_apply]
    simp only [one_mul, zero_add]
  have hesource : e.source = {p : ℝ × E3 |
      ((M 1 (heightCoordinates p.2)).1,
        a + reunionAxialHeight a lambda ε p.1 (M 1 (heightCoordinates p.2)).2) ∈ T.source} := by
    ext p
    change (True ∧ (True ∧ (c p).2 ∈ T.source)) ↔ _
    rw [show p = (p.1, p.2) from rfl, hc]
    simp only [true_and, mem_ofPred_eq]
  have hetarget : e.target = univ ×ˢ T.target := by
    ext p
    change ((True ∧ p.2 ∈ T.target) ∧ True) ↔ (True ∧ p.2 ∈ T.target)
    simp only [and_true]
  have heq (t : ℝ) (y : E3) : e (t, y) =
      (t, T ((M 1 (heightCoordinates y)).1,
        a + reunionAxialHeight a lambda ε t (M 1 (heightCoordinates y)).2)) := by
    change ((c (t, y)).1, T (c (t, y)).2) = _
    rw [hc]
  have heiq (t : ℝ) (Y : E3) : e.symm (t, Y) =
      let w := T.symm Y
      let Z := (D.symm (t, w.2 - a)).2
      let z := Z / P.vertical w.1
      (t, heightCoordinates.symm ((reunionReflectedHorizontal P z)⁻¹ • w.1, z)) := by
    change (t, heightCoordinates.symm (A.symm
      ((B.symm (t, placement.symm (T.symm Y))).2))) = _
    simp only [placement, surgeryCapPlacementDiffeomorph_symm_apply, inv_one, one_mul, sub_zero]
    change (t, heightCoordinates.symm (A.symm
      ((T.symm Y).1, (D.symm (t, (T.symm Y).2 - a)).2))) = _
    simp only [A, flatCapDiffeomorph_symm_apply, div_eq_mul_inv, mul_comm]
  have hmodel : ContDiff ℝ ∞ (fun p : ℝ × E3 => M 1 (heightCoordinates p.2)) := by
    simp_rw [hM]
    exact A.contMDiff_toFun.contDiff.comp (heightCoordinates.contDiff.comp contDiff_snd)
  have hcoords : ContDiff ℝ ∞ (fun p : ℝ × E3 =>
      ((M 1 (heightCoordinates p.2)).1,
        a + reunionAxialHeight a lambda ε p.1 (M 1 (heightCoordinates p.2)).2)) :=
    hmodel.fst.prodMk (contDiff_const.add (hg.comp (contDiff_fst.prodMk hmodel.snd)))
  have he : ContDiffOn ℝ ∞ e e.source := by
    have hf : ContDiffOn ℝ ∞ (fun p : ℝ × E3 =>
        T ((M 1 (heightCoordinates p.2)).1,
          a + reunionAxialHeight a lambda ε p.1 (M 1 (heightCoordinates p.2)).2)) e.source :=
      hT.comp hcoords.contDiffOn (fun p hp => by rwa [hesource] at hp)
    apply (contDiff_fst.contDiffOn.prodMk hf).congr
    intro p _hp
    exact heq p.1 p.2
  have hTubeInv : ContDiffOn ℝ ∞ (fun p : ℝ × E3 => T.symm p.2) e.target :=
    hTi.comp contDiff_snd.contDiffOn (fun p hp => by rw [hetarget] at hp; exact hp.2)
  have hZ : ContDiffOn ℝ ∞
      (fun p : ℝ × E3 => (D.symm (p.1, (T.symm p.2).2 - a)).2) e.target :=
    ((D.symm.contMDiff_toFun.contDiff).comp_contDiffOn
      (contDiff_fst.contDiffOn.prodMk (hTubeInv.snd.sub contDiff_const.contDiffOn))).snd
  have hz : ContDiffOn ℝ ∞ (fun p : ℝ × E3 =>
      (D.symm (p.1, (T.symm p.2).2 - a)).2 / P.vertical (T.symm p.2).1) e.target :=
    hZ.div (P.vertical_smooth.comp_contDiffOn hTubeInv.fst)
      (fun p _hp => (P.vertical_pos _).ne')
  have hX := ((hA.comp_contDiffOn hz).inv (fun p _hp => (hApos _).ne')).smul hTubeInv.fst
  have hei : ContDiffOn ℝ ∞ e.symm e.target := by
    apply (contDiff_fst.contDiffOn.prodMk
      (heightCoordinates.symm.contDiff.comp_contDiffOn (hX.prodMk hz))).congr
    intro p _hp
    exact heiq p.1 p.2
  refine ⟨D, hD, e, hesource, hetarget, heq, heiq, he, hei, ?_⟩
  intro t q
  rw [hesource]
  exact hsource ⟨mem_closedBall_zero_iff.mpr ((reunion_reflected_model_spec P).2.1 1 q).1,
    mem_univ _⟩

end PoincareConjecture.M25.Topology3D
