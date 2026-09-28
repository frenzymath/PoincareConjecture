import PoincareConjecture.Proofs.M25.Topology3D.Space3.CircleRadialChart












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_stackCircleRadialChart
    (E : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hE : ContDiffOn ℝ ∞ E E.source)
    (hEi : ContDiffOn ℝ ∞ E.symm E.target)
    (hEh : ∀ p ∈ E.source, (E p).1 = p.1)
    (hEs : univ ×ˢ sphere (0 : E2) 1 ⊆ E.source)
    (hEt : univ ×ˢ sphere (0 : E2) 1 ⊆ E.target)
    (hEC : MapsTo E (univ ×ˢ sphere (0 : E2) 1)
      (univ ×ˢ sphere (0 : E2) 1))
    (hEiC : MapsTo E.symm (univ ×ˢ sphere (0 : E2) 1)
      (univ ×ˢ sphere (0 : E2) 1)) :
    ∃ R : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2),
      R.source = univ ×ˢ ({0}ᶜ : Set E2) ∧
      R.target = univ ×ˢ ({0}ᶜ : Set E2) ∧
      (∀ p, R p = (p.1, ‖p.2‖ •
        (E (p.1, (circleDirection p.2 : E2))).2)) ∧
      (∀ p, R.symm p = (p.1, ‖p.2‖ •
        (E.symm (p.1, (circleDirection p.2 : E2))).2)) ∧
      ContDiffOn ℝ ∞ R R.source ∧
      ContDiffOn ℝ ∞ R.symm R.target ∧
      (∀ p, (R p).1 = p.1 ∧ (R.symm p).1 = p.1) ∧
      (∀ p, ‖(R p).2‖ = ‖p.2‖ ∧ ‖(R.symm p).2‖ = ‖p.2‖) ∧
      ∀ p ∈ univ ×ˢ sphere (0 : E2) 1,
        R p = E p ∧ R.symm p = E.symm p := by
  let C : Set (ℝ × E2) := univ ×ˢ sphere (0 : E2) 1
  let U : Set (ℝ × E2) := univ ×ˢ ({0}ᶜ : Set E2)
  let radial (V : (ℝ × E2) → ℝ × E2) (p : ℝ × E2) : ℝ × E2 :=
    (p.1, ‖p.2‖ • (V (p.1, (circleDirection p.2 : E2))).2)
  have hdirection (p : ℝ × E2) : (p.1, (circleDirection p.2 : E2)) ∈ C :=
    ⟨mem_univ _, (circleDirection p.2).2⟩
  have hnorm (V : (ℝ × E2) → ℝ × E2) (hVC : MapsTo V C C) (p : ℝ × E2) :
      ‖(radial V p).2‖ = ‖p.2‖ := by
    have hv := mem_sphere_zero_iff_norm.mp (hVC (hdirection p)).2
    change ‖‖p.2‖ • (V (p.1, (circleDirection p.2 : E2))).2‖ = ‖p.2‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hv, mul_one]
  have hmaps (V : (ℝ × E2) → ℝ × E2) (hVC : MapsTo V C C) :
      MapsTo (radial V) U U := by
    intro p hp
    refine ⟨mem_univ _, ?_⟩
    exact norm_ne_zero_iff.mp ((hnorm V hVC p).trans_ne (norm_ne_zero_iff.mpr hp.2))
  have hEhInv (p : ℝ × E2) (hp : p ∈ E.target) : (E.symm p).1 = p.1 := by
    have hh := hEh (E.symm p) (E.map_target hp)
    rw [E.right_inv hp] at hh
    exact hh.symm
  have hinverse (V : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
      (hVs : C ⊆ V.source) (hVC : MapsTo V C C)
      (hVh : ∀ p ∈ V.source, (V p).1 = p.1)
      (p : ℝ × E2) (hp : p ∈ U) : radial V.symm (radial V p) = p := by
    let q : ℝ × E2 := (p.1, (circleDirection p.2 : E2))
    have hq : q ∈ V.source := hVs (hdirection p)
    have hv : (V q).2 ∈ sphere (0 : E2) 1 := (hVC (hdirection p)).2
    have hd : (circleDirection (radial V p).2 : E2) = (V q).2 := by
      exact congrArg (fun r : UnitCircle => (r : E2))
        (circleDirection_smul ⟨(V q).2, hv⟩ (norm_pos_iff.mpr hp.2))
    have hh : (p.1, (V q).2) = V q := Prod.ext (hVh q hq).symm rfl
    change (p.1, ‖(radial V p).2‖ •
      (V.symm (p.1, (circleDirection (radial V p).2 : E2))).2) = p
    rw [hnorm V hVC p, hd, hh, V.left_inv hq]
    exact Prod.ext rfl (circleDirection_norm_smul p.2)
  have hsmooth (V : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
      (hVs : C ⊆ V.source) (hV : ContDiffOn ℝ ∞ V V.source) :
      ContDiffOn ℝ ∞ (radial V) U := by
    have hn : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => ‖p.2‖) U := by
      intro p hp
      exact ((contDiffAt_norm ℝ (show p.2 ≠ 0 from hp.2)).comp
        p contDiffAt_snd).contDiffWithinAt
    have hd : ContDiffOn ℝ ∞
        (fun p : ℝ × E2 => (circleDirection p.2 : E2)) U := by
      have hi := hn.inv (fun p hp => norm_ne_zero_iff.mpr hp.2)
      exact (hi.smul contDiff_snd.contDiffOn).congr (by
        intro p hp
        exact circleDirection_coe hp.2)
    exact contDiff_fst.contDiffOn.prodMk
      (hn.smul ((hV.comp (contDiff_fst.contDiffOn.prodMk hd)
        (fun p _ => hVs (hdirection p))).snd))
  have hboundary (V : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
      (hVs : C ⊆ V.source) (hVh : ∀ p ∈ V.source, (V p).1 = p.1)
      (p : ℝ × E2) (hp : p ∈ C) : radial V p = V p := by
    have hdir : (circleDirection p.2 : E2) = p.2 :=
      congrArg (fun q : UnitCircle => (q : E2)) (circleDirection_coe_unit ⟨p.2, hp.2⟩)
    change (p.1, ‖p.2‖ • (V (p.1, (circleDirection p.2 : E2))).2) = V p
    rw [mem_sphere_zero_iff_norm.mp hp.2, hdir, one_smul]
    exact Prod.ext (hVh p (hVs hp)).symm rfl
  let R : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2) := {
    toFun := radial E
    invFun := radial E.symm
    source := U
    target := U
    map_source' := hmaps E hEC
    map_target' := hmaps E.symm hEiC
    left_inv' := hinverse E hEs hEC hEh
    right_inv' := hinverse E.symm hEt hEiC hEhInv
    open_source := isOpen_univ.prod isClosed_singleton.isOpen_compl
    open_target := isOpen_univ.prod isClosed_singleton.isOpen_compl
    continuousOn_toFun := (hsmooth E hEs hE).continuousOn
    continuousOn_invFun := (hsmooth E.symm hEt hEi).continuousOn }
  exact ⟨R, rfl, rfl, fun _ => rfl, fun _ => rfl,
    hsmooth E hEs hE, hsmooth E.symm hEt hEi, fun _ => ⟨rfl, rfl⟩,
    fun p => ⟨hnorm E hEC p, hnorm E.symm hEiC p⟩,
    fun p hp => ⟨hboundary E hEs hEh p hp, hboundary E.symm hEt hEhInv p hp⟩⟩

end PoincareConjecture.M25.Topology3D
