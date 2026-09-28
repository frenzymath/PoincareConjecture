import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Germ.Angular
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Orientation









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare

open PoincareConjecture

local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem exists_extension_of_smooth_fixing_zero
    (f : RoundCylinderSpace → RoundCylinderSpace)
    (hf : ContMDiff CylModel CylModel ∞ f)
    (hzero : ∀ q : UnitTwoSphere, f (q, 0) = (q, 0))
    (hinj : ∀ q : UnitTwoSphere,
      Function.Injective (mfderiv CylModel CylModel f (q, 0))) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : Diffeomorph CylModel CylModel
        RoundCylinderSpace RoundCylinderSpace ∞,
      ∀ p : RoundCylinderSpace, |p.2| < r → F p = f p := by
  obtain ⟨R, hR, D, hDheight, hDagree⟩ := exists_angular_extension_of_fixing_zero f hf hzero
  obtain ⟨r, hr, _, σ, hσ, hσbound, hσinner⟩ := exists_smooth_height_retraction hR
  have hDinvheight (p : RoundCylinderSpace) : (D.symm p).2 = p.2 := by
    simpa only [D.apply_symm_apply] using (hDheight (D.symm p)).symm
  let S : RoundCylinderSpace → RoundCylinderSpace := fun p => (p.1, σ p.2)
  have hS : ContMDiff CylModel CylModel ∞ S :=
    contMDiff_fst.prodMk (hσ.contMDiff.comp contMDiff_snd)
  let G : RoundCylinderSpace → RoundCylinderSpace := fun p => f (D.symm (S p))
  have hG : ContMDiff CylModel CylModel ∞ G := hf.comp (D.symm.contMDiff.comp hS)
  have hGfst (p : RoundCylinderSpace) : (G p).1 = p.1 := by
    have hh := hDagree (D.symm (S p))
      (by rw [hDinvheight]; exact hσbound p.2)
    rw [D.apply_symm_apply] at hh
    exact hh.symm
  have hGagree (p : RoundCylinderSpace) (hp : |p.2| < r) : G p = f (D.symm p) := by
    change f (D.symm (p.1, σ p.2)) = f (D.symm p)
    rw [hσinner p.2 hp]
  have hGinj (q : UnitTwoSphere) :
      Function.Injective (mfderiv CylModel CylModel G (q, 0)) := by
    have heq : G =ᶠ[𝓝 (q, (0 : ℝ))] f ∘ D.symm := by
      have hn : {p : RoundCylinderSpace | |p.2| < r} ∈ 𝓝 (q, (0 : ℝ)) :=
        (isOpen_lt continuous_snd.abs continuous_const).mem_nhds (by simpa using hr)
      filter_upwards [hn] with p hp using hGagree p hp
    rw [heq.mfderiv_eq, mfderiv_comp (q, (0 : ℝ))
      (hf.mdifferentiableAt (by simp)) (D.symm.contMDiff.mdifferentiableAt (by simp))]
    have hp : D.symm (q, 0) = ((D.symm (q, 0)).1, 0) :=
      Prod.ext rfl (hDinvheight (q, 0))
    have hfi : Function.Injective (mfderiv CylModel CylModel f (D.symm (q, 0))) := by
      rw [hp]
      exact hinj _
    exact hfi.comp ((D.symm.mfderivToContinuousLinearEquiv (by simp) (q, 0)).injective)
  obtain ⟨a, K, ha, _, hK⟩ := CylinderGluing.exists_scalar_collar_extension_of_nonzero
    (fun p => (G p).2) (contMDiff_snd.comp hG)
    (fun q => CylinderGluing.axial_deriv_ne_zero_of_mfderiv_injective
      G hG hGfst (q, 0) (hGinj q))
  refine ⟨min r a, lt_min hr ha, D.trans K, ?_⟩
  intro p hp
  have hpr : |p.2| < r := hp.trans_le (min_le_left r a)
  have hpa : |p.2| < a := hp.trans_le (min_le_right r a)
  have hKp := hK (D p).1 p.2 hpa
  have hpair : ((D p).1, p.2) = D p := Prod.ext rfl (hDheight p).symm
  rw [hpair] at hKp
  have hGp : G (D p) = f p := by
    rw [hGagree (D p) (by rw [hDheight]; exact hpr), D.symm_apply_apply]
  change K (D p) = f p
  rw [hKp]
  have hpairG : ((D p).1, (G (D p)).2) = G (D p) :=
    Prod.ext (hGfst (D p)).symm rfl
  exact hpairG.trans hGp



theorem exists_cylinder_collar_extension_of_fixing_zero
    {δ : ℝ} (hδ : 0 < δ)
    (c : OpenPartialHomeomorph RoundCylinderSpace RoundCylinderSpace)
    (hsource : (univ : Set UnitTwoSphere) ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hc : ContMDiffOn CylModel CylModel ∞ c c.source)
    (hci : ContMDiffOn CylModel CylModel ∞ c.symm c.target)
    (hzero : ∀ q : UnitTwoSphere, c (q, 0) = (q, 0)) :
    ∃ η : ℝ, 0 < η ∧ η < δ ∧
      ∃ F : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞,
        ∀ p : RoundCylinderSpace, |p.2| < η → F p = c p := by
  obtain ⟨r, hr, hrδ, σ, hσ, hσbound, hσinner⟩ := exists_smooth_height_retraction hδ
  let S : RoundCylinderSpace → RoundCylinderSpace := fun p => (p.1, σ p.2)
  have hS : ContMDiff CylModel CylModel ∞ S :=
    contMDiff_fst.prodMk (hσ.contMDiff.comp contMDiff_snd)
  have hSmem (p : RoundCylinderSpace) : S p ∈ c.source :=
    hsource ⟨mem_univ _, abs_lt.mp (hσbound p.2)⟩
  let f : RoundCylinderSpace → RoundCylinderSpace := fun p => c (S p)
  have hf : ContMDiff CylModel CylModel ∞ f := by
    intro p
    exact (hc.contMDiffAt (c.open_source.mem_nhds (hSmem p))).comp p hS.contMDiffAt
  have hfagree (p : RoundCylinderSpace) (hp : |p.2| < r) : f p = c p := by
    change c (p.1, σ p.2) = c p
    rw [hσinner p.2 hp]
  have hfzero (q : UnitTwoSphere) : f (q, 0) = (q, 0) :=
    (hfagree (q, 0) (by simpa using hr)).trans (hzero q)
  have hfinj (q : UnitTwoSphere) :
      Function.Injective (mfderiv CylModel CylModel f (q, 0)) := by
    have hmem : (q, (0 : ℝ)) ∈ c.source :=
      hsource ⟨mem_univ _, by constructor <;> linarith⟩
    have hfc : f =ᶠ[𝓝 (q, (0 : ℝ))] c := by
      have hn : {p : RoundCylinderSpace | |p.2| < r} ∈ 𝓝 (q, (0 : ℝ)) :=
        (isOpen_lt continuous_snd.abs continuous_const).mem_nhds (by simpa using hr)
      filter_upwards [hn] with p hp using hfagree p hp
    rw [hfc.mfderiv_eq]
    have hh := mfderiv_comp (q, (0 : ℝ))
      ((hci.contMDiffAt (c.open_target.mem_nhds (c.map_source hmem))).mdifferentiableAt
        (by simp))
      ((hc.contMDiffAt (c.open_source.mem_nhds hmem)).mdifferentiableAt (by simp))
    have heq : c.symm ∘ c =ᶠ[𝓝 (q, (0 : ℝ))] id := by
      filter_upwards [c.open_source.mem_nhds hmem] with p hp using c.left_inv hp
    rw [heq.mfderiv_eq, mfderiv_id] at hh
    have hleft (v : TangentSpace CylModel (q, (0 : ℝ))) :
        mfderiv CylModel CylModel c.symm (c (q, 0))
          (mfderiv CylModel CylModel c (q, 0) v) = v :=
      (congrArg (fun L => L v) hh).symm
    intro v w hvw
    exact (hleft v).symm.trans
      ((congrArg (mfderiv CylModel CylModel c.symm (c (q, 0))) hvw).trans (hleft w))
  obtain ⟨a, ha, F, hF⟩ := exists_extension_of_smooth_fixing_zero f hf hfzero hfinj
  refine ⟨min a r, lt_min ha hr, (min_le_right a r).trans_lt hrδ, F, ?_⟩
  intro p hp
  exact (hF p (hp.trans_le (min_le_left a r))).trans
    (hfagree p (hp.trans_le (min_le_right a r)))

end Poincare
