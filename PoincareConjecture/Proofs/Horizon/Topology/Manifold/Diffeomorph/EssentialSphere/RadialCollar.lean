import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Fibration.Quotient.Collars.Extension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare

open PoincareConjecture

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

def radialPartialDiffeomorph :
    PartialDiffeomorph CylModel (𝓡 3) RoundCylinderSpace E3 ∞ := by
  let : Nonempty UnitTwoSphere :=
    (NormedSpace.sphere_nonempty.mpr (zero_le_one : (0 : ℝ) ≤ 1)).coe_sort
  let : Nonempty puncturedThreeSpace :=
    ⟨sphereCylinderDiffeomorphPunctured (Classical.choice inferInstance, 0)⟩
  let e := puncturedThreeSpace.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) puncturedThreeSpace E3 ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := by
      intro y hy
      apply (ContMDiffWithinAt.subtypeVal_comp_iff puncturedThreeSpace e.symm e.target y).mp
      apply contMDiffWithinAt_id.congr
      · intro z hz
        exact e.right_inv hz
      · exact e.right_inv hy }
  exact sphereCylinderDiffeomorphPunctured.toPartialDiffeomorph.trans d

@[simp] theorem radialPartialDiffeomorph_apply (p : RoundCylinderSpace) :
    radialPartialDiffeomorph p = (sphereCylinderDiffeomorphPunctured p : E3) := rfl

@[simp] theorem radialPartialDiffeomorph_source : radialPartialDiffeomorph.source = univ := by
  ext p
  simp [radialPartialDiffeomorph, PartialDiffeomorph.trans,
    Diffeomorph.toPartialDiffeomorph]

@[simp] theorem radialPartialDiffeomorph_target :
    radialPartialDiffeomorph.target = {0}ᶜ := by
  ext p
  simp [radialPartialDiffeomorph, PartialDiffeomorph.trans,
    Diffeomorph.toPartialDiffeomorph, puncturedThreeSpace,
    PartialDiffeomorph.toOpenPartialHomeomorph]

theorem exists_supported_radial_collar_transition
    (c : OpenPartialHomeomorph RoundCylinderSpace E3)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hsource : (univ : Set UnitTwoSphere) ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hzero : ∀ q : UnitTwoSphere, c (q, 0) = (q : E3))
    (hpositive : ∀ (q : UnitTwoSphere) (t : ℝ), 0 < t → t < δ → 1 < ‖c (q, t)‖)
    (R : ℝ) (hR : 0 < R) :
    ∃ (η : ℝ) (D : Diffeomorph CylModel CylModel
        RoundCylinderSpace RoundCylinderSpace ∞),
      0 < η ∧ η < δ ∧ η < R ∧
      (∀ p, |p.2| < η → (sphereCylinderDiffeomorphPunctured (D p) : E3) = c p) ∧
      (∀ p, R ≤ |p.2| → D p = p) := by
  let C : PartialDiffeomorph CylModel (𝓡 3) RoundCylinderSpace E3 ∞ := {
    toPartialEquiv := c.toPartialEquiv
    open_source := c.open_source
    open_target := c.open_target
    contMDiffOn_toFun := hc
    contMDiffOn_invFun := hci }
  let d := C.trans radialPartialDiffeomorph.symm
  have hczero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ c.source :=
    hsource ⟨mem_univ _, by constructor <;> linarith⟩
  have hdsource (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ d.source := by
    refine ⟨hczero q, ?_⟩
    change c (q, 0) ∈ radialPartialDiffeomorph.target
    rw [radialPartialDiffeomorph_target, hzero]
    exact ne_zero_of_mem_unit_sphere q
  have hdapply (p : RoundCylinderSpace) : d p = radialPartialDiffeomorph.symm (c p) := rfl
  have hd0 (q : UnitTwoSphere) : d (q, 0) = (q, 0) := by
    rw [hdapply, hzero]
    have hh := radialPartialDiffeomorph.toPartialEquiv.left_inv
      (show (q, (0 : ℝ)) ∈ radialPartialDiffeomorph.source by simp)
    change radialPartialDiffeomorph.symm (radialPartialDiffeomorph (q, 0)) = (q, 0) at hh
    rw [radialPartialDiffeomorph_apply, sphereCylinderDiffeomorphPunctured_zero] at hh
    exact hh
  have hnorm (p : RoundCylinderSpace) (hp : p ∈ d.source) :
      Real.exp (d p).2 = ‖c p‖ := by
    have hi := radialPartialDiffeomorph.toPartialEquiv.right_inv hp.2
    change radialPartialDiffeomorph (radialPartialDiffeomorph.symm (c p)) = c p at hi
    rw [← hdapply] at hi
    have hn := congrArg norm hi
    simpa [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hn
  have hdpos (q : UnitTwoSphere) : 0 < deriv (fun t : ℝ => (d (q, t)).2) 0 := by
    apply CylinderGluing.axial_deriv_pos_of_zero_sphere_localDiffeomorph d
      (fun q => congrArg Prod.snd (hd0 q)) q
      (d.isLocalDiffeomorphAt _ _ _ (hdsource q)) hδ
    intro t ht htδ
    have hp : (q, t) ∈ d.source := by
      refine ⟨hsource ⟨mem_univ _, by constructor <;> linarith⟩, ?_⟩
      change c (q, t) ∈ radialPartialDiffeomorph.target
      rw [radialPartialDiffeomorph_target]
      exact norm_pos_iff.mp (zero_lt_one.trans (hpositive q t ht htδ))
    apply (Real.exp_lt_exp).mp
    rw [Real.exp_zero, hnorm (q, t) hp]
    exact hpositive q t ht htδ
  obtain ⟨r, D, hr, hrR, hlocal, hout⟩ :=
    CylinderGluing.exists_supported_collar_germ_extension d d.source d.open_source
      d.contMDiffOn (Diffeomorph.refl _ _ _) hdsource hd0 hdpos R hR
  refine ⟨min r (δ / 2), D, lt_min hr (half_pos hδ),
    (min_le_right _ _).trans_lt (half_lt_self hδ),
    (min_le_left _ _).trans_lt hrR, ?_, ?_⟩
  · intro p hp
    obtain ⟨hs, heq⟩ := hlocal p (hp.trans_le (min_le_left _ _))
    rw [heq]
    exact radialPartialDiffeomorph.toPartialEquiv.right_inv hs.2
  · intro p hp
    exact hout p hp

end Poincare
