import PoincareConjecture.Proofs.M38.MonodromyCylinder









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

attribute [local instance] monodromyChartedSpace monodromy_isManifold

local notation "mq" => (Quotient.mk (monodromyOrbitRel phi) :
  monodromyPunctureOpen → MonodromyQuotient phi)


def monodromyZeroFiber : Set (MonodromyQuotient phi) :=
  monodromyProjection phi ⁻¹' {circlePeriodMap 0}


theorem monodromyZeroFiber_range :
    Set.range (fun z : UnitTwoSphere => monodromyCylinder phi (z, 0)) =
      monodromyZeroFiber phi := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact monodromyCylinder_projection phi (z, 0)
  · intro hq
    let x := monodromyNormalize phi 0 q
    have hlog : monodromyLogRadius x = 0 :=
      monodromyNormalize_logRadius phi 0 q hq
    refine ⟨capUnitDirection x.val, ?_⟩
    change mq (monodromyPolarPoint (capUnitDirection x.val, 0)) = q
    rw [← hlog, monodromyPolarPoint_reconstruct]
    exact monodromyNormalize_quotient phi 0 q


theorem monodromy_unit_strip_complement :
    monodromyCylinder phi '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) =
      (monodromyZeroFiber phi)ᶜ := by
  rw [monodromy_unit_strip_image]
  ext q
  simp [monodromyZeroFiber]



noncomputable def monodromyCutHomeomorph :
    (UnitTwoSphere × Set.Ioo (0 : ℝ) 1) ≃ₜ ↥((monodromyZeroFiber phi)ᶜ) := by
  let e := (monodromyStripChart phi 0 1 (by norm_num)).toOpenPartialHomeomorph
  exact ((Homeomorph.prodCongr (Homeomorph.Set.univ UnitTwoSphere).symm
    (Homeomorph.refl (Set.Ioo (0 : ℝ) 1))).trans
      (Homeomorph.Set.prod (Set.univ : Set UnitTwoSphere) (Set.Ioo (0 : ℝ) 1)).symm).trans
    (e.toHomeomorphSourceTarget.trans (Homeomorph.setCongr (monodromy_unit_strip_complement phi)))



noncomputable def monodromyCutCylinder : OpenCylinderModel (monodromyZeroFiber phi)ᶜ where
  homeomorph := monodromyCutHomeomorph phi
  coordinate := monodromyCylinder phi
  coordinate_eq := fun _ => rfl
  coordinate_smooth := (monodromyCylinder_localDiffeomorph phi).contMDiff.contMDiffOn
  inverse := monodromyStripInverse phi 0 1
  inverse_mem := fun _ hq => monodromyStripInverse_mem phi 0 1
    ((monodromy_unit_strip_complement phi).symm ▸ hq)
  left_inverse := monodromyStripInverse_left phi 0 1 (by norm_num)
  right_inverse := by
    rw [← monodromy_unit_strip_complement phi]
    exact monodromyStripInverse_right phi 0 1
  inverse_smooth := by
    rw [← monodromy_unit_strip_complement phi]
    exact monodromyStripInverse_smooth phi 0 1 (by norm_num)


theorem monodromyZeroFiber_complement_connected : IsConnected (monodromyZeroFiber phi)ᶜ := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : StandardCapSpace) (zero_le_one : (0 : ℝ) ≤ 1))
  rw [← monodromy_unit_strip_complement phi]
  exact (isConnected_univ.prod (isConnected_Ioo zero_lt_one)).image _
    (monodromyCylinder_localDiffeomorph phi).contMDiff.continuous.continuousOn


theorem monodromyZeroFiber_nonseparating : NonseparatingSphere (monodromyZeroFiber phi) := by
  change IsConnected (Set.univ \ monodromyZeroFiber phi)
  rw [← Set.compl_eq_univ_sdiff]
  exact monodromyZeroFiber_complement_connected phi

end PoincareConjecture.M38
