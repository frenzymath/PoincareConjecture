import PoincareConjecture.Proofs.M38.MonodromyFiber
import PoincareConjecture.Proofs.M38.TwoChartComparison
import PoincareConjecture.Proofs.M38.CylinderRegionTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

attribute [local instance] monodromyChartedSpace monodromy_isManifold
  monodromyLiftChartedSpace monodromy_lift_isManifold

noncomputable def monodromyLiftedCylinder (z : RoundCylinderSpace) :
    (monodromyCarrier.{u} phi).carrier :=
  ULift.up (monodromyCylinder phi z)

def monodromyLiftedZeroFiber : Set (monodromyCarrier.{u} phi).carrier :=
  ULift.down ⁻¹' monodromyZeroFiber phi

theorem monodromyLiftedCylinder_smooth :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (monodromyLiftedCylinder.{u} phi) :=
  (monodromy_up_contMDiff phi).comp (monodromyCylinder_localDiffeomorph phi).contMDiff

noncomputable def monodromyLiftedCollar (a : ℝ) (hwidth : 2 * a ≤ 1) :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace
      (monodromyCarrier.{u} phi).carrier ∞ where
  toFun := monodromyLiftedCylinder phi
  invFun q := monodromyStripInverse phi (-a) a q.down
  source := Set.univ ×ˢ Set.Ioo (-a) a
  target := ULift.down ⁻¹' (monodromyCylinder phi '' (Set.univ ×ˢ Set.Ioo (-a) a))
  map_source' := fun _ hz => Set.mem_image_of_mem _ hz
  map_target' := fun {_} hq => monodromyStripInverse_mem phi (-a) a hq
  left_inv' := monodromyStripInverse_left phi (-a) a (by linarith)
  right_inv' := fun _ hq => ULift.ext _ _ (monodromyStripInverse_right phi (-a) a hq)
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := ((monodromyStripChart phi (-a) a (by linarith)).open_target).preimage
    continuous_uliftDown
  contMDiffOn_toFun := (monodromyLiftedCylinder_smooth phi).contMDiffOn
  contMDiffOn_invFun := (monodromyStripInverse_smooth phi (-a) a (by linarith)).comp
    (monodromy_down_contMDiff phi).contMDiffOn (fun _ hq => hq)

theorem monodromyLiftedCollar_source (a : ℝ) (hwidth : 2 * a ≤ 1) :
    (monodromyLiftedCollar.{u} phi a hwidth).source =
      Set.univ ×ˢ Set.Ioo (-a) a := rfl

theorem monodromyLiftedCollar_apply (a : ℝ) (hwidth : 2 * a ≤ 1)
    (z : RoundCylinderSpace) :
    monodromyLiftedCollar.{u} phi a hwidth z = ULift.up (monodromyCylinder phi z) := rfl

theorem monodromyLiftedCollar_inverse (a : ℝ) (hwidth : 2 * a ≤ 1)
    (q : (monodromyCarrier.{u} phi).carrier) :
    (monodromyLiftedCollar phi a hwidth).symm q =
      monodromyStripInverse phi (-a) a q.down := rfl

theorem monodromyLiftedCollar_central (a : ℝ) (hwidth : 2 * a ≤ 1) :
    comparisonCentralSphere (monodromyLiftedCollar.{u} phi a hwidth) =
      monodromyLiftedZeroFiber phi := by
  change monodromyLiftedCylinder phi '' (Set.univ ×ˢ ({0} : Set ℝ)) = _
  ext q
  constructor
  · rintro ⟨z, hz, hq⟩
    change q.down ∈ monodromyZeroFiber phi
    rw [← monodromyZeroFiber_range]
    refine ⟨z.1, ?_⟩
    have hz0 : z.2 = 0 := hz.2
    have hdown := congrArg ULift.down hq
    change monodromyCylinder phi (z.1, z.2) = q.down at hdown
    simpa only [hz0] using hdown
  · intro hq
    change q.down ∈ monodromyZeroFiber phi at hq
    rw [← monodromyZeroFiber_range] at hq
    obtain ⟨z, hz⟩ := hq
    exact ⟨(z, 0), ⟨Set.mem_univ _, rfl⟩, ULift.ext _ _ hz⟩

theorem monodromyLiftedCylinder_unit_image :
    monodromyLiftedCylinder.{u} phi '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) =
      (monodromyLiftedZeroFiber phi)ᶜ := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    change monodromyCylinder phi z ∈ (monodromyZeroFiber phi)ᶜ
    rw [← monodromy_unit_strip_complement]
    exact ⟨z, hz, rfl⟩
  · intro hq
    change q.down ∈ (monodromyZeroFiber phi)ᶜ at hq
    rw [← monodromy_unit_strip_complement] at hq
    obtain ⟨z, hz, heq⟩ := hq
    exact ⟨z, hz, ULift.ext _ _ heq⟩

theorem monodromyLiftedStripInverse_mem (q : (monodromyCarrier.{u} phi).carrier)
    (hq : q ∈ (monodromyLiftedZeroFiber phi)ᶜ) :
    monodromyStripInverse phi 0 1 q.down ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1 := by
  apply monodromyStripInverse_mem phi 0 1
  rw [monodromy_unit_strip_complement]
  exact hq

noncomputable def monodromyCylinderRegionEquivalence
    {A : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} (C : OpenCylinderModel U) :
    SurgeryRegionEquivalence A (monodromyCarrier.{u} phi) U
      (monodromyLiftedZeroFiber phi)ᶜ := by
  let f : A.carrier → (monodromyCarrier phi).carrier :=
    fun x => monodromyLiftedCylinder phi (C.inverse x)
  let g : (monodromyCarrier phi).carrier → A.carrier :=
    fun y => C.coordinate (monodromyStripInverse phi 0 1 y.down)
  have hfmem : Set.MapsTo f U (monodromyLiftedZeroFiber phi)ᶜ := by
    intro x hx
    rw [← monodromyLiftedCylinder_unit_image]
    exact ⟨C.inverse x, C.inverse_mem x hx, rfl⟩
  have hgmem : Set.MapsTo g (monodromyLiftedZeroFiber phi)ᶜ U :=
    fun y hy => cylinderCoordinate_mem C (monodromyLiftedStripInverse_mem phi y hy)
  have hleft : Set.LeftInvOn g f U := by
    intro x hx
    change C.coordinate (monodromyStripInverse phi 0 1
      (monodromyCylinder phi (C.inverse x))) = x
    rw [monodromyStripInverse_left phi 0 1 (by norm_num) (C.inverse_mem x hx),
      C.right_inverse hx]
  have hright : Set.LeftInvOn f g (monodromyLiftedZeroFiber phi)ᶜ := by
    intro y hy
    apply ULift.ext
    change monodromyCylinder phi (C.inverse
      (C.coordinate (monodromyStripInverse phi 0 1 y.down))) = y.down
    rw [C.left_inverse (monodromyLiftedStripInverse_mem phi y hy)]
    apply monodromyStripInverse_right phi 0 1
    rw [monodromy_unit_strip_complement]
    exact hy
  exact {
    map := f
    inverse := g
    map_image := Set.Subset.antisymm (Set.image_subset_iff.mpr hfmem)
      (fun y hy => ⟨g y, hgmem hy, hright hy⟩)
    inverse_image := Set.Subset.antisymm (Set.image_subset_iff.mpr hgmem)
      (fun x hx => ⟨f x, hfmem hx, hleft hx⟩)
    left_inverse := hleft
    right_inverse := hright
    map_smooth := (monodromyLiftedCylinder_smooth phi).comp_contMDiffOn C.inverse_smooth
    inverse_smooth := C.coordinate_smooth.comp
      ((monodromyStripInverse_smooth phi 0 1 (by norm_num)).comp
        (monodromy_down_contMDiff phi).contMDiffOn (fun y hy => by
          rw [monodromy_unit_strip_complement]
          exact hy))
      (fun y hy => monodromyLiftedStripInverse_mem phi y hy) }

theorem monodromyCylinderRegionEquivalence_map
    {A : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} (C : OpenCylinderModel U)
    (x : A.carrier) :
    (monodromyCylinderRegionEquivalence phi C).map x =
      monodromyLiftedCylinder phi (C.inverse x) := rfl

theorem monodromyCylinderRegionEquivalence_inverse
    {A : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} (C : OpenCylinderModel U)
    (y : (monodromyCarrier.{u} phi).carrier) :
    (monodromyCylinderRegionEquivalence phi C).inverse y =
      C.coordinate (monodromyStripInverse phi 0 1 y.down) := rfl

theorem monodromyCylinderRegionEquivalence_coordinate
    {A : GeneralizedSliceCarrier.{u}} {U : Set A.carrier} (C : OpenCylinderModel U)
    {z : RoundCylinderSpace} (hz : z ∈ Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) :
    (monodromyCylinderRegionEquivalence phi C).map (C.coordinate z) =
      monodromyLiftedCylinder phi z := by
  rw [monodromyCylinderRegionEquivalence_map, C.left_inverse hz]

end PoincareConjecture.M38
