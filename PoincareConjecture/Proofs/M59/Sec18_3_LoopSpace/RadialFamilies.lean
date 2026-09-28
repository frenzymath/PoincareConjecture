import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.RadialHomotopy
import PoincareConjecture.Definitions.M59LoopIdentification

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u v

namespace PoincareConjecture

open Proofs.M58

theorem m59Annulus_ne_zero {z : LoopPlane} (hz : z ∈ loopAnnulus) : z ≠ 0 := by
  intro h
  have hpos := hz.1
  norm_num [h] at hpos

def m59AnnulusToCircle : C(loopAnnulus, LoopCircle) where
  toFun z := ⟨radialNormalization z.val, norm_radialNormalization (m59Annulus_ne_zero z.property)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (contDiffAt_radialNormalization (m59Annulus_ne_zero z.property)).continuousAt.comp
      continuous_subtype_val.continuousAt

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m59RadialFamily_joint_extension {B : Type v} [TopologicalSpace B]
    (F : B → C1FreeLoopSpace (M := M)) (hF : Continuous F) :
    ∃ extension : B × LoopPlane → M,
      ContinuousOn extension (univ ×ˢ loopAnnulus) ∧
      (∀ c (z : LoopCircle), extension (c, z.val) = m59RadialLoop (F c) z) ∧
      ∀ c, ContMDiffOn (𝓡 2) (𝓡 3) 1 (fun z => extension (c, z)) loopAnnulus := by
  refine ⟨fun p => (F p.1).extension (radialNormalization p.2), ?_, fun _ _ => rfl,
    fun c => contMDiffOn_radial_extension (F c)⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  let D := (univ : Set B) ×ˢ loopAnnulus
  have hparam : Continuous (fun p : D => (F p.val.1,
      m59AnnulusToCircle ⟨p.val.2, p.property.2⟩)) :=
    (hF.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (m59AnnulusToCircle.continuous.comp
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have h := continuous_loop_eval.comp hparam
  have heq : (fun p : D => (F p.val.1).extension (radialNormalization p.val.2)) =
      (fun p : D => F p.val.1 (m59AnnulusToCircle ⟨p.val.2, p.property.2⟩)) :=
    funext fun p => (F p.val.1).boundary (m59AnnulusToCircle ⟨p.val.2, p.property.2⟩)
  change Continuous (fun p : D => (F p.val.1).extension (radialNormalization p.val.2))
  rw [heq]
  exact h

theorem m59RadialLoop_null {gamma : C1FreeLoopSpace (M := M)}
    (hgamma : IsNullHomotopicLoop gamma) : IsNullHomotopicLoop (m59RadialLoop gamma) := by
  obtain ⟨F, hF, hboundary⟩ := hgamma
  exact ⟨F, hF, fun z => (hboundary z).trans (m59RadialLoop_apply gamma z).symm⟩

def m59RadialSphereFamily (q : M59SphereQuotient) (x : M)
    (F : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (hbase : F q.pole = constantC1Loop x) (hnull : ∀ c, IsNullHomotopicLoop (F c)) :
    FreeTwoSphereFamily (M := M) := by
  let g : GenLoop (Fin 2) (C1FreeLoopSpace (M := M)) (constantC1Loop x) :=
    ⟨m59RadialLoopMap.comp (F.comp q.map), fun z hz => by
      change m59RadialLoop (F (q.map z)) = constantC1Loop x
      rw [q.boundary_collapsed z hz, hbase, m59RadialLoop_constant]⟩
  exact {
    basepoint := x
    family := fun c => m59RadialLoop (F c)
    homotopy_class := Quotient.mk' g
    class_certificate := {
      cube_representative := g.val
      boundary_const := g.property
      sphere_parameter := q.map
      sphere_parameter_surjective := q.surjective
      sphere_parameter_boundary_collapsed := ⟨q.pole, q.boundary_collapsed⟩
      sphere_parameter_quotient_fiber := q.exact_fibers
      family_agreement := fun _ => rfl
      class_eq := rfl }
    continuous := continuous_m59RadialLoop.comp F.continuous
    derivative_continuous := continuous_m59RadialLoop_derivative F F.continuous
    null_homotopic := fun c => m59RadialLoop_null (hnull c)
    joint_extension := m59RadialFamily_joint_extension F F.continuous }

theorem m59RadialSphereFamily_normalized (q : M59SphereQuotient) (x : M)
    (F : C(LoopTwoSphere, C1FreeLoopSpace (M := M)))
    (hbase : F q.pole = constantC1Loop x) (hnull : ∀ c, IsNullHomotopicLoop (F c)) :
    M59NormalizedAt q x (m59RadialSphereFamily q x F hbase hnull) :=
  ⟨rfl, rfl⟩

end PoincareConjecture
