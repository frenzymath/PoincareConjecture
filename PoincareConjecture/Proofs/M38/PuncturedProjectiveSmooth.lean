import PoincareConjecture.Proofs.M38.ProjectiveAtlas
import PoincareConjecture.Proofs.M38.ProjectiveCoverTopology









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

attribute [local instance] projectiveChartedSpace projective_isManifold projective_t2


def projectivePunctureOpen (p : RealProjectiveThree) :
    TopologicalSpace.Opens RealProjectiveThree :=
  ⟨{q | q ≠ p}, isOpen_ne_fun continuous_id continuous_const⟩

variable {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  {p : RealProjectiveThree} {U : Set Q}



theorem puncturedProjectiveCover_isOpen (C : StandardPuncturedProjectiveCover Q p U) :
    IsOpen U := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨x, hx, rfl⟩ := C.image_eq.symm.subset hy
  rw [← C.local_diffeomorph.isLocalHomeomorphOn.map_nhds_eq hx]
  change C.cover ⁻¹' U ∈ 𝓝 x
  apply Filter.mem_of_superset
    (((projectivePunctureOpen p).isOpen.preimage continuous_quotient_mk').mem_nhds hx)
  intro z hz
  exact C.image_eq.subset (Set.mem_image_of_mem C.cover hz)


def puncturedProjectiveCoverOpen (C : StandardPuncturedProjectiveCover Q p U) :
    TopologicalSpace.Opens Q := ⟨U, puncturedProjectiveCover_isOpen C⟩



theorem puncturedProjectiveCoverHomeomorph_contMDiff
    (C : StandardPuncturedProjectiveCover Q p U) :
    ContMDiff (M := projectivePunctureOpen p) (M' := puncturedProjectiveCoverOpen C)
      (𝓡 3) (𝓡 3) ∞
      (puncturedProjectiveCoverHomeomorph C :
        projectivePunctureOpen p → puncturedProjectiveCoverOpen C) := by
  apply (ContMDiff.subtypeVal_comp_iff (puncturedProjectiveCoverOpen C) _).mp
  intro z
  let x := projectiveRepresentative z.val
  let s := projective_quotient_localHomeomorph.localInverseAt x
  have hsz : z.val ∈ s.source := by
    rw [← projectiveRepresentative_spec z.val]
    exact projective_quotient_localHomeomorph.apply_self_mem_localInverseAt_source
  have hnon : (Quotient.mk' (s z.val) : RealProjectiveThree) ≠ p := by
    rw [projective_quotient_localHomeomorph.apply_localInverseAt_of_mem hsz]
    exact z.property
  have hs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ s z.val :=
    (projective_sheet_contMDiffOn x).contMDiffAt (s.open_source.mem_nhds hsz)
  have hsub : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : projectivePunctureOpen p → RealProjectiveThree) := contMDiff_subtype_val
  have hc := (C.local_diffeomorph ⟨s z.val, hnon⟩).contMDiffAt
  apply (hc.comp z (hs.comp z (hsub z))).congr_of_eventuallyEq
  filter_upwards [(s.open_source.preimage hsub.continuous).mem_nhds hsz] with w hw
  have hq : (Quotient.mk' (s w.val) : RealProjectiveThree) = w.val :=
    projective_quotient_localHomeomorph.apply_localInverseAt_of_mem hw
  have hn : (Quotient.mk' (s w.val) : RealProjectiveThree) ≠ p := by
    rw [hq]
    exact w.property
  have he : (⟨Quotient.mk' (s w.val), hn⟩ : PuncturedRealProjectiveThree p) = w :=
    Subtype.ext hq
  exact (congrArg (fun q => (puncturedProjectiveCoverHomeomorph C q).val) he).symm.trans
    (puncturedProjectiveCoverHomeomorph_apply C (s w.val) hn)



theorem puncturedProjectiveCoverHomeomorph_symm_contMDiff
    (C : StandardPuncturedProjectiveCover Q p U) :
    ContMDiff (M := puncturedProjectiveCoverOpen C) (M' := projectivePunctureOpen p)
      (𝓡 3) (𝓡 3) ∞
      ((puncturedProjectiveCoverHomeomorph C).symm :
        puncturedProjectiveCoverOpen C → projectivePunctureOpen p) := by
  apply (ContMDiff.subtypeVal_comp_iff (projectivePunctureOpen p) _).mp
  intro y
  obtain ⟨x, hx, hxy⟩ := C.image_eq.symm.subset y.property
  let hlocal := C.local_diffeomorph ⟨x, hx⟩
  let s := hlocal.localInverse
  have hy : y.val ∈ s.source := hxy ▸ hlocal.localInverse_mem_source
  have hsy : s y.val = x := by
    rw [← hxy]
    exact hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  have hs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ s y.val :=
    hlocal.contmdiffOn_localInverse.contMDiffAt (s.open_source.mem_nhds hy)
  have hsub : ContMDiff (𝓡 3) (𝓡 3) ∞
      (Subtype.val : puncturedProjectiveCoverOpen C → Q) := contMDiff_subtype_val
  have hcomp := (projective_quotient_contMDiff (s y.val)).comp y (hs.comp y (hsub y))
  have hne : (Quotient.mk' (s y.val) : RealProjectiveThree) ≠ p := by
    rw [hsy]
    exact hx
  have hev := (hcomp.continuousAt.ne_iff_eventually_ne continuous_const.continuousAt).mp hne
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [(s.open_source.preimage hsub.continuous).mem_nhds hy, hev] with z hz hn
  have he : puncturedProjectiveCoverHomeomorph C ⟨Quotient.mk' (s z.val), hn⟩ = z := by
    apply Subtype.ext
    exact (puncturedProjectiveCoverHomeomorph_apply C (s z.val) hn).trans
      (hlocal.localInverse_right_inv hz)
  have hi := congrArg (puncturedProjectiveCoverHomeomorph C).symm he
  rw [Homeomorph.symm_apply_apply] at hi
  exact (congrArg Subtype.val hi).symm


noncomputable def puncturedProjectiveCoverDiffeomorph
    (C : StandardPuncturedProjectiveCover Q p U) :
    (projectivePunctureOpen p) ≃ₘ^∞⟮𝓡 3, 𝓡 3⟯ (puncturedProjectiveCoverOpen C) where
  toEquiv := (puncturedProjectiveCoverHomeomorph C).toEquiv
  contMDiff_toFun := puncturedProjectiveCoverHomeomorph_contMDiff C
  contMDiff_invFun := puncturedProjectiveCoverHomeomorph_symm_contMDiff C



theorem puncturedProjectiveCoverDiffeomorph_apply
    (C : StandardPuncturedProjectiveCover Q p U)
    (x : UnitThreeSphere) (hx : Quotient.mk' x ≠ p) :
    (puncturedProjectiveCoverDiffeomorph C ⟨Quotient.mk' x, hx⟩).val = C.cover x :=
  puncturedProjectiveCoverHomeomorph_apply C x hx

end PoincareConjecture.M38
