import PoincareConjecture.Proofs.M38.MonodromyLocalSheets









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

local notation "mq" => (Quotient.mk (monodromyOrbitRel phi) :
  monodromyPunctureOpen → MonodromyQuotient phi)


noncomputable def monodromyRepresentative : MonodromyQuotient phi → monodromyPunctureOpen :=
  Function.surjInv (monodromy_open_quotient phi).surjective


theorem monodromyRepresentative_spec (p : MonodromyQuotient phi) :
    mq (monodromyRepresentative phi p) = p :=
  Function.surjInv_eq (monodromy_open_quotient phi).surjective p


@[instance_reducible]
noncomputable def monodromyChartedSpace :
    ChartedSpace StandardCapSpace (MonodromyQuotient phi) :=
  (monodromy_quotient_localHomeomorph phi).chartedSpaceOfRightInverse
    (monodromyRepresentative_spec phi)


theorem monodromy_chart_transition_smooth (a b : monodromyPunctureOpen) :
    let e := ((monodromy_quotient_localHomeomorph phi).localInverseAt a).trans
      (chartAt StandardCapSpace a)
    let e' := ((monodromy_quotient_localHomeomorph phi).localInverseAt b).trans
      (chartAt StandardCapSpace b)
    ContDiffOn ℝ ∞ (e.symm.trans e') (e.symm.trans e').source := by
  let sa := (monodromy_quotient_localHomeomorph phi).localInverseAt a
  let sb := (monodromy_quotient_localHomeomorph phi).localInverseAt b
  let ca := chartAt StandardCapSpace a
  let cb := chartAt StandardCapSpace b
  let e := sa.trans ca
  let e' := sb.trans cb
  change ContDiffOn ℝ ∞ (e.symm.trans e') (e.symm.trans e').source
  apply ContMDiffOn.contDiffOn
  intro z hz
  have hz' : z ∈ ca.target ∧ ca.symm z ∈ sa.target ∧
      mq (ca.symm z) ∈ sb.source ∧ sb (mq (ca.symm z)) ∈ cb.source := by
    simpa only [e, e', OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.coe_trans_symm, sa, sb,
      (monodromy_quotient_localHomeomorph phi).localInverseAt_symm,
      Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply, and_assoc] using hz
  have hca : ContMDiffAt (𝓡 3) (𝓡 3) ∞ ca.symm z :=
    contMDiffOn_chart_symm.contMDiffAt (ca.open_target.mem_nhds hz'.1)
  have hsheet : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (sb ∘ mq) (ca.symm z) :=
    (monodromy_sheet_transition_smooth phi b).contMDiffAt
      ((sb.open_source.preimage (monodromy_open_quotient phi).continuous).mem_nhds hz'.2.2.1)
  have hcb : ContMDiffAt (𝓡 3) (𝓡 3) ∞ cb (sb (mq (ca.symm z))) :=
    contMDiffOn_chart.contMDiffAt (cb.open_source.mem_nhds hz'.2.2.2)
  have hcomp := (hcb.comp z (hsheet.comp z hca)).contMDiffWithinAt
    (s := (e.symm.trans e').source)
  simpa only [e, e', OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.coe_trans_symm, sa, sb,
    (monodromy_quotient_localHomeomorph phi).localInverseAt_symm, Function.comp_assoc]
    using hcomp


theorem monodromy_isManifold :
    letI := monodromyChartedSpace phi
    IsManifold (𝓡 3) ∞ (MonodromyQuotient phi) := by
  let := monodromyChartedSpace phi
  apply isManifold_of_contDiffOn (𝓡 3) ∞ (MonodromyQuotient phi)
  intro e e' he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨p', rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using monodromy_chart_transition_smooth phi
    (monodromyRepresentative phi p) (monodromyRepresentative phi p')

attribute [local instance] monodromyChartedSpace monodromy_isManifold


theorem monodromy_quotient_contMDiff : ContMDiff (𝓡 3) (𝓡 3) ∞ mq := by
  intro x
  apply contMDiffAt_iff_target.mpr
  refine ⟨(monodromy_open_quotient phi).continuous.continuousAt, ?_⟩
  let p : MonodromyQuotient phi := mq x
  let a := monodromyRepresentative phi p
  let s := (monodromy_quotient_localHomeomorph phi).localInverseAt a
  let c := chartAt StandardCapSpace a
  have hp : p ∈ s.source ∧ s p ∈ c.source := mem_chart_source StandardCapSpace p
  have hs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (s ∘ mq) x :=
    (monodromy_sheet_transition_smooth phi a).contMDiffAt
      ((s.open_source.preimage (monodromy_open_quotient phi).continuous).mem_nhds hp.1)
  have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c (s p) :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hp.2)
  change ContMDiffAt (𝓡 3) (𝓡 3) ∞ (c ∘ (s ∘ mq)) x
  exact hc.comp x hs



theorem monodromy_chosen_sheet_contMDiffAt (p : MonodromyQuotient phi) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞
      ((monodromy_quotient_localHomeomorph phi).localInverseAt
        (monodromyRepresentative phi p)) p := by
  let a := monodromyRepresentative phi p
  let s := (monodromy_quotient_localHomeomorph phi).localInverseAt a
  let c := chartAt StandardCapSpace a
  let e := chartAt StandardCapSpace p
  have hp : p ∈ e.source := mem_chart_source _ p
  have hc : s p ∈ c.source := hp.2
  have hcs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm (e p) :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds (c.map_source hc))
  have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e p :=
    contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hp)
  apply (hcs.comp p he).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with y hy
  exact (c.left_inv hy.2).symm


theorem monodromy_sheet_contMDiffOn (a : monodromyPunctureOpen) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      ((monodromy_quotient_localHomeomorph phi).localInverseAt a)
      ((monodromy_quotient_localHomeomorph phi).localInverseAt a).source := by
  let b := (monodromy_quotient_localHomeomorph phi).localInverseAt a
  intro p hp
  let s := (monodromy_quotient_localHomeomorph phi).localInverseAt
    (monodromyRepresentative phi p)
  have hs : p ∈ s.source := by
    rw [← monodromyRepresentative_spec phi p]
    exact (monodromy_quotient_localHomeomorph phi).apply_self_mem_localInverseAt_source
  have heq : mq (s p) = p :=
    (monodromy_quotient_localHomeomorph phi).apply_localInverseAt_of_mem hs
  have hb : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (b ∘ mq) (s p) :=
    (monodromy_sheet_transition_smooth phi a).contMDiffAt
      ((b.open_source.preimage (monodromy_open_quotient phi).continuous).mem_nhds (by
        change mq (s p) ∈ b.source
        rw [heq]
        exact hp))
  have hcomp := hb.comp p (monodromy_chosen_sheet_contMDiffAt phi p)
  apply ContMDiffAt.contMDiffWithinAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [s.open_source.mem_nhds hs] with y hy
  exact congrArg b
    ((monodromy_quotient_localHomeomorph phi).apply_localInverseAt_of_mem hy).symm

end PoincareConjecture.M38
