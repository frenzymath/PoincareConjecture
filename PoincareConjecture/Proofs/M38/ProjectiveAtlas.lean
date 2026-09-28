import PoincareConjecture.Proofs.M38.ProjectiveLocalSheets










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩


noncomputable def projectiveRepresentative : RealProjectiveThree → UnitThreeSphere :=
  Function.surjInv Quotient.mk_surjective


theorem projectiveRepresentative_spec (p : RealProjectiveThree) :
    Quotient.mk' (projectiveRepresentative p) = p :=
  Function.surjInv_eq Quotient.mk_surjective p


noncomputable def projectiveChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) RealProjectiveThree :=
  projective_quotient_localHomeomorph.chartedSpaceOfRightInverse
    projectiveRepresentative_spec



theorem projective_chart_transition_smooth (a b : UnitThreeSphere) :
    let e := (projective_quotient_localHomeomorph.localInverseAt a).trans
      (chartAt (EuclideanSpace ℝ (Fin 3)) a)
    let e' := (projective_quotient_localHomeomorph.localInverseAt b).trans
      (chartAt (EuclideanSpace ℝ (Fin 3)) b)
    ContDiffOn ℝ ∞ (e.symm.trans e') (e.symm.trans e').source := by
  let sa := projective_quotient_localHomeomorph.localInverseAt a
  let sb := projective_quotient_localHomeomorph.localInverseAt b
  let ca := chartAt (EuclideanSpace ℝ (Fin 3)) a
  let cb := chartAt (EuclideanSpace ℝ (Fin 3)) b
  let e := sa.trans ca
  let e' := sb.trans cb
  change ContDiffOn ℝ ∞ (e.symm.trans e') (e.symm.trans e').source
  apply ContMDiffOn.contDiffOn
  intro z hz
  have hz' : z ∈ ca.target ∧ ca.symm z ∈ sa.target ∧
      Quotient.mk' (ca.symm z) ∈ sb.source ∧
      sb (Quotient.mk' (ca.symm z)) ∈ cb.source := by
    simpa only [e, e', OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_target,
      OpenPartialHomeomorph.coe_trans_symm, sa, sb,
      projective_quotient_localHomeomorph.localInverseAt_symm,
      Set.mem_inter_iff, Set.mem_preimage, Function.comp_apply, and_assoc] using hz
  have hca : ContMDiffAt (𝓡 3) (𝓡 3) ∞ ca.symm z :=
    contMDiffOn_chart_symm.contMDiffAt (ca.open_target.mem_nhds hz'.1)
  have hsheet : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (sb ∘ (Quotient.mk' : UnitThreeSphere → RealProjectiveThree)) (ca.symm z) :=
    (projective_sheet_transition_smooth b).contMDiffAt
      ((sb.open_source.preimage continuous_quotient_mk').mem_nhds hz'.2.2.1)
  have hcb : ContMDiffAt (𝓡 3) (𝓡 3) ∞ cb
      (sb (Quotient.mk' (ca.symm z))) :=
    contMDiffOn_chart.contMDiffAt (cb.open_source.mem_nhds hz'.2.2.2)
  have hcomp := (hcb.comp z (hsheet.comp z hca)).contMDiffWithinAt
    (s := (e.symm.trans e').source)
  simpa only [e, e', OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.coe_trans_symm, sa, sb,
    projective_quotient_localHomeomorph.localInverseAt_symm, Function.comp_assoc]
    using hcomp


theorem projective_isManifold :
    letI := projectiveChartedSpace
    IsManifold (𝓡 3) ∞ RealProjectiveThree := by
  letI := projectiveChartedSpace
  apply isManifold_of_contDiffOn (𝓡 3) ∞ RealProjectiveThree
  intro e e' he he'
  obtain ⟨p, rfl⟩ := he
  obtain ⟨p', rfl⟩ := he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, Set.preimage_id, Set.range_id,
    Set.inter_univ] using
    projective_chart_transition_smooth (projectiveRepresentative p)
      (projectiveRepresentative p')

attribute [local instance] projectiveChartedSpace projective_isManifold


theorem projective_quotient_contMDiff :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (Quotient.mk' : UnitThreeSphere → RealProjectiveThree) := by
  intro x
  apply contMDiffAt_iff_target.mpr
  refine ⟨continuous_quotient_mk'.continuousAt, ?_⟩
  let p : RealProjectiveThree := Quotient.mk' x
  let a := projectiveRepresentative p
  let s := projective_quotient_localHomeomorph.localInverseAt a
  let c := chartAt (EuclideanSpace ℝ (Fin 3)) a
  have hp : p ∈ s.source ∧ s p ∈ c.source :=
    mem_chart_source (EuclideanSpace ℝ (Fin 3)) p
  have hs : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (s ∘ (Quotient.mk' : UnitThreeSphere → RealProjectiveThree)) x :=
    (projective_sheet_transition_smooth a).contMDiffAt
      ((s.open_source.preimage continuous_quotient_mk').mem_nhds hp.1)
  have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c (s p) :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hp.2)
  change ContMDiffAt (𝓡 3) (𝓡 3) ∞
    (c ∘ (s ∘ (Quotient.mk' : UnitThreeSphere → RealProjectiveThree))) x
  exact hc.comp x hs



theorem projective_chosen_sheet_contMDiffAt (p : RealProjectiveThree) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (projective_quotient_localHomeomorph.localInverseAt (projectiveRepresentative p)) p := by
  let a := projectiveRepresentative p
  let s := projective_quotient_localHomeomorph.localInverseAt a
  let c := chartAt (EuclideanSpace ℝ (Fin 3)) a
  let e := chartAt (EuclideanSpace ℝ (Fin 3)) p
  have hp : p ∈ e.source := mem_chart_source _ p
  have hc : s p ∈ c.source := hp.2
  have hcs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm (e p) :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds (c.map_source hc))
  have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e p :=
    contMDiffOn_chart.contMDiffAt (e.open_source.mem_nhds hp)
  apply (hcs.comp p he).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with y hy
  exact (c.left_inv hy.2).symm



theorem projective_sheet_contMDiffOn (a : UnitThreeSphere) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (projective_quotient_localHomeomorph.localInverseAt a)
      (projective_quotient_localHomeomorph.localInverseAt a).source := by
  let b := projective_quotient_localHomeomorph.localInverseAt a
  intro p hp
  let s := projective_quotient_localHomeomorph.localInverseAt (projectiveRepresentative p)
  have hs : p ∈ s.source := by
    rw [← projectiveRepresentative_spec p]
    exact projective_quotient_localHomeomorph.apply_self_mem_localInverseAt_source
  have heq : (Quotient.mk' (s p) : RealProjectiveThree) = p :=
    projective_quotient_localHomeomorph.apply_localInverseAt_of_mem hs
  have hb : ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (b ∘ (Quotient.mk' : UnitThreeSphere → RealProjectiveThree)) (s p) :=
    (projective_sheet_transition_smooth a).contMDiffAt
      ((b.open_source.preimage continuous_quotient_mk').mem_nhds (by
        change Quotient.mk' (s p) ∈ b.source
        rw [heq]
        exact hp))
  have hcomp := hb.comp p (projective_chosen_sheet_contMDiffAt p)
  apply ContMDiffAt.contMDiffWithinAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [s.open_source.mem_nhds hs] with y hy
  exact congrArg b
    (projective_quotient_localHomeomorph.apply_localInverseAt_of_mem hy).symm

end PoincareConjecture.M38
