import PoincareConjecture.Proofs.M47.TerminalSourceRealizationCoefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

private noncomputable def normalSubtypeChart
    {C : GeneralizedSliceCarrier.{u}} (U : TopologicalSpace.Opens C.carrier) (p : U) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) U C.carrier ∞ := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨p⟩
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp
    apply contMDiffWithinAt_id.congr_of_mem _ hx
    intro y hy
    exact e.right_inv hy
  exact {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := hi }

private theorem normalMap_rebase
    {C : GeneralizedSliceCarrier.{u}} (U : TopologicalSpace.Opens C.carrier)
    (S : ℝ → GeneralizedSliceCarrier.{u}) {a b : ℝ} (hab : a = b)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) U (S a).carrier ∞) :
    ∃ j : PartialDiffeomorph (𝓡 3) (𝓡 3) U (S b).carrier ∞,
      j.source = e.source ∧
      (⟨b, fun x : U => j x⟩ : (t : ℝ) × (U → (S t).carrier)) =
        ⟨a, fun x : U => e x⟩ := by
  cases hab
  exact ⟨e, rfl, rfl⟩

private theorem normalMap_exists
    {S : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}} {b Q : ℝ} {I : Set ℝ}
    (U : TopologicalSpace.Opens C.carrier) (p : U)
    (e : SurgeryFlowCylinder S C b Q I U) (h0 : (0 : ℝ) ∈ I) :
    ∃ j : PartialDiffeomorph (𝓡 3) (𝓡 3) U (S.slice b).carrier ∞,
      j.source = univ ∧
      (⟨b, fun x : U => j x⟩ : (t : ℝ) × (U → (S.slice t).carrier)) =
        ⟨b + 0 / Q, fun x : U => e.forward 0 h0 x.val⟩ := by
  let a := (normalSubtypeChart U p).trans (M44.cylinderSliceChart e U.isOpen 0 h0)
  obtain ⟨j, hsource, hmap⟩ := normalMap_rebase U S.slice (by simp : b + 0 / Q = b) a
  refine ⟨j, hsource.trans ?_, hmap⟩
  ext x
  change (x ∈ (univ : Set U) ∧ x.val ∈ U) ↔ x ∈ (univ : Set U)
  simp only [mem_univ, true_and, iff_true]
  exact x.property

noncomputable def terminalSourceNormal_terminalMap
    {S : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}} {b Q : ℝ} {I : Set ℝ}
    (U : TopologicalSpace.Opens C.carrier) (p : U)
    (e : SurgeryFlowCylinder S C b Q I U) (h0 : (0 : ℝ) ∈ I) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) U (S.slice b).carrier ∞ :=
  (normalMap_exists U p e h0).choose

theorem terminalSourceNormal_terminal_map
    {S : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}} {b Q : ℝ} {I : Set ℝ}
    (U : TopologicalSpace.Opens C.carrier) (p : U)
    (e : SurgeryFlowCylinder S C b Q I U) (h0 : (0 : ℝ) ∈ I) :
    let j := terminalSourceNormal_terminalMap U p e h0
    j.source = univ ∧ j.target = range (fun x : U => j x) ∧
      (⟨b, fun x : U => j x⟩ : (t : ℝ) × (U → (S.slice t).carrier)) =
        ⟨b + 0 / Q, fun x : U => e.forward 0 h0 x.val⟩ := by
  let j := terminalSourceNormal_terminalMap U p e h0
  have hj := (normalMap_exists U p e h0).choose_spec
  refine ⟨hj.1, ?_, hj.2⟩
  have ht := j.toPartialEquiv.image_source_eq_target
  have hsource : j.source = univ := hj.1
  rw [hsource, image_univ] at ht
  exact ht.symm

theorem terminalSourceNormal_terminal_readouts
    {S : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}} {b Q : ℝ} {I J : Set ℝ}
    (U : TopologicalSpace.Opens C.carrier) (p : U)
    (e : SurgeryFlowCylinder S C b Q I U) (h0 : (0 : ℝ) ∈ I)
    (F : RicciFlow 3 U J)
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      (F.metric 0).inner x v w = e.pullbackInner 0 h0 x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w))
    (hnorm : ∀ x : U, (F.connection 0).curvatureTensorNorm x =
      (S.connection (b + 0 / Q)).curvatureTensorNorm (e.forward 0 h0 x.val) / Q) :
    let j := terminalSourceNormal_terminalMap U p e h0
    (∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      (F.metric 0).inner x v w = Q * (S.metric b).inner (j x)
        (mfderiv (𝓡 3) (𝓡 3) j x v) (mfderiv (𝓡 3) (𝓡 3) j x w)) ∧
      ∀ x : U, (F.connection 0).curvatureTensorNorm x =
        (S.connection b).curvatureTensorNorm (j x) / Q := by
  let j := terminalSourceNormal_terminalMap U p e h0
  have hmap := (terminalSourceNormal_terminal_map U p e h0).2.2
  constructor
  · intro x v w
    have hm := congrArg (fun q : (t : ℝ) × (U → (S.slice t).carrier) =>
      (S.metric q.1).inner (q.2 x)
        (mfderiv (𝓡 3) (𝓡 3) q.2 x v) (mfderiv (𝓡 3) (𝓡 3) q.2 x w)) hmap
    have hf := (e.forward_smooth 0 h0 x.val x.property).contMDiffAt
      (U.isOpen.mem_nhds x.property)
    have hd := mfderiv_comp x (hf.mdifferentiableAt (by simp))
      (contMDiff_subtype_val (n := ∞) x |>.mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward 0 h0 y.val) x = _ at hd
    rw [hd] at hm
    exact (hmetric x v w).trans (congrArg (fun z : ℝ => Q * z) hm.symm)
  · intro x
    have hn := congrArg (fun q : (t : ℝ) × (U → (S.slice t).carrier) =>
      (S.connection q.1).curvatureTensorNorm (q.2 x)) hmap
    exact (hnorm x).trans (congrArg (fun z : ℝ => z / Q) hn.symm)

end PoincareConjecture.M47
