import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Extension.ExtensionCanonical
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Assembly

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryFlowExtension

variable {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)

def strongNeck_direct (t : ℝ) (ht : t ∈ F.time_domain) {epsilon : ℝ}
    (N : SurgeryStrongNeck F t epsilon) : SurgeryStrongNeck E.extended t epsilon := by
  let e := (E.identify t ht).symm
  have H : MetricHomothetyCalculus (E.extended.metric t) (F.metric t) e 1 :=
    Homothety.metricHomothetyCalculus _ _ _ 1 (by norm_num) (E.metric_homothety_symm t ht)
  let K := N.neck.m48_pullback (E.metric_homothety_symm t ht) H (E.extended.connection t)
  let d := E.pushCylinder N.cylinder
  let c := d.rebaseSource e
  have hcoord (z : RoundCylinderSpace)
      (hz : z.2 ∈ Ioo (-N.neck.epsilon⁻¹) N.neck.epsilon⁻¹) :
      N.neck.coordinate_map z ∈ N.neck.carrier := by
    have h := N.neck.coordinate_map_eq (z.1, ⟨z.2, hz⟩)
    exact h ▸ (N.neck.coordinate (z.1, ⟨z.2, hz⟩)).property
  have hterminal : ∀ h x, x ∈ K.carrier → HEq (c.forward 0 h x) x := by
    intro h x hx
    have hz := E.identify_heq (N.cylinder.time_subset ⟨0, h, rfl⟩) ht
      (by simp) (N.terminal_identity h (e x) hx)
    change HEq (c.forward 0 h x) ((E.identify t ht) (e x)) at hz
    simpa only [e, Diffeomorph.apply_symm_apply] using hz
  have hcomparison : RoundCylinderFamilyClose epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback c K.coordinate_map) := by
    apply RoundCylinderFamilyClose.congr
      (B' := surgeryCylinderPullback N.cylinder N.neck.coordinate_map) ?_
      N.metric_comparison
    intro s hs z hz v w
    have hz : z.2 ∈ Ioo (-N.neck.epsilon⁻¹) N.neck.epsilon⁻¹ := by
      simpa only [N.epsilon_eq] using hz
    have hmem : e (K.coordinate_map z) ∈ N.neck.carrier := by
      change e (e.symm (N.neck.coordinate_map z)) ∈ N.neck.carrier
      rw [e.apply_symm_apply]
      exact hcoord z hz
    have hdiff := (K.coordinate_map_smooth.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt
      (by simp)
    have hcomp : e ∘ K.coordinate_map = N.neck.coordinate_map := by
      funext z
      exact e.apply_symm_apply _
    have hd : (mfderiv (𝓡 3) (𝓡 3) e (K.coordinate_map z)).comp
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) K.coordinate_map z) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.neck.coordinate_map z := by
      rw [← mfderiv_comp z (e.contMDiff.mdifferentiable (by simp) _) hdiff, hcomp]
    have hv (v : RoundCylinderTangent z) :
        mfderiv (𝓡 3) (𝓡 3) e (K.coordinate_map z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) K.coordinate_map z v) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.neck.coordinate_map z v :=
      congrArg (fun A => A v) hd
    simp only [surgeryCylinderPullback, dif_pos hs]
    rw [d.rebaseSource_pullbackInner e N.neck.carrier_open s hs
      (K.coordinate_map z) hmem, hv v, hv w]
    change d.pullbackInner s hs (e (e.symm (N.neck.coordinate_map z))) _ _ = _
    rw [e.apply_symm_apply]
    exact E.pushCylinder_pullbackInner N.cylinder N.neck.carrier_open s hs
      (N.neck.coordinate_map z) (hcoord z hz) _ _
  exact ⟨K, N.epsilon_eq, rfl, c, hterminal, hcomparison⟩

theorem canonical_control_direct (t : ℝ) (ht : t ∈ F.time_domain)
    (x : (F.slice t).carrier) (epsilon C : ℝ)
    (h : SurgeryCanonicalControl F t x epsilon C) :
    SurgeryCanonicalControl E.extended t (E.identify t ht x) epsilon C := by
  let e := (E.identify t ht).symm
  have he : MetricHomothety (E.extended.metric t) (F.metric t) e 1 :=
    E.metric_homothety_symm t ht
  have H : MetricHomothetyCalculus (E.extended.metric t) (F.metric t) e 1 :=
    Homothety.metricHomothetyCalculus _ _ _ 1 (by norm_num) he
  cases h with
  | neck N hcenter =>
    refine .neck (E.strongNeck_direct t ht N) ?_
    exact congrArg (E.identify t ht) hcenter
  | cap N hepsilon hconstant _ hcore =>
    refine .cap (N.m48_pullback he H (E.extended.connection t)) hepsilon hconstant rfl ?_
    change (E.identify t ht).symm (E.identify t ht x) ∈ N.core
    simpa only [Diffeomorph.symm_apply_apply] using hcore
  | component N hmem =>
    refine .component (N.m48_pullback he H (E.extended.connection t)) ?_
    change (E.identify t ht).symm (E.identify t ht x) ∈ N.carrier
    simpa only [Diffeomorph.symm_apply_apply] using hmem
  | round N hmem =>
    refine .round (N.m48_pullback he) ?_
    change (E.identify t ht).symm (E.identify t ht x) ∈ N.carrier
    simpa only [Diffeomorph.symm_apply_apply] using hmem

end PoincareConjecture.SurgeryFlowExtension
