import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingFamily
import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingNeck
import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingCoordinate
import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47



theorem exists_actualCap_nearby_evolving_neck
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {theta A v gamma : ℝ} (htheta : theta < 1) (hA : 0 < A)
    (hv : v ∈ Icc 0 theta) {z : StandardCapSpace}
    (N : StandardEvolvingNeck standard.atlas standard.flow v gamma z
      (Ioc (-(1 + gamma)) 0))
    (E : EpsilonNeck (standard.flow.metric v)) (hge : gamma ≤ E.epsilon)
    (hmap : E.coordinate_map = N.patch.coordinate)
    (hconnection : E.connection = standard.flow.connection v) (hcenter : E.center = z)
    (hsource : E.carrier ⊆ g0.metric.ball 0 A) :
    ∃ eta0 delta : ℝ, ∃ V : Set StandardCapSpace,
      0 < eta0 ∧ 0 < delta ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ g0.metric.ball 0 A ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (_comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J),
      s ≤ theta → Icc 0 s ⊆ J → |s - v| < delta → ∀ z' ∈ V,
      ∃ N' : SurgeryStrongNeck F (t + s / ((F.parameters.h t)⁻¹ ^ 2)) E.epsilon,
        N'.neck.center = e.forward s hs (initial.chart z') := by
  obtain ⟨lambda, etaF, deltaF, hlambda, hetaF, hdeltaF, hmodel, hphysical⟩ :=
    exists_actualCap_evolving_family_tolerance standard htheta hA hv.2 N E hge hmap hsource
  have hzE : z ∈ E.carrier := hcenter ▸ E.central_sphere_subset E.center_on_central_sphere
  obtain ⟨etaC, deltaC, V0, hetaC, hdeltaC, hV0, hzV0, hV0source, hclockNear⟩ :=
    exists_actualCap_evolving_clock_tolerance standard htheta hA hv N (hsource hzE) hdeltaF
  let V := V0 ∩ E.region (-deltaF) deltaF
  have hV : IsOpen V := hV0.inter (E.region_isOpen _ _)
  have hzV : z ∈ V := by
    refine ⟨hzV0, hzE, ?_⟩
    have hzero : (E.coordinate_inverse z).2 = 0 :=
      (E.mem_central_sphere_iff_of_mem hzE).mp (hcenter ▸ E.center_on_central_sphere)
    rw [hzero]
    exact ⟨neg_neg_of_pos hdeltaF, hdeltaF⟩
  refine ⟨min etaF etaC, min deltaF deltaC, V, lt_min hetaF hetaC,
    lt_min hdeltaF hdeltaC, hV, hzV, fun x hx => hV0source hx.1, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetaSmall comparison hh
    s hs hst hJ hnear z' hz'
  obtain ⟨hQ, hrho, hmodelPos, hmodelNear, _htimes⟩ :=
    hclockNear F hinitial S hS t hT hn i J U e initial eta heta
      (hetaSmall.trans (min_le_right _ _)) comparison hh s hs hst
      (hnear.trans_le (min_le_right _ _)) z' hz'.1
  let q' := (E.coordinate_inverse z').1
  let c := (E.coordinate_inverse z').2
  let modelR := (standard.flow.connection v).scalarCurvature z'
  let Q := (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
    (actualCapSliceChart e initial comparison s hs z')
  let rho := (F.parameters.h t) ^ 2 * Q
  have hc : |c| < deltaF := abs_lt.mpr hz'.2.2
  have hpoint : E.coordinate_map (q', c) = z' :=
    E.coordinate_map_coordinate_inverse hz'.2.1
  obtain ⟨_, hshift, hmodelFamily⟩ := hmodel v modelR c
    (by simpa only [sub_self, abs_zero] using hdeltaF) hmodelNear hc
  have hdomain : ∀ r ∈ Ioo (-E.epsilon⁻¹) E.epsilon⁻¹,
      lambda * r + c ∈ Ioo (-E.epsilon⁻¹) E.epsilon⁻¹ := by
    intro r hr
    exact neckAxialCoordinate_mem_open_interval E.epsilon_pos hlambda hshift
      ⟨hr.1.le, hr.2.le⟩
  have hscalar : 0 < E.connection.scalarCurvature (E.coordinate_map (q', c)) := by
    rw [hconnection, hpoint]
    exact hmodelPos
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hmodelClose : RoundCylinderClose E.epsilon 0 (fun p a b =>
      modelR * neckAxialTensorPullback lambda c
        (roundCylinderPullback (standard.flow.metric v) E.coordinate_map) p a b) := by
    simpa only [zero_div, add_zero] using
      (show RoundCylinderClose E.epsilon 0 (fun p a b =>
        modelR * neckAxialTensorPullback lambda c
          (roundCylinderPullback (standard.flow.metric (v + 0 / modelR))
            E.coordinate_map) p a b) from
        ⟨hmodelFamily.1 0 hzero, hmodelFamily.2.choose,
          hmodelFamily.2.choose_spec.1, hmodelFamily.2.choose_spec.2 0 hzero⟩)
  have hclose : RoundCylinderClose E.epsilon 0 (fun p a b =>
      E.connection.scalarCurvature (E.coordinate_map (q', c)) *
        roundCylinderPullback (standard.flow.metric v)
          (E.coordinate_map ∘ neckAxialSpaceMap lambda c) p a b) := by
    apply hmodelClose.congr_cylinder
    intro p hp a b
    rw [cap_neck_affine_pullback E lambda c (hdomain p.2 hp), hconnection, hpoint]
  let E' := capAffineNeck E E.epsilon_pos E.epsilon_lt_half hlambda.1
    hdomain q' hscalar hclose
  have hepsilon : E'.epsilon = E.epsilon := rfl
  have hcenter' : E'.center = z' := by
    change E.coordinate_map (q', c) = z'
    exact hpoint
  have hcoordinate : E'.coordinate_map = E.coordinate_map ∘ neckAxialSpaceMap lambda c := rfl
  have hsourceF : E.carrier ⊆ F.standard_initial.metric.ball 0 A := by
    rw [hinitial]
    exact hsource
  have hsource' : E'.carrier ⊆ F.standard_initial.metric.ball 0 A := by
    intro x hx
    exact hsourceF hx.1
  obtain ⟨hclock, hfamily⟩ := hphysical F hinitial S hS t hT hn i J U e initial
    eta heta (hetaSmall.trans (min_le_left _ _)) comparison hh s rho c hst hJ
    (hnear.trans_le (min_le_left _ _)) hrho hc
  have hfamily' : RoundCylinderFamilyClose E'.epsilon (Icc (-1 : ℝ) 0)
      (sourceCapNeckTensor e initial comparison hh E'
        (fun u : ℝ => s + u / rho) hclock rho 1 0) := by
    rw [hepsilon]
    apply hfamily.congr_cylinder
    intro u hu p hp a b
    exact (sourceCapNeckTensor_affine_coordinate e initial comparison hh E E' hsourceF
      (fun u : ℝ => s + u / rho) hclock rho lambda c hlambda hshift
      hcoordinate u hu hp a b).symm
  have hQ' : 0 < (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
      (actualCapSliceChart e initial comparison s hs E'.center) := by
    rw [hcenter']
    exact hQ
  have hclock' : MapsTo
      (fun u : ℝ => s + u / ((F.parameters.h t) ^ 2 *
        (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (actualCapSliceChart e initial comparison s hs E'.center)))
      (Icc (-1 : ℝ) 0) J := by
    rw [hcenter']
    exact hclock
  have hfamily'' : RoundCylinderFamilyClose E'.epsilon (Icc (-1 : ℝ) 0)
      (sourceCapNeckTensor e initial comparison hh E'
        (fun u : ℝ => s + u / ((F.parameters.h t) ^ 2 *
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (actualCapSliceChart e initial comparison s hs E'.center))) hclock'
        ((F.parameters.h t) ^ 2 *
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (actualCapSliceChart e initial comparison s hs E'.center)) 1 0) := by
    have hnormalize : (F.parameters.h t) ^ 2 *
        (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (actualCapSliceChart e initial comparison s hs E'.center) = rho := by
      rw [hcenter']
    have hsame (rho' : ℝ) (heq : rho' = rho)
        (clock' : MapsTo (fun u : ℝ => s + u / rho') (Icc (-1 : ℝ) 0) J) :
        RoundCylinderFamilyClose E'.epsilon (Icc (-1 : ℝ) 0)
          (sourceCapNeckTensor e initial comparison hh E'
            (fun u : ℝ => s + u / rho') clock' rho' 1 0) := by
      subst rho'
      exact hfamily'
    exact hsame _ hnormalize hclock'
  obtain ⟨N', hN'⟩ := exists_actualCap_strong_neck_of_family e initial comparison hh
    E' hsource' s hs hQ' hclock' hfamily''
  refine ⟨N', ?_⟩
  simpa only [hcenter', actualCapSliceChart_apply] using hN'

end PoincareConjecture.M47
