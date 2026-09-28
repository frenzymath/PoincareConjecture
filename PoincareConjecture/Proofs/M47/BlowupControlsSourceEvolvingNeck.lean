import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingCylinder
import PoincareConjecture.Proofs.M47.BlowupControlsCapNeckImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

theorem exists_actualCap_strong_neck_of_family
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
    {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hh : 0 < F.parameters.h t) {g : RiemannianMetric 3 StandardCapSpace}
    (N : EpsilonNeck g) (hsource : N.carrier ⊆ F.standard_initial.metric.ball 0 A)
    (s : ℝ) (hs : s ∈ J)
    (hQ : 0 < (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
      (actualCapSliceChart e initial comparison s hs N.center))
    (hclock : MapsTo
      (fun u : ℝ => s + u / ((F.parameters.h t) ^ 2 *
        (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (actualCapSliceChart e initial comparison s hs N.center)))
      (Icc (-1 : ℝ) 0) J)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Icc (-1 : ℝ) 0)
      (sourceCapNeckTensor e initial comparison hh N
        (fun u : ℝ => s + u / ((F.parameters.h t) ^ 2 *
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (actualCapSliceChart e initial comparison s hs N.center))) hclock
        ((F.parameters.h t) ^ 2 *
          (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
            (actualCapSliceChart e initial comparison s hs N.center)) 1 0)) :
    ∃ N' : SurgeryStrongNeck F (t + s / ((F.parameters.h t)⁻¹ ^ 2)) N.epsilon,
      N'.neck.center = actualCapSliceChart e initial comparison s hs N.center := by
  let b := t + s / ((F.parameters.h t)⁻¹ ^ 2)
  let phi := actualCapSliceChart e initial comparison s hs
  let Q := (F.connection b).scalarCurvature (phi N.center)
  let rho := (F.parameters.h t) ^ 2 * Q
  let sigma := fun u : ℝ => s + u / rho
  let B := sourceCapNeckTensor e initial comparison hh N sigma hclock rho 1 0
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hunit (T : RoundCylinderTwoTensor) : neckAxialTensorPullback 1 0 T = T := by
    have hA (p : RoundCylinderSpace) : neckAxialSpaceMap 1 0 p = p := by
      ext <;> simp [neckAxialSpaceMap]
    have hL (a : RoundCylinderCoordinates) : neckAxialLinearMap 1 a = a := by
      ext <;> simp [neckAxialLinearMap]
    funext p a b
    simp only [neckAxialTensorPullback, hL]
    exact congrArg (fun y : RoundCylinderSpace => T y a b) (hA p)
  have hclose0 : RoundCylinderClose N.epsilon 0 (B 0) :=
    ⟨hfamily.1 0 hzero, hfamily.2.choose, hfamily.2.choose_spec.1,
      hfamily.2.choose_spec.2 0 hzero⟩
  have hclose : RoundCylinderClose N.epsilon 0 (fun z v w =>
      Q * roundCylinderPullback (F.metric b) (phi ∘ N.coordinate_map) z v w) := by
    apply hclose0.congr_cylinder
    intro z _ v w
    have hread (s' : ℝ) (hs' : s' ∈ J) (heq : s' = s) :
        rho * roundCylinderPullback
          (m01RescaledMetric (F.metric (t + s' / ((F.parameters.h t)⁻¹ ^ 2)))
            ((F.parameters.h t)⁻¹ ^ 2) (sq_pos_of_pos (inv_pos.mpr hh)))
          (actualCapSliceChart e initial comparison s' hs' ∘ N.coordinate_map) z v w =
        Q * roundCylinderPullback (F.metric b) (phi ∘ N.coordinate_map) z v w := by
      subst s'
      change ((F.parameters.h t) ^ 2 * Q) *
        (((F.parameters.h t)⁻¹ ^ 2) *
          roundCylinderPullback (F.metric b) (phi ∘ N.coordinate_map) z v w) = _
      field_simp [hh.ne']
    dsimp only [B, sourceCapNeckTensor]
    simp only [dif_pos hzero, hunit]
    exact hread (sigma 0) (hclock hzero) (by simp only [sigma, zero_div, add_zero])
  have hNphi : N.carrier ⊆ phi.source := by
    rw [actualCapSliceChart_source]
    exact hsource
  obtain ⟨E, hepsilon, hcenter, hconnection, hcarrier, _hsphere, hcoordinate, _hinverse,
      _hregions⟩ := exists_cap_neck_image_of_normalized_comparison
    N (F.connection b) phi hNphi hQ hclose
  have hscale : E.scale⁻¹ ^ 2 = Q := by
    rw [E.scale_eq_scalar, hconnection, hcenter, inv_pow,
      ← Real.rpow_mul_natCast hQ.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
    rfl
  have hscalePos : 0 < E.scale⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr E.scale_pos)
  have hclockE : MapsTo (fun u : ℝ => s + u / ((F.parameters.h t) ^ 2 *
      (E.scale⁻¹ ^ 2))) (Icc (-1 : ℝ) 0) J := by
    rw [hscale]
    exact hclock
  let raw := sourceCapRebasedCylinder e initial comparison hh N hsource
    s hs (E.scale⁻¹ ^ 2) hscalePos hclockE
  have hsourceE : E.carrier ⊆ phi '' N.carrier := hcarrier.subset
  let d := raw.restrict (Subset.refl _) ordConnected_Ioc hsourceE
  have hcomparison : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback d E.coordinate_map) := by
    have hsmall : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0) B :=
      ⟨fun u hu => hfamily.1 u (Ioc_subset_Icc_self hu),
        hfamily.2.choose, hfamily.2.choose_spec.1,
        fun u hu => hfamily.2.choose_spec.2 u (Ioc_subset_Icc_self hu)⟩
    apply hsmall.congr_cylinder
    intro u hu z hz v w
    rw [hcoordinate]
    have h := sourceCapRebasedCylinder_pullback e initial comparison hh N hsource
      s hs (E.scale⁻¹ ^ 2) hscalePos hclockE u hu hz v w
    have hB : sourceCapNeckTensor e initial comparison hh N
        (fun u : ℝ => s + u / ((F.parameters.h t) ^ 2 * (E.scale⁻¹ ^ 2))) hclockE
        ((F.parameters.h t) ^ 2 * (E.scale⁻¹ ^ 2)) 1 0 u z v w = B u z v w := by
      simp only [hscale]
      rfl
    exact hB.symm.trans h.symm
  refine ⟨{
    neck := E
    epsilon_eq := hepsilon
    connection_eq := hconnection
    cylinder := d
    terminal_identity := fun h x hx => sourceCapRebasedCylinder_terminal_identity
      e initial comparison hh N hsource s hs (E.scale⁻¹ ^ 2) hscalePos hclockE
      h x (hsourceE hx)
    metric_comparison := hcomparison }, hcenter⟩

end PoincareConjecture.M47
