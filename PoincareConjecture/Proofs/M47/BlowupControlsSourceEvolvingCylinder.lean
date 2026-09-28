import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingTensor
import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M47

open Proofs.M47 Proofs.M46

local notation "E" => StandardCapSpace
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
  [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}
  {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
  {J : Set ℝ} {U : Set (F.slice t).carrier}
  (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
  (initial : SurgeryCapInitialComparison F t hT i A)
  (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
  (hh : 0 < F.parameters.h t) {g : RiemannianMetric 3 E} (N : EpsilonNeck g)
  (hsource : N.carrier ⊆ F.standard_initial.metric.ball 0 A)
  (s : ℝ) (hs : s ∈ J) (Q : ℝ) (hQ : 0 < Q)
  (hclock : MapsTo (fun u : ℝ => s + u / ((F.parameters.h t) ^ 2 * Q))
    (Icc (-1 : ℝ) 0) J)

omit [Nonempty (F.slice t).carrier] in
include hh hQ in
private theorem source_cap_physical_clock (u : ℝ) :
    (t + s / ((F.parameters.h t)⁻¹ ^ 2)) + u / Q =
      t + (s + u / ((F.parameters.h t) ^ 2 * Q)) / ((F.parameters.h t)⁻¹ ^ 2) := by
  field_simp [hh.ne', hQ.ne']
  ring

noncomputable def sourceCapRebasedCylinder :
    SurgeryFlowCylinder F (F.slice (t + s / ((F.parameters.h t)⁻¹ ^ 2)))
      (t + s / ((F.parameters.h t)⁻¹ ^ 2)) Q (Ioc (-1 : ℝ) 0)
      (actualCapSliceChart e initial comparison s hs '' N.carrier) := by
  let rho := (F.parameters.h t) ^ 2 * Q
  have hrho : 0 < rho := mul_pos (sq_pos_of_pos hh) hQ
  let sigma := fun u : ℝ => s + u / rho
  have hmem : MapsTo sigma (Ioc (-1 : ℝ) 0) J :=
    fun _ hu => hclock (Ioc_subset_Icc_self hu)
  have hmono : StrictMonoOn sigma (Ioc (-1 : ℝ) 0) :=
    fun _ _ _ _ huv => add_lt_add_right ((div_lt_div_iff_of_pos_right hrho).mpr huv) s
  have ht : ∀ u ∈ Ioc (-1 : ℝ) 0,
      (t + s / ((F.parameters.h t)⁻¹ ^ 2)) + u / Q =
        t + sigma u / ((F.parameters.h t)⁻¹ ^ 2) :=
    fun u _ => source_cap_physical_clock hh s Q hQ u
  let raw := seedCylinderReclock e hQ ordConnected_Ioc sigma hmem hmono ht
  have hU : IsOpen U := comparison.choose_spec.2.2.2.1 ▸
    (capInitialPartialDiffeomorph initial).open_target
  let D := M44.cylinderSliceChart e hU s hs
  let V := actualCapSliceChart e initial comparison s hs '' N.carrier
  have hV : V ⊆ D.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem (e.forward s hs)
      (comparison.choose_spec.2.2.2.1 ▸ mem_image_of_mem initial.chart (hsource hx))
  have hmaps : MapsTo D.symm V U := fun _ hx => D.map_target (hV hx)
  exact seedCylinderSource raw D.symm V hV hmaps

theorem sourceCapRebasedCylinder_terminal_identity
    (hzero : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0)
    (x : (F.slice (t + s / ((F.parameters.h t)⁻¹ ^ 2))).carrier)
    (hx : x ∈ actualCapSliceChart e initial comparison s hs '' N.carrier) :
    HEq ((sourceCapRebasedCylinder e initial comparison hh N hsource s hs Q hQ hclock).forward
      0 hzero x) x := by
  let rho := (F.parameters.h t) ^ 2 * Q
  have hrho : 0 < rho := mul_pos (sq_pos_of_pos hh) hQ
  let sigma := fun u : ℝ => s + u / rho
  have hmem : MapsTo sigma (Ioc (-1 : ℝ) 0) J :=
    fun _ hu => hclock (Ioc_subset_Icc_self hu)
  have hmono : StrictMonoOn sigma (Ioc (-1 : ℝ) 0) :=
    fun _ _ _ _ huv => add_lt_add_right ((div_lt_div_iff_of_pos_right hrho).mpr huv) s
  have ht : ∀ u ∈ Ioc (-1 : ℝ) 0,
      (t + s / ((F.parameters.h t)⁻¹ ^ 2)) + u / Q =
        t + sigma u / ((F.parameters.h t)⁻¹ ^ 2) :=
    fun u _ => source_cap_physical_clock hh s Q hQ u
  have hU : IsOpen U := comparison.choose_spec.2.2.2.1 ▸
    (capInitialPartialDiffeomorph initial).open_target
  let D := M44.cylinderSliceChart e hU s hs
  have hxD : x ∈ D.target := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact mem_image_of_mem (e.forward s hs)
      (comparison.choose_spec.2.2.2.1 ▸ mem_image_of_mem initial.chart (hsource hy))
  have he := seedCylinderReclock_forward_heq e hQ ordConnected_Ioc sigma hmem hmono ht
    0 hzero (D.symm x)
  have hsame : ∀ u (hu : u ∈ J), u = s →
      HEq (e.forward u hu (D.symm x)) (e.forward s hs (D.symm x)) := by
    intro u hu hus
    subst u
    rfl
  exact he.trans ((hsame _ _ (by simp only [sigma, zero_div, add_zero])).trans
    (heq_of_eq (D.right_inv hxD)))

theorem sourceCapRebasedCylinder_pullback
    (u : ℝ) (hu : u ∈ Ioc (-1 : ℝ) 0) {z : RoundCylinderSpace}
    (hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v w : RoundCylinderTangent z) :
    surgeryCylinderPullback
        (sourceCapRebasedCylinder e initial comparison hh N hsource s hs Q hQ hclock)
        (actualCapSliceChart e initial comparison s hs ∘ N.coordinate_map) u z v w =
      sourceCapNeckTensor e initial comparison hh N
        (fun u : ℝ => s + u / ((F.parameters.h t) ^ 2 * Q)) hclock
        ((F.parameters.h t) ^ 2 * Q) 1 0 u z v w := by
  let rho := (F.parameters.h t) ^ 2 * Q
  have hrho : 0 < rho := mul_pos (sq_pos_of_pos hh) hQ
  let sigma := fun u : ℝ => s + u / rho
  have hmem : MapsTo sigma (Ioc (-1 : ℝ) 0) J :=
    fun _ hu => hclock (Ioc_subset_Icc_self hu)
  have hmono : StrictMonoOn sigma (Ioc (-1 : ℝ) 0) :=
    fun _ _ _ _ huv => add_lt_add_right ((div_lt_div_iff_of_pos_right hrho).mpr huv) s
  have ht : ∀ u ∈ Ioc (-1 : ℝ) 0,
      (t + s / ((F.parameters.h t)⁻¹ ^ 2)) + u / Q =
        t + sigma u / ((F.parameters.h t)⁻¹ ^ 2) :=
    fun u _ => source_cap_physical_clock hh s Q hQ u
  let raw := seedCylinderReclock e hQ ordConnected_Ioc sigma hmem hmono ht
  have hU : IsOpen U := comparison.choose_spec.2.2.2.1 ▸
    (capInitialPartialDiffeomorph initial).open_target
  let D := M44.cylinderSliceChart e hU s hs
  let V := actualCapSliceChart e initial comparison s hs '' N.carrier
  have hV : V ⊆ D.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem (e.forward s hs)
      (comparison.choose_spec.2.2.2.1 ▸ mem_image_of_mem initial.chart (hsource hx))
  have hmaps : MapsTo D.symm V U := fun _ hx => D.map_target (hV hx)
  let P := initial.chart ∘ N.coordinate_map
  have hzN : N.coordinate_map z ∈ N.carrier := N.coordinate_map_mem_of_axial_mem hz
  have hzSource := hsource hzN
  have hpoint : P z ∈ U := comparison.choose_spec.2.2.2.1 ▸
    mem_image_of_mem initial.chart hzSource
  have hNd := (N.coordinate_map_smooth.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have hId := (initial.chart_smooth.contMDiffAt
    ((capInitialPartialDiffeomorph initial).open_source.mem_nhds hzSource)).mdifferentiableAt
      (by simp)
  have hPd : MDifferentiableAt Ic (𝓡 3) P z := hId.comp z hNd
  have hDd := (D.contMDiffOn_toFun.contMDiffAt (hU.mem_nhds hpoint)).mdifferentiableAt
    (by simp)
  have hchain := mfderiv_comp z hDd hPd
  have hxV : D (P z) ∈ V := mem_image_of_mem _ hzN
  have hsourceMetric := neck_source_inverse_pullbackInner raw D V hV hmaps hU u hu
    hpoint hxV (mfderiv Ic (𝓡 3) P z v) (mfderiv Ic (𝓡 3) P z w)
  have hrawMetric := neck_reclock_pullbackInner e hQ ordConnected_Ioc sigma hmem hmono ht
    u hu (P z) (mfderiv Ic (𝓡 3) P z v) (mfderiv Ic (𝓡 3) P z w)
  have hratio : Q / ((F.parameters.h t)⁻¹ ^ 2) = rho := by
    dsimp only [rho]
    field_simp [hh.ne']
  rw [hratio] at hrawMetric
  have hleft : surgeryCylinderPullback
      (sourceCapRebasedCylinder e initial comparison hh N hsource s hs Q hQ hclock)
      (actualCapSliceChart e initial comparison s hs ∘ N.coordinate_map) u z v w =
      raw.pullbackInner u hu (P z) (mfderiv Ic (𝓡 3) P z v)
        (mfderiv Ic (𝓡 3) P z w) := by
    change surgeryCylinderPullback (seedCylinderSource raw D.symm V hV hmaps)
      (D ∘ P) u z v w = _
    simp only [surgeryCylinderPullback, dif_pos hu, Function.comp_apply,
      hchain, ContinuousLinearMap.comp_apply]
    exact hsourceMetric
  rw [hleft, hrawMetric]
  have hOld := ((e.forward_smooth (sigma u) (hmem hu)).contMDiffAt
    (hU.mem_nhds hpoint)).mdifferentiableAt (by simp)
  have hOldChain := mfderiv_comp z hOld hPd
  have hunit (T : RoundCylinderTwoTensor) : neckAxialTensorPullback 1 0 T = T := by
    have hA (p : RoundCylinderSpace) : neckAxialSpaceMap 1 0 p = p := by
      ext <;> simp [neckAxialSpaceMap]
    have hL (a : RoundCylinderCoordinates) : neckAxialLinearMap 1 a = a := by
      ext <;> simp [neckAxialLinearMap]
    funext p a b
    simp only [neckAxialTensorPullback, hL]
    exact congrArg (fun y : RoundCylinderSpace => T y a b) (hA p)
  simp only [sourceCapNeckTensor, dif_pos (Ioc_subset_Icc_self hu), hunit]
  change rho * (((F.parameters.h t)⁻¹ ^ 2) *
      (F.metric (t + sigma u / ((F.parameters.h t)⁻¹ ^ 2))).inner
        (e.forward (sigma u) (hmem hu) (P z))
        (mfderiv (𝓡 3) (𝓡 3) (e.forward (sigma u) (hmem hu)) (P z)
          (mfderiv Ic (𝓡 3) P z v))
        (mfderiv (𝓡 3) (𝓡 3) (e.forward (sigma u) (hmem hu)) (P z)
          (mfderiv Ic (𝓡 3) P z w))) =
    rho * (((F.parameters.h t)⁻¹ ^ 2) *
      (F.metric (t + sigma u / ((F.parameters.h t)⁻¹ ^ 2))).inner
        ((e.forward (sigma u) (hmem hu) ∘ P) z)
        (mfderiv Ic (𝓡 3) (e.forward (sigma u) (hmem hu) ∘ P) z v)
        (mfderiv Ic (𝓡 3) (e.forward (sigma u) (hmem hu) ∘ P) z w))
  rw [hOldChain]
  rfl

end PoincareConjecture.M47
