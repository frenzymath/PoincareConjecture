import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNativePast
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialNormalizedFamily
import PoincareConjecture.Proofs.M47.CanonicalNeckScalarComparison
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistencePullbackSmooth
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_EvolvingJets












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M47

open M36 M44

local notation "E" => EuclideanSpace ℝ (Fin 3)
local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem initialOlder_cylinder_smooth
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin scale epsilon : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (D : SurgeryFlowCylinder F C origin scale I U) (hU : IsOpen U)
    {f : RoundCylinderSpace → C.carrier}
    (hf : ContMDiffOn Ic (𝓡 3) ∞ f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹))
    (hcap : MapsTo f (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹) U)
    {s : ℝ} (hs : s ∈ I) :
    RoundCylinderTensorSmoothOn epsilon (surgeryCylinderPullback D f s) := by
  have hcomp := (D.forward_smooth s hs).comp hf hcap
  have hb := (M34.capPersistence_roundCylinderTensorSmoothOn_pullback
    (F.metric (origin + s / scale)) hcomp).const_mul (beta := scale)
  apply hb.congr_cylinder
  intro z hz v w
  have hfz := (hf.contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
  have hDz := ((D.forward_smooth s hs).contMDiffAt
    (hU.mem_nhds (hcap ⟨mem_univ _, hz⟩))).mdifferentiableAt (by simp)
  simp only [surgeryCylinderPullback, dif_pos hs, roundCylinderPullback]
  rw [mfderiv_comp z hDz hfz]
  rfl



noncomputable def sourceInitialOlderTensor
    {F : SurgeryFlowData.{u}} {T left : ℝ} {hT : T ∈ F.surgery_times}
    [Nonempty (F.slice T).carrier] {i : Fin (F.event T hT).cap_count}
    (old : SurgeryTerminalStrongNeck F T hT i)
    {U : Set (F.event T hT).terminal.carrier}
    (D : SurgeryFlowCylinder F (F.event T hT).terminal T
      (((F.event T hT).necks i).neck.scale⁻¹ ^ 2) (Icc left (-1 / 2)) U)
    (s : ℝ) : RoundCylinderTwoTensor :=
  if s ≤ -1 then surgeryCylinderPullback D ((F.event T hT).necks i).neck.coordinate_map s
  else if s = 0 then
    fun z v w => ((F.event T hT).necks i).neck.scale⁻¹ ^ 2 *
      roundCylinderPullback (F.event T hT).limit_metric
        ((F.event T hT).necks i).neck.coordinate_map z v w
  else surgeryCylinderPullback old.cylinder ((F.event T hT).necks i).neck.coordinate_map s




theorem exists_source_initial_older_tensor_tolerance (P : M47Predecessors.{u})
    {epsilon zeta K : ℝ} (hepsilon : 0 < epsilon)
    (hzeta : 0 < zeta) (hzetaSmall : zeta ≤ 1 / 8) (hK : 0 < K) :
    ∃ omega delta0 : ℝ,
      0 < omega ∧ omega ≤ zeta / 2 ∧ omega ≤ 1 ∧
      0 < delta0 ∧ delta0 ≤ epsilon ∧ delta0 ≤ 1 / 200 ∧
      ∀ {F : SurgeryFlowData.{u}} {T left R : ℝ} (hT : T ∈ F.surgery_times),
      ∀ [Nonempty (F.slice T).carrier], ∀ (i : Fin (F.event T hT).cap_count)
        (old : SurgeryTerminalStrongNeck F T hT i),
      let N := ((F.event T hT).necks i).neck
      N.epsilon ≤ delta0 → 0 < R → R + 1 < N.epsilon⁻¹ →
      left ≤ -1 - 4 * zeta →
      ∀ (U : TopologicalSpace.Opens (F.event T hT).terminal.carrier),
        (U : Set (F.event T hT).terminal.carrier) = N.region (-(R + 1)) (R + 1) →
        (U : Set (F.event T hT).terminal.carrier).Nonempty →
      ∀ (D : SurgeryFlowCylinder F (F.event T hT).terminal T
        (N.scale⁻¹ ^ 2) (Icc left (-1 / 2)) U),
      (∀ s (hs : s ∈ Icc left (-1 / 2)) (hs' : s ∈ Ioo (-1 : ℝ) 0),
        ∀ x ∈ U, D.forward s hs x = old.cylinder.forward s hs' x) →
      (∀ s (hs : s ∈ Icc left (-1 / 2)), s ∈ Icc (-1 - 4 * zeta) (-1 + zeta) →
        ∀ x ∈ U, (F.connection (T + s / (N.scale⁻¹ ^ 2))).curvatureTensorNorm
          (D.forward s hs x) ≤ K * (N.scale⁻¹ ^ 2)) →
      ∀ y ∈ N.carrier,
      (∀ r ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
        r + (N.coordinate_inverse y).2 ∈ Ioo (-R) R) →
      let k := N.connection.scalarCurvature y / (N.scale⁻¹ ^ 2)
      k ∈ Icc (3 / 4 : ℝ) (5 / 4) ∧
      MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0) (Icc (-1 - omega) 0) ∧
      sourceInitialOlderTensor old D 0 = (fun z v w => N.scale⁻¹ ^ 2 *
        roundCylinderPullback (F.event T hT).limit_metric N.coordinate_map z v w) ∧
      RoundCylinderFamilyClose epsilon (Icc (-1 : ℝ) 0)
        (fun u z v w => k * Proofs.M47.neckAxialTensorPullback 1
          (N.coordinate_inverse y).2 (sourceInitialOlderTensor old D (u / k)) z v w) := by
  classical
  let m := Nat.floor epsilon⁻¹
  obtain ⟨Cpast, Lpast, hCpast, hLpast, past⟩ :=
    exists_source_initial_past_comparison P hzeta hzetaSmall hK m
  choose Cj hCj hjbound using fun j => M45.exists_evolvingCylinderError_jet_bound j
  let Cterminal := 1 + ∑ j ∈ Finset.range (m + 1), Cj j
  have hCterminal : 0 < Cterminal := by
    have hs := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (m + 1)) => (hCj j).le)
    dsimp only [Cterminal]
    linarith only [hs]
  have hCjBound (j : ℕ) (hj : j ≤ m) : Cj j ≤ Cterminal := by
    have hs := Finset.single_le_sum (fun j _ => (hCj j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    dsimp only [Cterminal]
    linarith only [hs]
  let Cerror := max Cpast Cterminal
  have hCerror : 0 ≤ Cerror := hCpast.le.trans (le_max_left _ _)
  obtain ⟨omega, delta0, homega, homegaZeta, homegaOne, hdelta0, hdeltaE, hdeltaSmall,
    normalize⟩ := exists_source_initial_own_scalar_family_tolerance
      hepsilon (half_pos hzeta) hCerror hLpast
  refine ⟨omega, delta0, homega, homegaZeta, homegaOne, hdelta0, hdeltaE, hdeltaSmall, ?_⟩
  intro F T left R hT hn i old N hdelta hR hbuffer hleft U hU hne D hagree hcurv y hy hband
  let q := N.scale⁻¹ ^ 2
  let k := N.connection.scalarCurvature y / q
  let B := sourceInitialOlderTensor old D
  let terminal : ℝ → RoundCylinderTwoTensor := fun s =>
    if s = 0 then fun z v w => q * roundCylinderPullback (F.event T hT).limit_metric
      N.coordinate_map z v w else surgeryCylinderPullback old.cylinder N.coordinate_map s
  have hterm : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0) terminal := by
    simpa only [N, (F.event T hT).neck_delta i, terminal, q] using old.comparison
  have htermClose (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) :
      RoundCylinderClose N.epsilon s (terminal s) := by
    rcases hterm.2 with ⟨b, hb, hbound⟩
    exact ⟨hterm.1 s hs, b, hb, hbound s hs⟩
  have holdClose (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0) :
      RoundCylinderClose N.epsilon s (surgeryCylinderPullback old.cylinder N.coordinate_map s) := by
    simpa only [terminal, if_neg hs.2.ne] using htermClose s ⟨hs.1, hs.2.le⟩
  have horder : m ≤ ⌊N.epsilon⁻¹⌋₊ :=
    Nat.floor_mono (inv_anti₀ N.epsilon_pos (hdelta.trans hdeltaE))
  obtain ⟨hmem, G, hread, _hGcurv, hcharts⟩ :=
    past N hbuffer horder hleft U hU hne D old.cylinder hagree holdClose hcurv
  have hrawMem {s : ℝ} (hs : s ∈ Icc (-1 - omega) (-1 : ℝ)) :
      s ∈ Icc left (-1 / 2) := by
    constructor <;> linarith only [hs.1, hs.2, hleft, homegaZeta, hzeta]
  have hbandOld {r : ℝ} (hr : r ∈ Ioo (-R) R) :
      r ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    constructor <;> linarith only [hr.1, hr.2, hbuffer]
  have hcoord : ContMDiffOn Ic (𝓡 3) ∞ N.coordinate_map (univ ×ˢ Ioo (-R) R) :=
    N.coordinate_map_smooth.mono (fun _ hp => ⟨hp.1, hbandOld hp.2⟩)
  have hcapture : MapsTo N.coordinate_map (univ ×ˢ Ioo (-R) R) U := by
    intro z hz
    rw [hU]
    have hzOld := hbandOld hz.2
    refine ⟨neck_coordinate_mem N z ⟨mem_univ _, hzOld⟩, ?_⟩
    rw [neck_inverse_coordinate N z ⟨mem_univ _, hzOld⟩]
    constructor <;> linarith only [hz.2.1, hz.2.2]
  have hBzero : B 0 = fun z v w => q * roundCylinderPullback
      (F.event T hT).limit_metric N.coordinate_map z v w := by
    simp only [B, sourceInitialOlderTensor, show ¬(0 : ℝ) ≤ -1 by norm_num,
      if_false, if_true, N, q]
  have hsmooth : ∀ s ∈ Icc (-1 - omega) 0, ∀ (theta : UnitTwoSphere) (a b : Fin 3),
      ContDiffOn ℝ ∞ (fun p : V => roundCylinderTensorCoefficient (B s)
        (chartAt E₂ theta) p a b) ((chartAt E₂ theta).target ×ˢ Ioo (-R) R) := by
    intro s hs
    by_cases hsPast : s ≤ -1
    · have hD := initialOlder_cylinder_smooth (epsilon := R⁻¹) D U.isOpen
        (by simpa only [inv_inv] using hcoord)
        (by simpa only [inv_inv] using hcapture) (hrawMem ⟨hs.1, hsPast⟩)
      simpa only [B, sourceInitialOlderTensor, if_pos hsPast, RoundCylinderTensorSmoothOn,
        inv_inv] using hD
    · have hsOld : s ∈ Ioc (-1 : ℝ) 0 := ⟨lt_of_not_ge hsPast, hs.2⟩
      intro theta a b
      have h := (hterm.1 s hsOld theta a b).mono
        (Set.prod_mono Subset.rfl (fun _ hr => hbandOld hr))
      simpa only [B, sourceInitialOlderTensor, if_neg hsPast, terminal, N, q] using h
  have hjets : ∀ s ∈ Icc (-1 - omega) 0, ∀ (theta : UnitTwoSphere) (r : ℝ),
      r ∈ Ioo (-R) R → ∀ j ≤ m,
        ‖iteratedFDeriv ℝ j (centeredCylinderMetric (B s) theta r) (0 : E) -
          iteratedFDeriv ℝ j (evolvingCylinderModelField s) (0 : E)‖ ≤
            Cerror * N.epsilon + Lpast * omega := by
    intro s hs theta r hr j hj
    by_cases hsPast : s ≤ -1
    · let a := s + 1 - zeta
      have ha : a ∈ Icc (-zeta - omega) (-zeta) := by
        dsimp only [a]
        constructor <;> linarith only [hs.1, hsPast]
      have haSlab : a ∈ Icc (-(5 * zeta)) 0 := by
        constructor <;> linarith only [ha.1, ha.2, homegaZeta, hzeta]
      have hraw : -1 + zeta + a = s := by dsimp only [a]; ring
      have hrAbs : |r| ≤ R := (abs_lt.mpr hr).le
      obtain ⟨Phi, hPhi, hmap, _hOld, hbound⟩ := hcharts theta r hrAbs
      have hdomain : Metric.ball (0 : E) (1 / 2) ⊆ centeredNeckDomain N r := by
        intro p hp
        have hp' : ‖p‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hp
        have hh : |cylinderHeightCovector p| ≤ ‖p‖ := by
          change |p 2| ≤ ‖p‖
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p (2 : Fin 3)
        apply abs_lt.mp
        exact (abs_add_le _ _).trans_lt (by linarith only [hh, hp', hrAbs, hbuffer])
      have heq : (G.metric a).pullbackCoefficients Phi =ᶠ[𝓝 (0 : E)]
          centeredCylinderMetric (B s) theta r := by
        filter_upwards [Metric.isOpen_ball.mem_nhds
          (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))] with p hp
        have h := source_initial_actual_slab_coefficients N U D (-1 + zeta + a)
          (hmem haSlab) (G.metric a) (fun x => (hread a haSlab x).1)
          theta r Phi hPhi hmap hdomain hp
        simpa only [hraw, B, sourceInitialOlderTensor, if_pos hsPast] using h
      have h := hbound homega.le homegaZeta a ha j hj
      rw [(heq.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds] at h
      simp only [hraw] at h
      exact h.trans (add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) N.epsilon_pos.le) le_rfl)
    · have hsOld : s ∈ Ioc (-1 : ℝ) 0 := ⟨lt_of_not_ge hsPast, hs.2⟩
      have hclose : RoundCylinderClose N.epsilon s (B s) := by
        simpa only [B, sourceInitialOlderTensor, if_neg hsPast, terminal, N, q] using
          htermClose s hsOld
      have hbound := hjbound j N.epsilon_pos ⟨hsOld.1.le, hsOld.2⟩ hclose
        (hj.trans horder) (theta, r) (hbandOld hr)
      have hzero : (0 : E₂) ∈ (chartAt E₂ theta).target := by
        rw [roundCylinder_sphereChart_target]
        trivial
      have hB : ContDiffAt ℝ ∞ (centeredCylinderMetric (B s) theta r) (0 : E) := by
        apply centeredCylinderBilinear_contDiffAt
        intro a b
        exact (hsmooth s hs theta a b).contDiffAt
          (((chartAt E₂ theta).open_target.prod isOpen_Ioo).mem_nhds ⟨hzero, hr⟩)
      rw [fun_iteratedFDeriv_sub_apply (hB.of_le (by exact_mod_cast le_top))
        ((evolvingCylinderModelField_contDiff s).contDiffAt.of_le
          (by exact_mod_cast le_top))] at hbound
      apply hbound.trans
      have hCj' : Cj j ≤ Cerror := (hCjBound j hj).trans (le_max_right _ _)
      exact (mul_le_mul_of_nonneg_right hCj' N.epsilon_pos.le).trans
        (le_add_of_nonneg_right (mul_nonneg hLpast homega.le))
  have hq : 0 < q := sq_pos_of_pos (inv_pos.mpr N.scale_pos)
  have hk : |k - 1| ≤ (16 / 5 : ℝ) * N.epsilon := by
    have h := Proofs.M47.neck_pullback_scalar_difference_le N
      (hdelta.trans hdeltaSmall) (F.event T hT).limit_metric N.connection hq
      (u := 0) le_rfl N.metric_comparison.close y hy
    simpa only [k, sub_zero, div_one] using h
  have hkBounds : k ∈ Icc (3 / 4 : ℝ) (5 / 4) := by
    have he := hdelta.trans hdeltaSmall
    constructor <;> linarith only [(abs_le.mp hk).1, (abs_le.mp hk).2, he]
  obtain ⟨_hkPos, hclock, hfamily⟩ := normalize N.epsilon_pos hdelta hk hband B hsmooth hjets
  exact ⟨hkBounds, hclock, hBzero, hfamily⟩

end PoincareConjecture.M47
