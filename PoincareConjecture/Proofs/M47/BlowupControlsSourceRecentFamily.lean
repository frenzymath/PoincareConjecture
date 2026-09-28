import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamilyReference
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamilyTensor
import PoincareConjecture.Proofs.M47.BlowupControlsSourceRecentFamilyTolerance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47 M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem recent_jet_sub_triangle {f k g : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ ∞ f x) (hk : ContDiffAt ℝ ∞ k x)
    (hg : ContDiffAt ℝ ∞ g x) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv ℝ j (fun y => f y - k y) x‖ +
        ‖iteratedFDeriv ℝ j (fun y => k y - g y) x‖ := by
  change ‖iteratedFDeriv ℝ j (f - g) x‖ ≤
    ‖iteratedFDeriv ℝ j (f - k) x‖ + ‖iteratedFDeriv ℝ j (k - g) x‖
  rw [iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast le_top))
      (hg.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast le_top))
      (hk.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_sub_apply (hk.of_le (by exact_mod_cast le_top))
      (hg.of_le (by exact_mod_cast le_top))]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

theorem exists_actualCap_initial_recent_family_tolerance
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {theta A v gamma : ℝ} (htheta : theta < 1) (hA : 0 < A) (hvtheta : v ≤ theta)
    {z : StandardCapSpace}
    (N : StandardEvolvingNeck standard.atlas standard.flow v gamma z
      (Icc (-v * (standard.flow.connection v).scalarCurvature z) 0))
    (E : EpsilonNeck (standard.flow.metric v)) (heps : E.epsilon = 2 * gamma)
    (hmap : E.coordinate_map = N.patch.coordinate)
    (hsource : E.carrier ⊆ g0.metric.ball 0 A) :
    ∃ eta0 delta : ℝ, 0 < eta0 ∧ 0 < delta ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (hh : 0 < F.parameters.h t) (s H c : ℝ), s ∈ Icc 0 theta →
      Icc 0 s ⊆ J → |s - v| < delta →
      |H - (standard.flow.connection v).scalarCurvature z| < delta → |c| < delta →
      0 < H ∧ ∃ hclock : MapsTo (fun u : ℝ => s + u / H) (Icc (-H * s) 0) J,
        RoundCylinderFamilyClose (3 * gamma) (Icc (-H * s) 0)
          (sourceRecentCapTensor e initial comparison hh E s H c hclock) := by
  let q := (standard.flow.connection v).scalarCurvature z
  have hq : 0 < q := N.scalar_pos
  have hgamma : 0 < gamma := N.epsilon_pos
  let T := (theta + 1) / 2
  have hT : 0 < T := by dsimp only [T]; linarith only [N.time_mem.1, hvtheta]
  have hthetaT : theta < T := by dsimp only [T]; linarith only [htheta]
  have hT1 : T < 1 := by dsimp only [T]; linarith only [htheta]
  have hI : Icc 0 T ⊆ Ico 0 standard.flow.base.lifetime := by
    intro w hw
    refine ⟨hw.1, ?_⟩
    rw [standard.lifetime_one]
    exact hw.2.trans_lt hT1
  let G : RicciFlow 3 StandardCapSpace (Icc 0 T) := {
    metric := standard.flow.metric
    connection := standard.flow.connection
    interval := ordConnected_Icc
    nontrivial := ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, hT.ne⟩
    smooth := standard.flow.base.flow.smooth.mono (prod_mono hI Subset.rfl)
    equation := fun w hw y a b =>
      (standard.flow.base.flow.equation w (hI hw) y a b).mono hI }
  have hv : v ∈ Icc 0 T := ⟨N.time_mem.1, hvtheta.trans hthetaT.le⟩
  have hfamily : RoundCylinderFamilyClose gamma (Icc (-v * q) 0)
      (fun u p a b => q *
        roundCylinderPullback (G.metric (v + u / q)) E.coordinate_map p a b) := by
    rw [hmap]
    exact N.close
  let L := q + 1
  have hL : 0 < L := by dsimp only [L]; linarith only [hq]
  obtain ⟨kappa, hkappa, henergy⟩ :=
    exists_source_recent_family_coefficient_tolerance hgamma (L * T)
  obtain ⟨delta, hdelta, hreference⟩ := exists_source_recent_reference_tolerance
    hT hgamma G E heps hv hq hfamily (half_pos hkappa)
  let m := Nat.floor (3 * gamma)⁻¹
  have hm : m ≤ Nat.floor E.epsilon⁻¹ := by
    apply Nat.floor_mono
    apply inv_anti₀ E.epsilon_pos
    rw [heps]
    linarith only [hgamma]
  obtain ⟨Cphys, hCphys, hphysical⟩ := exists_actualCap_fixed_neck_coefficient_error_bound
    standard htheta hA hL E hsource m hm
  let eta0 := min (1 / ((m : ℝ) + 1)) (kappa / (2 * Cphys))
  have heta0 : 0 < eta0 := lt_min (by positivity) (div_pos hkappa (by positivity))
  refine ⟨eta0, delta, heta0, hdelta, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta heta hetaSmall comparison hh
    s H c hs hJ hsv hHq hc
  have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hthetaT.le⟩
  obtain ⟨hH, hHL, hdom, href⟩ := hreference s hsT H c hsv hHq hc
  have hclockTimes (u : ℝ) (hu : u ∈ Icc (-H * s) 0) : s + u / H ∈ Icc 0 s := by
    obtain ⟨w, hw, _, hclock⟩ := source_recent_clock_parameter hH hs.1 hu
    rw [hclock]
    exact ⟨mul_nonneg hs.1 hw.1, by nlinarith only [mul_nonneg hs.1 (sub_nonneg.mpr hw.2)]⟩
  have hclock : MapsTo (fun u : ℝ => s + u / H) (Icc (-H * s) 0) J :=
    fun u hu => hJ (hclockTimes u hu)
  have hetaOrder : eta ≤ 1 / ((m : ℝ) + 1) := hetaSmall.trans (min_le_left _ _)
  have hproduct : Cphys * eta ≤ kappa / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * Cphys)).mp
      (hetaSmall.trans (min_le_right _ _))
    nlinarith only [h]
  have herr := hphysical F hinitial S hS t hT hn i J U e initial eta heta hetaOrder
    comparison hh
  cases hinitial
  cases hS
  let B := sourceRecentCapTensor e initial comparison hh E s H c hclock
  have hBsmooth := sourceRecentCapTensor_smooth e initial comparison hh E s H c hclock
    hsource (fun r hr => hdom r ⟨hr.1.le, hr.2.le⟩)
  have herror := sourceRecentCapTensor_coefficient_error_le e initial comparison hh E s H c
    hclock hsource hdom m (fun u hu => herr (s + u / H) (hclock hu)
      ((hclockTimes u hu).2.trans hs.2) H hH hHL)
  refine ⟨hH, hclock, hBsmooth, 6 * gamma ^ 2, ?_, ?_⟩
  · nlinarith only [sq_pos_of_pos hgamma]
  · intro u hu z0 hz0
    obtain ⟨w, hw, hueq, hclockEq⟩ := source_recent_clock_parameter hH hs.1 hu
    have ref := href w hw
    dsimp only at ref
    rw [← hueq] at ref
    let D : RoundCylinderTwoTensor := fun p a b => H * neckAxialTensorPullback 1 c
      (roundCylinderPullback (standard.flow.metric (s * w)) E.coordinate_map) p a b
    let C := sourceRecentTimeCorrection u (-q * v * (1 - w)) (fun p a b => q *
      neckAxialTensorPullback 1 c
        (roundCylinderPullback (standard.flow.metric (v * w)) E.coordinate_map) p a b)
    obtain ⟨hCsmooth, hCenergy, hCcoeff⟩ := ref
    change RoundCylinderTensorSmoothOn (3 * gamma) C at hCsmooth
    let linear : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun p =>
      let A : V →L[ℝ] E₃ := mfderiv Ic (𝓡 3) E.coordinate_map p
      let M : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
        (standard.flow.metric (s * w)).inner (E.coordinate_map p)
      H • M.bilinearComp A A
    have hraw : RoundCylinderTensorSmoothOn E.epsilon (fun p a b => linear p a b) :=
      (capPersistence_roundCylinderTensorSmoothOn_pullback
        (standard.flow.metric (s * w)) E.coordinate_map_smooth).const_mul
    have hDsmooth : RoundCylinderTensorSmoothOn (3 * gamma) D :=
      source_recent_translation_smooth (fun r hr => hdom r ⟨hr.1.le, hr.2.le⟩) linear hraw
    have huT : u ∈ Icc (-(L * T)) 0 := by
      refine ⟨?_, hu.2⟩
      have hprod : H * s ≤ L * T := mul_le_mul hHL hsT.2 hs.1 hL.le
      linarith only [hu.1, hprod]
    apply henergy u huT (B u) C (hBsmooth u hu) hCsmooth hCenergy ?_ z0 hz0
    intro p r hr j hj a b
    have hpoint : (0, r) ∈ (chartAt E₂ p).target ×ˢ
        Ioo (-(3 * gamma)⁻¹) (3 * gamma)⁻¹ := by
      refine ⟨?_, hr⟩
      rw [roundCylinder_sphereChart_target]
      trivial
    have hnhds := ((chartAt E₂ p).open_target.prod isOpen_Ioo).mem_nhds hpoint
    have hf := (hBsmooth u hu p a b).contDiffAt hnhds
    have hk := (hDsmooth p a b).contDiffAt hnhds
    have hg := (hCsmooth p a b).contDiffAt hnhds
    have htriangle := recent_jet_sub_triangle hf hk hg j
    have he1 := herror u hu p r ⟨hr.1.le, hr.2.le⟩ j hj a b
    rw [hclockEq] at he1
    have he2 := hCcoeff p r hr j hj a b
    exact htriangle.trans (add_le_add (he1.trans hproduct) he2 |>.trans
      (by linarith only [hkappa]))

end PoincareConjecture.M47
