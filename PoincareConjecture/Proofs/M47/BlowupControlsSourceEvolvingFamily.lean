import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingModel
import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingTensor










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

private theorem source_jet_sub_triangle {f k g : V → ℝ} {x : V}
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




theorem exists_actualCap_evolving_family_tolerance
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {theta A v gamma : ℝ} (htheta : theta < 1) (hA : 0 < A) (hvtheta : v ≤ theta)
    {z : StandardCapSpace}
    (N : StandardEvolvingNeck standard.atlas standard.flow v gamma z
      (Ioc (-(1 + gamma)) 0))
    (E : EpsilonNeck (standard.flow.metric v)) (hge : gamma ≤ E.epsilon)
    (hmap : E.coordinate_map = N.patch.coordinate)
    (hsource : E.carrier ⊆ g0.metric.ball 0 A) :
    ∃ lambda eta0 delta : ℝ,
      lambda ∈ Ioo (0 : ℝ) 1 ∧ 0 < eta0 ∧ 0 < delta ∧
      (∀ s rho c : ℝ, |s - v| < delta →
        |rho - (standard.flow.connection v).scalarCurvature z| < delta → |c| < delta →
        0 < rho ∧ |c| < (1 - lambda) * E.epsilon⁻¹ ∧
        RoundCylinderFamilyClose E.epsilon (Icc (-1 : ℝ) 0)
          (fun u p a b => rho * neckAxialTensorPullback lambda c
            (roundCylinderPullback (standard.flow.metric (s + u / rho)) E.coordinate_map)
            p a b)) ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S standard.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (hh : 0 < F.parameters.h t) (s rho c : ℝ), s ≤ theta →
      Icc 0 s ⊆ J → |s - v| < delta →
      |rho - (standard.flow.connection v).scalarCurvature z| < delta → |c| < delta →
      ∃ hclock : MapsTo (fun u : ℝ => s + u / rho) (Icc (-1 : ℝ) 0) J,
        RoundCylinderFamilyClose E.epsilon (Icc (-1 : ℝ) 0)
          (sourceCapNeckTensor e initial comparison hh E
            (fun u : ℝ => s + u / rho) hclock rho lambda c) := by
  let q := (standard.flow.connection v).scalarCurvature z
  have hq : 0 < q := N.scalar_pos
  obtain ⟨lambda, hlambda, hbase, hmodel⟩ :=
    exists_standard_evolving_model_jet_buffer standard N (hvtheta.trans_lt htheta) E hge hmap
  let D : ℝ → RoundCylinderTwoTensor := fun u p a b => q *
    neckAxialTensorPullback lambda 0
      (roundCylinderPullback (standard.flow.metric (v + u / q)) E.coordinate_map) p a b
  obtain ⟨kappa, hkappa, hfamily⟩ :=
    exists_source_neck_family_coefficient_tolerance E.epsilon_pos D hbase
  obtain ⟨dmodel, hdmodel, hmodelJets⟩ := hmodel (kappa / 2) (half_pos hkappa)
  obtain ⟨dclock, hdclock, hclockNear⟩ := exists_source_evolving_clock_tolerance hq
    (standard_evolving_neck_birth_gap N) zero_lt_one
  let L := q + 1
  have hL : 0 < L := by dsimp only [L]; linarith only [hq]
  let m := Nat.floor E.epsilon⁻¹
  obtain ⟨C, hC, hphysical⟩ := exists_actualCap_fixed_neck_coefficient_error_bound
    standard htheta hA hL E hsource m le_rfl
  let eta0 := min (1 / ((m : ℝ) + 1)) (kappa / (2 * C))
  have heta0 : 0 < eta0 := lt_min (by positivity) (div_pos hkappa (by positivity))
  let delta := min (min dmodel dclock) 1
  have hdelta : 0 < delta := lt_min (lt_min hdmodel hdclock) zero_lt_one
  have hdM : delta ≤ dmodel := (min_le_left _ _).trans (min_le_left _ _)
  have hdC : delta ≤ dclock := (min_le_left _ _).trans (min_le_right _ _)
  have hd1 : delta ≤ 1 := min_le_right _ _
  let model (s rho c : ℝ) : ℝ → RoundCylinderTwoTensor := fun u p a b =>
    rho * neckAxialTensorPullback lambda c
      (roundCylinderPullback (standard.flow.metric (s + u / rho)) E.coordinate_map) p a b
  have hmodelSmooth (s rho c : ℝ)
      (hc : |c| < (1 - lambda) * E.epsilon⁻¹) (u : ℝ) :
      RoundCylinderTensorSmoothOn E.epsilon (model s rho c u) := by
    let B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun p =>
      let T : E₃ →L[ℝ] E₃ →L[ℝ] ℝ :=
        (standard.flow.metric (s + u / rho)).inner (E.coordinate_map p)
      let J := mfderiv Ic (𝓡 3) E.coordinate_map p
      T.bilinearComp J J
    have hB : RoundCylinderTensorSmoothOn E.epsilon (fun p a b => B p a b) :=
      capPersistence_roundCylinderTensorSmoothOn_pullback
        (standard.flow.metric (s + u / rho)) E.coordinate_map_smooth
    exact (roundCylinderTensorSmoothOn_neckAxialTensorPullback
      E.epsilon_pos hlambda hc B hB).const_mul
  refine ⟨lambda, eta0, delta, hlambda, heta0, hdelta, ?_, ?_⟩
  · intro s rho c hs hrho hc
    obtain ⟨hrhoPos, hshift, hjets⟩ := hmodelJets s rho c
      (hs.trans_le hdM) (hrho.trans_le hdM) (hc.trans_le hdM)
    refine ⟨hrhoPos, hshift, hfamily (model s rho c)
      (fun u _ => hmodelSmooth s rho c hshift u) ?_⟩
    intro u hu p r hr j hj i l
    exact ((hjets u hu).2 p r ⟨hr.1.le, hr.2.le⟩ j hj i l).le.trans
      (half_le_self hkappa.le)
  · intro F hinitial S hS t hT hn i J U e initial eta heta hetaSmall comparison hh
      s rho c hst hJ hs hrho hc
    obtain ⟨hrhoPos, hshift, hjets⟩ := hmodelJets s rho c
      (hs.trans_le hdM) (hrho.trans_le hdM) (hc.trans_le hdM)
    obtain ⟨_, hclockTimes⟩ := hclockNear s rho (hs.trans_le hdC) (hrho.trans_le hdC)
    have hclock : MapsTo (fun u : ℝ => s + u / rho) (Icc (-1 : ℝ) 0) J := by
      intro u hu
      exact hJ ⟨(hclockTimes u hu).1.1.le, (hclockTimes u hu).1.2⟩
    have hrhoL : rho ≤ L := by
      have h := (abs_lt.mp (hrho.trans_le hd1)).2
      dsimp only [L]
      linarith only [h]
    have hetaOrder : eta ≤ 1 / ((m : ℝ) + 1) := hetaSmall.trans (min_le_left _ _)
    have hproduct : C * eta ≤ kappa / 2 := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp
        (hetaSmall.trans (min_le_right _ _))
      nlinarith only [h]
    have herr := hphysical F hinitial S hS t hT hn i J U e initial eta heta hetaOrder
      comparison hh
    cases hinitial
    cases hS
    let B := sourceCapNeckTensor e initial comparison hh E
      (fun u : ℝ => s + u / rho) hclock rho lambda c
    have hBsmooth := sourceCapNeckTensor_smooth e initial comparison hh E
      (fun u : ℝ => s + u / rho) hclock rho lambda c hsource hlambda hshift
    have herror := sourceCapNeckTensor_coefficient_error_le e initial comparison hh E
      (fun u : ℝ => s + u / rho) hclock rho lambda c hsource hlambda hshift m (C * eta)
      (fun u hu => herr (s + u / rho) (hclock hu)
        ((hclockTimes u hu).1.2.trans hst) rho hrhoPos hrhoL)
    refine ⟨hclock, hfamily B hBsmooth ?_⟩
    intro u hu p r hr j hj i l
    have hpoint : (0, r) ∈ (chartAt E₂ p).target ×ˢ
        Ioo (-E.epsilon⁻¹) E.epsilon⁻¹ := by
      refine ⟨?_, hr⟩
      rw [roundCylinder_sphereChart_target]
      trivial
    have hnhds := ((chartAt E₂ p).open_target.prod isOpen_Ioo).mem_nhds hpoint
    have hf := (hBsmooth u hu p i l).contDiffAt hnhds
    have hk := (hmodelSmooth s rho c hshift u p i l).contDiffAt hnhds
    have hg := (hbase.1 u hu p i l).contDiffAt hnhds
    have htriangle := source_jet_sub_triangle hf hk hg j
    have he1 := herror u hu p r ⟨hr.1.le, hr.2.le⟩ j hj i l
    have he2 := (hjets u hu).2 p r ⟨hr.1.le, hr.2.le⟩ j hj i l
    exact htriangle.trans (add_le_add (he1.trans hproduct) he2.le |>.trans
      (by linarith only [hkappa]))

end PoincareConjecture.M47
