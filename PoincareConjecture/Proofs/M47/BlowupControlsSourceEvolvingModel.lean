import PoincareConjecture.Proofs.M47.BlowupControlsSourceEvolvingClock
import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineFields
import PoincareConjecture.Proofs.M47.CanonicalNeckBufferedFamily
import PoincareConjecture.Proofs.M45.Ch12_Standard.StandardNecks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "V" => RoundCylinderCoordinates

theorem exists_standard_evolving_neck_spatial_restriction
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma epsilon : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z (Ioc (-(1 + gamma)) 0))
    (hge : gamma ≤ epsilon) (hepsilon : epsilon < 1 / 2) :
    ∃ E : EpsilonNeck (G.metric v), E.epsilon = epsilon ∧
      E.connection = G.connection v ∧ E.center = z ∧
      E.coordinate_map = N.patch.coordinate ∧
      E.coordinate_inverse = N.patch.inverse := by
  have heps : 0 < epsilon := N.epsilon_pos.trans_le hge
  have hzero : (0 : ℝ) ∈ Ioc (-(1 + gamma)) 0 := by
    constructor <;> linarith only [N.epsilon_pos]
  let K := (N.staticAtZero hzero).toEpsilonNeck
  have hinv : epsilon⁻¹ ≤ K.epsilon⁻¹ := inv_anti₀ N.epsilon_pos hge
  have hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      (1 : ℝ) * s + 0 ∈ Ioo (-K.epsilon⁻¹) K.epsilon⁻¹ := by
    intro s hs
    simpa only [one_mul, add_zero] using
      (show s ∈ Ioo (-K.epsilon⁻¹) K.epsilon⁻¹ from
        ⟨(neg_le_neg hinv).trans_lt hs.1, hs.2.trans_le hinv⟩)
  obtain ⟨q, hq⟩ := N.patch.center_sphere
  have hcenter : K.coordinate_map (q, 0) = z := hq
  have hscalar : 0 < K.connection.scalarCurvature (K.coordinate_map (q, 0)) := by
    rw [hcenter]
    exact N.scalar_pos
  have hmap : K.coordinate_map ∘ neckAxialSpaceMap 1 0 = K.coordinate_map := by
    funext p
    simp only [Function.comp_apply, neckAxialSpaceMap, one_mul, add_zero]
  have hclose : RoundCylinderClose epsilon 0 (fun p a b =>
      K.connection.scalarCurvature (K.coordinate_map (q, 0)) *
        roundCylinderPullback (G.metric v)
          (K.coordinate_map ∘ neckAxialSpaceMap 1 0) p a b) := by
    rw [hmap, hcenter]
    exact (N.staticAtZero hzero).close.mono_epsilon
      N.epsilon_pos hge zero_lt_one
  let E := capAffineNeck K heps hepsilon zero_lt_one hdomain q hscalar hclose
  refine ⟨E, rfl, rfl, hcenter, ?_, ?_⟩
  · exact hmap
  · change neckAxialInverse 1 0 ∘ N.patch.inverse = N.patch.inverse
    funext p
    simp only [Function.comp_apply, neckAxialInverse, sub_zero, div_one]

theorem standard_evolving_neck_unit_family
    {g0 : StandardInitialMetric} {G : MaximalStandardCapFlow g0}
    {atlas : StandardCylinderAtlas} {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck atlas G v gamma z (Ioc (-(1 + gamma)) 0))
    (E : EpsilonNeck (G.metric v)) (hge : gamma ≤ E.epsilon)
    (hmap : E.coordinate_map = N.patch.coordinate) :
    RoundCylinderFamilyClose E.epsilon (Icc (-1 : ℝ) 0)
      (fun u p a b => (G.connection v).scalarCurvature z *
        roundCylinderPullback (G.metric (v + u / (G.connection v).scalarCurvature z))
          E.coordinate_map p a b) := by
  have hI : Icc (-1 : ℝ) 0 ⊆ Ioc (-(1 + gamma)) 0 := by
    intro u hu
    exact ⟨by linarith only [hu.1, N.epsilon_pos], hu.2⟩
  rw [hmap]
  apply RoundCylinderFamilyClose.mono_epsilon N.epsilon_pos hge
    (fun _ hu => hu.2.trans_lt zero_lt_one)
  obtain ⟨hsmooth, B, hB, hbound⟩ := N.close
  exact ⟨fun u hu => hsmooth u (hI hu), B, hB,
    fun u hu => hbound u (hI hu)⟩

theorem exists_standard_evolving_model_jet_buffer
    {g0 : StandardInitialMetric} (standard : RepairedStandardCapExistenceData g0)
    {v gamma : ℝ} {z : StandardCapSpace}
    (N : StandardEvolvingNeck standard.atlas standard.flow v gamma z
      (Ioc (-(1 + gamma)) 0)) (hv : v < 1)
    (E : EpsilonNeck (standard.flow.metric v)) (hge : gamma ≤ E.epsilon)
    (hmap : E.coordinate_map = N.patch.coordinate) :
    ∃ lambda : ℝ, lambda ∈ Ioo (0 : ℝ) 1 ∧
      RoundCylinderFamilyClose E.epsilon (Icc (-1 : ℝ) 0)
        (fun u p a b => (standard.flow.connection v).scalarCurvature z *
          neckAxialTensorPullback lambda 0
            (roundCylinderPullback
              (standard.flow.metric (v + u / (standard.flow.connection v).scalarCurvature z))
              E.coordinate_map) p a b) ∧
      ∀ nu : ℝ, 0 < nu → ∃ delta : ℝ, 0 < delta ∧
        ∀ s rho c : ℝ, |s - v| < delta →
          |rho - (standard.flow.connection v).scalarCurvature z| < delta →
          |c| < delta →
          0 < rho ∧ |c| < (1 - lambda) * E.epsilon⁻¹ ∧
          ∀ u ∈ Icc (-1 : ℝ) 0, s + u / rho ∈ Ioo (0 : ℝ) 1 ∧
            ∀ q : UnitTwoSphere, ∀ r ∈ Icc (-E.epsilon⁻¹) E.epsilon⁻¹,
              ∀ j ≤ Nat.floor E.epsilon⁻¹, ∀ i l : Fin 3,
                ‖iteratedFDeriv ℝ j (fun y =>
                    rho * roundCylinderTensorCoefficient
                      (neckAxialTensorPullback lambda c
                        (roundCylinderPullback (standard.flow.metric (s + u / rho))
                          E.coordinate_map)) (chartAt E₂ q) y i l -
                    (standard.flow.connection v).scalarCurvature z *
                      roundCylinderTensorCoefficient
                        (neckAxialTensorPullback lambda 0
                          (roundCylinderPullback
                            (standard.flow.metric (v + u /
                              (standard.flow.connection v).scalarCurvature z))
                            E.coordinate_map)) (chartAt E₂ q) y i l) (0, r)‖ < nu := by
  let G := standard.flow
  let q := (G.connection v).scalarCurvature z
  have hq : 0 < q := N.scalar_pos
  have hgap : 0 < v - q⁻¹ := standard_evolving_neck_birth_gap N
  let a := (v - q⁻¹) / 2
  let b := (v + 1) / 2
  have ha : 0 < a := half_pos hgap
  have hbottom : a < v - q⁻¹ := half_lt_self hgap
  have htop : v < b := by dsimp only [b]; linarith only [hv]
  have hb : b < 1 := by dsimp only [b]; linarith only [hv]
  have hav : a < v := hbottom.trans (sub_lt_self _ (inv_pos.mpr hq))
  have hab : a < b := hav.trans htop
  have hI : Icc a b ⊆ Ico 0 G.base.lifetime := by
    intro t ht
    refine ⟨ha.le.trans ht.1, ?_⟩
    rw [standard.lifetime_one]
    exact ht.2.trans_lt hb
  let F : RicciFlow 3 StandardCapSpace (Icc a b) := {
    metric := G.metric
    connection := G.connection
    interval := ordConnected_Icc
    nontrivial := ⟨a, ⟨le_rfl, hab.le⟩, b, ⟨hab.le, le_rfl⟩, hab.ne⟩
    smooth := G.base.flow.smooth.mono (prod_mono hI Subset.rfl)
    equation := fun t ht y w w' => (G.base.flow.equation t (hI ht) y w w').mono hI }
  let B0 : ℝ → RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun u p =>
    let T : E₃ →L[ℝ] E₃ →L[ℝ] ℝ := (G.metric (v + u / q)).inner (E.coordinate_map p)
    let J : V →L[ℝ] E₃ := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) E.coordinate_map p
    q • T.bilinearComp J J
  have hB0 : RoundCylinderFamilyClose E.epsilon (Icc (-1 : ℝ) 0)
      (fun u p a b => B0 u p a b) := standard_evolving_neck_unit_family N E hge hmap
  obtain ⟨lambda, hlambda, hcompression⟩ := exists_same_epsilon_neck_axial_compression
    E.epsilon_pos (fun _ hu => hu.2) B0 hB0
  have hzero : |(0 : ℝ)| < (1 - lambda) * E.epsilon⁻¹ := by
    rw [abs_zero]
    exact mul_pos (sub_pos.mpr hlambda.2) (inv_pos.mpr E.epsilon_pos)
  refine ⟨lambda, hlambda, hcompression 0 hzero, ?_⟩
  intro nu hnu
  have hnear := eventually_buffered_normalized_neck_jets hab F E hlambda
    (p0 := (v, q, (0 : ℝ))) (T := fun p : ℝ × ℝ × ℝ => p.1)
    (Q := fun p => p.2.1) (c := fun p => p.2.2)
    continuousAt_fst (continuousAt_fst.comp continuousAt_snd)
    (continuousAt_snd.comp continuousAt_snd) rfl hq hbottom htop
    (Nat.floor E.epsilon⁻¹) le_rfl hnu
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨delta, hdelta, ?_⟩
  intro s rho c hs hrho hc
  have hmem : (s, rho, c) ∈ Metric.ball (v, q, (0 : ℝ)) delta := by
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
      using ⟨hs, hrho, hc⟩
  obtain ⟨hpositive, hshift, htimes⟩ := hball hmem
  refine ⟨hpositive, hshift, ?_⟩
  intro u hu
  obtain ⟨htime, hjets⟩ := htimes u hu
  exact ⟨⟨ha.trans_le htime.1, htime.2.trans_lt hb⟩, hjets⟩

end PoincareConjecture.M47
