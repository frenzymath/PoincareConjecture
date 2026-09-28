import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.ScalarFamily
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.EscapeCarrier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.Translation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Boundary.Reparameterization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Canonical.RoundCylinderCongruence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace RoundCylinderTranslation

theorem familyClose_pullback {δ ε : ℝ} {I : Set ℝ}
    (s : ℝ) {B : ℝ → RoundCylinderTwoTensor}
    (hδ : 0 < δ) (hδε : δ ≤ ε) (hI : ∀ u ∈ I, u < 1)
    (hB : RoundCylinderFamilyClose δ I B)
    (hsub : MapsTo (fun t : ℝ => t + s) (Ioo (-ε⁻¹) ε⁻¹) (Ioo (-δ⁻¹) δ⁻¹)) :
    RoundCylinderFamilyClose ε I (fun u => pullback s (B u)) := by
  obtain ⟨hsmooth, bound, hbound, hjet⟩ := hB
  refine ⟨fun u hu => smoothOn_pullback s (hsmooth u hu) hsub, bound,
    hbound.trans_le (pow_le_pow_left₀ hδ.le hδε 2), ?_⟩
  intro u hu z hz
  rw [jetErrorSquared_pullback]
  have horder : ⌊ε⁻¹⌋₊ ≤ ⌊δ⁻¹⌋₊ :=
    Nat.floor_mono ((inv_le_inv₀ (hδ.trans_le hδε) hδ).2 hδε)
  exact (DeepHorn.evolvingCylinderJetErrorSquared_mono (hI u hu)
    (B u) (space s z) horder).trans (hjet u hu (space s z) (hsub hz))

end RoundCylinderTranslation

namespace CompactKappa

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_strongNeck_of_translated_scalarFamily
    (K : AncientKappaSolution 3 M) (N : EpsilonNeck (K.flow.metric 0))
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) (hεhalf : ε < 1 / 2)
    (hNδ : N.epsilon ≤ δ) (q : UnitTwoSphere) (s : ℝ)
    (hsub : MapsTo (fun t : ℝ => t + s) (Ioo (-ε⁻¹) ε⁻¹) (Ioo (-δ⁻¹) δ⁻¹))
    (hR : 0 < (K.flow.connection 0).scalarCurvature (N.coordinate_map (q, s)))
    (hclose :
      let R := (K.flow.connection 0).scalarCurvature (N.coordinate_map (q, s))
      RoundCylinderFamilyClose δ (Ioc (-1 : ℝ) 0) (fun u z v w =>
        R * roundCylinderPullback (K.flow.metric (u / R)) N.coordinate_map z v w)) :
    ∃ Q : StrongEvolvingNeck K 0 ε,
      Q.center = N.coordinate_map (q, s) ∧
      Q.duration = ((K.flow.connection 0).scalarCurvature (N.coordinate_map (q, s)))⁻¹ ∧
      Q.terminal_neck.coordinate_map = N.coordinate_map ∘ RoundCylinderAffine.space 1 s ∧
      Q.terminal_neck.connection = K.flow.connection 0 := by
  let R := (K.flow.connection 0).scalarCurvature (N.coordinate_map (q, s))
  have hε : 0 < ε := hδ.trans_le hδε
  have hsubN : MapsTo (fun t : ℝ => 1 * t + s)
      (Ioo (-ε⁻¹) ε⁻¹) (Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) := by
    intro t ht
    simpa only [one_mul] using DeepHorn.neckInterval_subset N.epsilon_pos hNδ (hsub ht)
  have hspace : RoundCylinderAffine.space 1 s = RoundCylinderTranslation.space s := by
    funext z
    simp only [RoundCylinderAffine.space, RoundCylinderTranslation.space, one_mul]
  have htranslated := RoundCylinderTranslation.familyClose_pullback s hδ hδε
    (fun u hu => by linarith [hu.2]) hclose hsub
  have hactual : RoundCylinderFamilyClose ε (Ioc (-1 : ℝ) 0) (fun u z v w =>
      R * roundCylinderPullback (K.flow.metric (u / R))
        (N.coordinate_map ∘ RoundCylinderAffine.space 1 s) z v w) := by
    apply RoundCylinderFamilyClose.congr (B' := fun u => RoundCylinderTranslation.pullback s
      (fun z v w => R * roundCylinderPullback (K.flow.metric (u / R))
        N.coordinate_map z v w)) ?_ htranslated
    intro u _ z hz v w
    have hdom : RoundCylinderTranslation.space s z ∈ N.cylinderDomain := by
      refine ⟨mem_univ _, ?_⟩
      simpa only [RoundCylinderTranslation.space, one_mul] using hsubN hz
    have hf := (N.coordinate_map_smooth.contMDiffAt
      (N.cylinderDomain_open.mem_nhds hdom)).mdifferentiableAt (by simp)
    rw [hspace, RoundCylinderTranslation.metric_pullback_translate
      (K.flow.metric (u / R)) N.coordinate_map s z hf]
    rfl
  have hstatic : RoundCylinderClose ε 0 (fun z v w =>
      R * roundCylinderPullback (K.flow.metric 0)
        (N.coordinate_map ∘ RoundCylinderAffine.space 1 s) z v w) := by
    obtain ⟨hsmooth, B, hB, hbound⟩ := hactual
    have hz : (0 : ℝ) ∈ Ioc (-1 : ℝ) 0 := by constructor <;> norm_num
    exact ⟨by simpa only [zero_div] using hsmooth 0 hz,
      B, hB, by simpa only [zero_div] using hbound 0 hz⟩
  let neck := N.affineWithMetric (show (0 : ℝ) < 1 by norm_num) s hsubN
    (K.flow.metric 0) (K.flow.connection 0) hε hεhalf q hR hstatic
  have hmap : neck.coordinate_map = N.coordinate_map ∘ RoundCylinderAffine.space 1 s := rfl
  let Q : StrongEvolvingNeck K 0 ε := {
    time_mem := le_rfl
    center := N.coordinate_map (q, s)
    duration := R⁻¹
    duration_pos := inv_pos.mpr hR
    normalized_duration := inv_mul_cancel₀ hR.ne'
    terminal_neck := neck
    terminal_center := rfl
    terminal_epsilon := rfl
    terminal_connection := rfl
    metric_comparison := by simpa only [zero_add, hmap, R] using hactual }
  exact ⟨Q, rfl, rfl, rfl, rfl⟩

theorem eventually_strongNeck_centers_of_scalarFamily
    (K : AncientKappaSolution 3 M) {δ ε : ℝ} (N : StrongEvolvingNeck K 0 δ)
    (hδε : δ < ε) (hεhalf : ε < 1 / 2)
    (hfamily : ∀ᶠ x in 𝓝 N.center,
      let R := (K.flow.connection 0).scalarCurvature x
      RoundCylinderFamilyClose δ (Ioc (-1 : ℝ) 0) (fun u z v w =>
        R * roundCylinderPullback (K.flow.metric (u / R)) N.terminal_neck.coordinate_map z v w)) :
    ∀ᶠ x in 𝓝 N.center, ∃ Q : StrongEvolvingNeck K 0 ε, Q.center = x := by
  have hδ : 0 < δ := N.terminal_epsilon ▸ N.terminal_neck.epsilon_pos
  have hε : 0 < ε := hδ.trans hδε
  have hinv : ε⁻¹ < δ⁻¹ := (inv_lt_inv₀ hε hδ).mpr hδε
  let b := δ⁻¹ - ε⁻¹
  have hb : 0 < b := sub_pos.mpr hinv
  have hcenter : N.center ∈ N.terminal_neck.carrier := by
    rw [← N.terminal_center]
    exact N.terminal_neck.central_sphere_subset N.terminal_neck.center_on_central_sphere
  have haxis : (N.terminal_neck.coordinate_inverse N.center).2 = 0 := by
    rw [← N.terminal_center]
    exact ((N.terminal_neck.mem_central_sphere_iff _).mp
      N.terminal_neck.center_on_central_sphere).2
  have haxis_cont : ContinuousAt (fun x => (N.terminal_neck.coordinate_inverse x).2) N.center :=
    (N.terminal_neck.coordinate_inverse_smooth.contMDiffAt
      (N.terminal_neck.carrier_open.mem_nhds hcenter)).continuousAt.snd
  have haxis_near : ∀ᶠ x in 𝓝 N.center,
      (N.terminal_neck.coordinate_inverse x).2 ∈ Ioo (-b) b :=
    haxis_cont.preimage_mem_nhds (isOpen_Ioo.mem_nhds
      (by rw [haxis]; exact ⟨neg_lt_zero.mpr hb, hb⟩))
  have hRcenter : 0 < (K.flow.connection 0).scalarCurvature N.center := by
    simpa only [N.terminal_connection, N.terminal_center] using N.terminal_neck.scalar_center_pos
  have hRnear : ∀ᶠ x in 𝓝 N.center, 0 < (K.flow.connection 0).scalarCurvature x :=
    (K.flow.connection 0).continuous_scalarCurvature.continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds hRcenter)
  filter_upwards [hfamily, haxis_near, hRnear,
    N.terminal_neck.carrier_open.mem_nhds hcenter] with x hfamilyx hxaxis hxR hxN
  let q := (N.terminal_neck.coordinate_inverse x).1
  let s := (N.terminal_neck.coordinate_inverse x).2
  have hsub : MapsTo (fun t : ℝ => t + s)
      (Ioo (-ε⁻¹) ε⁻¹) (Ioo (-δ⁻¹) δ⁻¹) := by
    intro t ht
    change -b < s ∧ s < b at hxaxis
    dsimp only [b] at hxaxis
    constructor <;> linarith [ht.1, ht.2, hxaxis.1, hxaxis.2]
  have hmap : N.terminal_neck.coordinate_map (q, s) = x :=
    N.terminal_neck.coordinate_map_coordinate_inverse hxN
  obtain ⟨Q, hQ, _, _, _⟩ := exists_strongNeck_of_translated_scalarFamily K N.terminal_neck
    hδ hδε.le hεhalf N.terminal_epsilon.le q s hsub
    (by rwa [hmap]) (by simpa only [hmap] using hfamilyx)
  exact ⟨Q, hQ.trans hmap⟩

theorem eventually_strongNeck_centers_of_lt
    (K : AncientKappaSolution 3 M) {δ ε : ℝ} (N : StrongEvolvingNeck K 0 δ)
    (hδε : δ < ε) (hεsmall : ε < 1 / 200) :
    ∀ᶠ x in 𝓝 N.center, ∃ Q : StrongEvolvingNeck K 0 ε, Q.center = x := by
  apply eventually_strongNeck_centers_of_scalarFamily K N hδε
    (hεsmall.trans (by norm_num : (1 / 200 : ℝ) < 1 / 2))
  have hcompact := N.terminal_neck.isCompact_closure_carrier (K.complete 0 le_rfl)
  have hsmall : N.terminal_neck.epsilon < 1 / 200 := by
    rw [N.terminal_epsilon]
    exact hδε.trans hεsmall
  have hR : 0 < (K.flow.connection 0).scalarCurvature N.center := by
    simpa only [N.terminal_connection, N.terminal_center] using N.terminal_neck.scalar_center_pos
  have hclose : RoundCylinderFamilyClose N.terminal_neck.epsilon (Ioc (-1 : ℝ) 0)
      (fun u z v w => (K.flow.connection 0).scalarCurvature N.center *
        roundCylinderPullback (K.flow.metric (u / (K.flow.connection 0).scalarCurvature N.center))
          N.terminal_neck.coordinate_map z v w) := by
    rw [N.terminal_epsilon]
    simpa only [zero_add] using N.metric_comparison
  have hpersist := K.flow.eventually_scalarNormalized_neck_familyClose
    N.terminal_neck hcompact hsmall hR hclose
    (K.flow.connection 0).continuous_scalarCurvature.continuousAt.tendsto
  simpa only [N.terminal_epsilon] using hpersist

theorem exists_open_strongNeck_center_neighborhood
    (K : AncientKappaSolution 3 M) {δ ε : ℝ} (N : StrongEvolvingNeck K 0 δ)
    (hδε : δ < ε) (hεsmall : ε < 1 / 200) :
    ∃ U : Set M, IsOpen U ∧ N.center ∈ U ∧
      ∀ x ∈ U, ∃ Q : StrongEvolvingNeck K 0 ε, Q.center = x := by
  obtain ⟨U, hUsub, hUopen, hcenter⟩ := mem_nhds_iff.mp
    (eventually_strongNeck_centers_of_lt K N hδε hεsmall)
  exact ⟨U, hUopen, hcenter, fun x hx => hUsub hx⟩

end CompactKappa

end PoincareConjecture
