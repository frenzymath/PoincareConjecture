import PoincareConjecture.Proofs.M32.Cor11_36.EndCutTransport
import PoincareConjecture.Proofs.M32.Cor11_36.Restriction
import PoincareConjecture.Proofs.M32.Thm11_31.Topology
import PoincareConjecture.Proofs.M32.Neck.NearbyTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected
import Mathlib.Topology.Connected.Clopen















set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32

private theorem center_mem_middleHalf
    {F : GeneralizedRicciFlowData.{u}} {t alpha : ℝ}
    (N : GeneralizedStrongNeck F t alpha) (ha : alpha < 1 / 2) :
    N.center ∈ (spatialNeck N ha).region (-alpha⁻¹ / 2) (alpha⁻¹ / 2) := by
  have hc := ((spatialNeck N ha).mem_central_sphere_iff N.center).mp
    N.center_on_central_sphere
  refine ⟨hc.1, ?_⟩
  rw [hc.2]
  have hi := inv_pos.mpr N.epsilon_pos
  constructor <;> linarith




theorem exists_hornCut_propagation :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 / 200 ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {T epsilon alpha rho q : ℝ}
        {E : GeneralizedFlowExtension F T} (horn : StrongHorn E epsilon),
        epsilon ≤ alpha → alpha ≤ tau → rho⁻¹ ^ 2 ≤ q / 2 →
        (∀ z ∈ horn.boundary_sphere,
          (E.extended.connection T).scalarCurvature z ≤ q / 2) →
        ∀ {s : Set (E.extended.slice T).carrier}, IsPreconnected s →
          s ⊆ horn.carrier →
          (∀ z ∈ s, q < (E.extended.connection T).scalarCurvature z) →
          ∀ N0 : TerminalStrongNeck E alpha, N0.center ∈ s →
            Nonempty (HornEndCut horn N0 rho) →
            ∀ N : TerminalStrongNeck E alpha, N.center ∈ s →
              Nonempty (HornEndCut horn N rho) := by
  obtain ⟨tau₁, ht₁, hsmall₁, hscalar⟩ := exists_strongNeck_scalarComparison.{u}
  obtain ⟨tau₂, ht₂, _, hmove⟩ := exists_nearby_compact_transport.{u}
  refine ⟨min tau₁ tau₂, lt_min ht₁ ht₂, (min_le_left _ _).trans hsmall₁, ?_⟩
  intro F T epsilon alpha rho q E horn hea ha hl hb s hs hsH hsR N0 hN0 hcut0 N hN
  classical
  have ha₁ : alpha ≤ tau₁ := ha.trans (min_le_left _ _)
  have ha₂ : alpha ≤ tau₂ := ha.trans (min_le_right _ _)
  have hahalf : alpha < 1 / 2 := ha₁.trans_lt (hsmall₁.trans_lt (by norm_num))
  choose original hcenter using fun x : s => horn.every_point_neck x (hsH x.property)
  let chosen (x : s) : TerminalStrongNeck E alpha :=
    restrictNeckAccuracy (original x) hea
  have hchosen (x : s) : (chosen x).center = x := hcenter x
  let spatial (x : s) := spatialNeck (chosen x) hahalf
  have hhigh (x : s) (z : (E.extended.slice T).carrier) (hz : z ∈ (chosen x).carrier) :
      q / 2 < (E.extended.connection T).scalarCurvature z := by
    have hh := (hscalar (chosen x) ha₁ z hz).1
    rw [hchosen x] at hh
    linarith [hsR x x.property]
  have hinside (x : s) : (chosen x).carrier ⊆ horn.carrier := by
    apply horn_subset_carrier_of_isPreconnected horn
      (spatial x).isConnected_carrier.isPreconnected
    · refine ⟨x, ?_, hsH x.property⟩
      rw [← hchosen x]
      exact (chosen x).central_sphere_subset (chosen x).center_on_central_sphere
    · exact disjoint_left.mpr (fun z hz hzb => (hhigh x z hz).not_ge (hb z hzb))
  have hcompare (x : s) (N' : TerminalStrongNeck E alpha)
      (hmid : N'.center ∈ (spatial x).region (-alpha⁻¹ / 2) (alpha⁻¹ / 2)) :
      Nonempty (HornEndCut horn (chosen x) rho) ↔ Nonempty (HornEndCut horn N' rho) := by
    obtain ⟨e, K, hK, hKN, hfix, _, hsphere⟩ :=
      hmove N0.epsilon_pos ha₂ (spatial x) (spatialNeck N' hahalf) rfl rfl hmid
    apply hornEndCut_nonempty_iff_of_compact_transport horn (chosen x) N' e K hK
      (hKN.trans (hinside x)) _ hfix hsphere
    exact disjoint_left.mpr (fun z hz hzl =>
      (hl.trans_lt (hhigh x z (hKN hz))).not_ge hzl)
  have hsame (x : s) (N' : TerminalStrongNeck E alpha) (hc : N'.center = x) :
      Nonempty (HornEndCut horn (chosen x) rho) ↔ Nonempty (HornEndCut horn N' rho) := by
    apply hcompare x N'
    rw [hc, ← hchosen x]
    exact center_mem_middleHalf (chosen x) hahalf
  let : PreconnectedSpace s := Subtype.preconnectedSpace hs
  let P (x y : s) : Prop :=
    Nonempty (HornEndCut horn (chosen x) rho) ↔ Nonempty (HornEndCut horn (chosen y) rho)
  have hlocal (x : s) : ∀ᶠ y in 𝓝 x, P x y ∧ P y x := by
    have hneighborhood : {y : s | (y : (E.extended.slice T).carrier) ∈
        (spatial x).region (-alpha⁻¹ / 2) (alpha⁻¹ / 2)} ∈ 𝓝 x := by
      apply (((spatial x).isOpen_region _ _).preimage continuous_subtype_val).mem_nhds
      change (x : (E.extended.slice T).carrier) ∈
        (spatial x).region (-alpha⁻¹ / 2) (alpha⁻¹ / 2)
      rw [← hchosen x]
      exact center_mem_middleHalf (chosen x) hahalf
    filter_upwards [hneighborhood] with y hy
    have hi := hcompare x (chosen y) (by rwa [hchosen y])
    exact ⟨hi, hi.symm⟩
  have hprop : P ⟨N0.center, hN0⟩ ⟨N.center, hN⟩ :=
    PreconnectedSpace.induction₂' P hlocal ⟨fun _ _ _ hxy hyz => hxy.trans hyz⟩ _ _
  exact (hsame ⟨N.center, hN⟩ N rfl).mp
    (hprop.mp ((hsame ⟨N0.center, hN0⟩ N0 rfl).mpr hcut0))

end PoincareConjecture.M32
