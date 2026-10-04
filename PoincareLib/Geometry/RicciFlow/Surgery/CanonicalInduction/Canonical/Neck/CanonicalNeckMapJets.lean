import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Coordinates.CapPersistenceChartJets
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Collar.Coordinates.ClosedTimeJets
import Mathlib.Topology.Order.Compact

/-!
# Actual neck map jets at the recorded derivative order

Proposition 9.79(3), p. 234, and Theorem 12.28, pp. 323-324.
The existing local-isometry estimate at index m-1 supplies every map
derivative needed to pull back m metric derivatives. Joint continuity
of the actual metric jets gives one included-time neighborhood on each
compact coordinate set. The full neck comparison is a later step.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M]

/-- Exactly the recorded metric order controls all coordinate map jets
needed for its pullback, uniformly before the neck center and height.
Proposition 9.79(3), p. 234. -/
theorem neck_chart_map_jets_at_recorded_order [T2Space M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (m : ℕ)
    (hm : m ≤ Nat.floor N.epsilon⁻¹) (a : M) {H : Set E₃}
    (hH : IsCompact H) (hHt : H ⊆ (extChartAt (𝓡 3) a).target) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (q : UnitTwoSphere) (z : ℝ),
      z ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      N.coordinate_map (q, z) ∈ (extChartAt (𝓡 3) a).source →
      (extChartAt (𝓡 3) a) (N.coordinate_map (q, z)) ∈ H →
      ∀ j ≤ m + 1, ‖iteratedFDeriv ℝ j
        ((extChartAt (𝓡 3) a) ∘ N.capPersistenceEuclideanMap q z) 0‖ ≤ D := by
  by_cases hm0 : m = 0
  · subst m
    have horder : 1 ≤ Nat.floor N.epsilon⁻¹ := by
      apply (Nat.le_floor_iff (inv_pos.mpr N.epsilon_pos).le).mpr
      rw [inv_eq_one_div, le_div_iff₀ N.epsilon_pos]
      norm_num only [Nat.cast_one, one_mul]
      linarith [N.epsilon_lt_half]
    obtain ⟨D, hD, hbound⟩ := N.exists_capPersistence_chart_jet_bound 0 horder a hH hHt
    exact ⟨D, hD, fun q z hz hsource hcenter j hj =>
      hbound q z hz hsource hcenter j (by omega)⟩
  · obtain ⟨D, hD, hbound⟩ := N.exists_capPersistence_chart_jet_bound (m - 1)
      (by omega) a hH hHt
    exact ⟨D, hD, fun q z hz hsource hcenter j hj =>
      hbound q z hz hsource hcenter j (by omega)⟩

/-- Actual fixed-coordinate metric differences have uniformly small
finite spatial jets near every included slab time, before all compact
coordinate points. Proposition 9.79(3), p. 234. -/
theorem metric_jets_uniform_near_time_on_compact
    {a b : ℝ} (hab : a < b) (F : RicciFlow 3 M (Icc a b))
    {U : Set E₃} (hU : IsOpen U) {e : E₃ → M}
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U)
    {H : Set E₃} (hH : IsCompact H) (hHU : H ⊆ U)
    (t : Icc a b) (m : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∀ x ∈ H, ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j (fun y =>
        (F.metric s.val).pullbackCoefficients e y -
          (F.metric t.val).pullbackCoefficients e y) x‖ < rho := by
  let : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have hj (j : Fin (m + 1)) : ∀ᶠ s : Icc a b in 𝓝 t, ∀ x ∈ H,
      ‖iteratedFDeriv ℝ j.val ((F.metric s.val).pullbackCoefficients e) x -
        iteratedFDeriv ℝ j.val ((F.metric t.val).pullbackCoefficients e) x‖ < rho := by
    have hc : Continuous (fun z : Icc a b × H =>
        iteratedFDeriv ℝ j.val ((F.metric z.1.val).pullbackCoefficients e) z.2.val) := by
      have hmap : Continuous (fun z : Icc a b × H => (z.1.val, z.2.val)) :=
        (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      have h := (M44.continuousOn_pullback_spatialJet hab F hU he j.val).comp_continuous
        hmap (fun z => ⟨z.1.property, hHU z.2.property⟩)
      exact h
    have hbase := hc.comp (continuous_const.prodMk continuous_snd :
      Continuous (fun z : Icc a b × H => (t, z.2)))
    have hdiff := (hc.sub hbase).norm
    have hnear : ∀ᶠ s : Icc a b in 𝓝 t, ∀ x : H, x ∈ (univ : Set H) →
        ‖iteratedFDeriv ℝ j.val ((F.metric s.val).pullbackCoefficients e) x.val -
          iteratedFDeriv ℝ j.val ((F.metric t.val).pullbackCoefficients e) x.val‖ < rho := by
      apply (isCompact_univ : IsCompact (univ : Set H)).eventually_forall_of_forall_eventually
      intro x _
      exact hdiff.continuousAt.eventually (Iio_mem_nhds (by
        change ‖iteratedFDeriv ℝ j.val ((F.metric t.val).pullbackCoefficients e) x.val -
          iteratedFDeriv ℝ j.val ((F.metric t.val).pullbackCoefficients e) x.val‖ < rho
        simpa only [sub_self, norm_zero] using hrho))
    filter_upwards [hnear] with s hs x hx
    exact hs ⟨x, hx⟩ (mem_univ _)
  filter_upwards [Filter.eventually_all.mpr hj] with s hs x hx j hjm
  have he' := he.contMDiffAt (hU.mem_nhds (hHU hx))
  have hnew := (F.metric s.val).contDiffAt_pullbackCoefficients he'
  have hold := (F.metric t.val).contDiffAt_pullbackCoefficients he'
  change ‖iteratedFDeriv ℝ j
    ((F.metric s.val).pullbackCoefficients e - (F.metric t.val).pullbackCoefficients e) x‖ < rho
  rw [iteratedFDeriv_sub_apply (hnew.of_le (by exact_mod_cast le_top))
    (hold.of_le (by exact_mod_cast le_top))]
  exact hs ⟨j, Nat.lt_succ_of_le hjm⟩ x hx

end PoincareMT.Proofs.M47
