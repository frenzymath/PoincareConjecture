import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.Configuration
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.PathCongruence

/-!
# The stable image of an open comparison region

Morgan--Tian, completion of Proposition 16.1, printed p. 394, following
Claim 16.27, pp. 391-392. An open comparison region retains its volume
after intersection with a full-measure stable image, and its global
reduced-length bound becomes the normalized exponential bound of
Theorem 8.1(4)-(5). The construction of the comparison region and its
null exceptional set are separate geometric obligations.
-/

set_option autoImplicit false
-- The history and its slice realization retain the same chosen instances.
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareMT.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}

/-- The stable branch has the global reduced length at its actual slice
endpoint, Proposition 6.28, p. 117, as used on p. 394. -/
theorem stableEndpoint_reducedLength (H : M14StableSet G T tau x E)
    {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) :
    E.reduced_length Z (Real.sqrt tau) =
      M14ReducedLengthValue G T 0 tau x (H.endpoint_slice_map Z).val := by
  have ht : Real.sqrt tau ^ 2 = tau := Real.sq_sqrt H.tau_pos.le
  have hpos : 0 < Real.sqrt tau := Real.sqrt_pos.mpr H.tau_pos
  have hs := H.survivor Z hZ
  obtain ⟨p, htrace, hp, _⟩ := H.minimizing_path Z hZ
  have haction : E.action Z (Real.sqrt tau) =
      M14ActionValue G T 0 tau x (H.endpoint_map Z) := by
    rw [← M14.action_eq_actionValue_of_minimizing p hp]
    have hex : ∃ q : M14BackwardPath G T 0 (Real.sqrt tau ^ 2) x
        (E.gamma Z (Real.sqrt tau)),
        EqOn q.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 (Real.sqrt tau ^ 2)) ∧
        E.action Z (Real.sqrt tau) = M14BackwardLAction G q :=
      ⟨E.path Z (Real.sqrt tau) hs hpos,
        E.path_coherent Z (Real.sqrt tau) hs hpos,
        E.action_eq Z (Real.sqrt tau) hs hpos⟩
    rw [ht, ← H.endpoint_map_eq Z hZ] at hex
    obtain ⟨q, hqtrace, hqa⟩ := hex
    exact hqa.trans (M14.action_eq_of_curve_eqOn q p
      (fun _ hsmem => (hqtrace (Ioo_subset_Icc_self hsmem)).trans
        (htrace (Ioo_subset_Icc_self hsmem)).symm))
  rw [E.reduced_length_eq Z (Real.sqrt tau) hs hpos, haction,
    H.endpoint_slice_map_val Z hZ]
  rfl

/-- The source action bound `L/2` gives a uniform normalized reduced-length
bound once the backward time is at least `epsilon^2`, p. 394. -/
theorem reducedLength_le_of_action_bound {L epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hL : 0 ≤ L) (htau : epsilon ^ 2 ≤ tau)
    {y : G.Point} (haction : M14ActionValue G T 0 tau x y ≤ L / 2) :
    M14ReducedLengthValue G T 0 tau x y ≤ L / (4 * epsilon) := by
  have hroot : epsilon ≤ Real.sqrt tau := Real.le_sqrt_of_sq_le htau
  have hrootpos : 0 < Real.sqrt tau := hepsilon.trans_le hroot
  calc
    M14ReducedLengthValue G T 0 tau x y ≤ (L / 2) / (2 * Real.sqrt tau) :=
      div_le_div_of_nonneg_right haction (by positivity)
    _ ≤ (L / 2) / (2 * epsilon) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hroot (by norm_num))
    _ = L / (4 * epsilon) := by ring

/-- An open comparison region with null exceptional set yields the open
stable source and its unchanged volume, Proposition 16.1, p. 394. -/
theorem stable_source_of_open_comparison (H : M14StableSet G T tau x E)
    (A : Set (G.slices (T - tau)).Point) (hA : IsOpen A)
    {l0 V : ℝ}
    (hlength : ∀ q ∈ A, M14ReducedLengthValue G T 0 tau x q.val ≤ l0)
    (hvolume : ENNReal.ofReal V ≤
      calibratedMetricVolume (G.slices (T - tau)).metricOnPoints A)
    (hnull : calibratedMetricVolume (G.slices (T - tau)).metricOnPoints
      (A \ (H.endpoint_slice_map '' H.carrier)) = 0) :
    ∃ W : Set (G.Horizontal x), IsOpen W ∧ W ⊆ H.carrier ∧
      (∀ Z ∈ W, E.reduced_length Z (Real.sqrt tau) ≤ l0) ∧
      ENNReal.ofReal V ≤
        calibratedMetricVolume (G.slices (T - tau)).metricOnPoints
          (H.endpoint_slice_map '' W) := by
  let W : Set (G.Horizontal x) := H.carrier ∩ H.endpoint_slice_map ⁻¹' A
  have himage : H.endpoint_slice_map '' W =
      A ∩ (H.endpoint_slice_map '' H.carrier) := by
    ext q
    constructor
    · rintro ⟨Z, ⟨hZ, hZA⟩, rfl⟩
      exact ⟨hZA, ⟨Z, hZ, rfl⟩⟩
    · rintro ⟨hqA, Z, hZ, rfl⟩
      exact ⟨Z, ⟨hZ, hqA⟩, rfl⟩
  refine ⟨W, H.endpoint_slice_continuous.isOpen_inter_preimage
    H.carrier_open hA, inter_subset_left, ?_, ?_⟩
  · intro Z hZ
    rw [stableEndpoint_reducedLength H hZ.1]
    exact hlength _ hZ.2
  · rw [himage, measure_inter_conull' hnull]
    exact hvolume

/-- The comparison-region output has exactly the stable-source fields
fixed in the assembly interface, Proposition 16.1, p. 394. -/
theorem stableSource_of_comparison
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} (history : HalfRadiusHistory D)
    {taubar l0 V tau : ℝ}
    (E : M14ExponentialFamily history.spacetime.geometry.toLGeometry D.time
      ((history.spacetime.geometry.sliceIdentification D.time).identification
        history.center).val)
    (H : M14StableSet history.spacetime.geometry.toLGeometry D.time tau
      ((history.spacetime.geometry.sliceIdentification D.time).identification
        history.center).val E)
    (htau : tau ≤ taubar) (hradius : (D.radius / 2) ^ 2 ≤ tau)
    (hterminal : D.time - tau ∈
      history.spacetime.history.generalized.interval)
    (A : Set (history.spacetime.geometry.toLGeometry.slices (D.time - tau)).Point)
    (hA : IsOpen A)
    (hlength : ∀ q ∈ A,
      M14ReducedLengthValue history.spacetime.geometry.toLGeometry D.time 0 tau
        ((history.spacetime.geometry.sliceIdentification D.time).identification
          history.center).val q.val ≤ l0)
    (hvolume : ENNReal.ofReal V ≤ calibratedMetricVolume
      (history.spacetime.geometry.toLGeometry.slices (D.time - tau)).metricOnPoints A)
    (hnull : calibratedMetricVolume
      (history.spacetime.geometry.toLGeometry.slices (D.time - tau)).metricOnPoints
      (A \ (H.endpoint_slice_map '' H.carrier)) = 0) :
    Nonempty (StableSource history taubar l0 V) := by
  obtain ⟨W, hW, hWH, hlW, hvW⟩ :=
    stable_source_of_open_comparison H A hA hlength hvolume hnull
  exact ⟨{
    exponential := E
    tau := tau
    tau_pos := H.tau_pos
    tau_le := htau
    radius_sq_le := hradius
    terminal_mem := hterminal
    stable := H
    W := W
    W_open := hW
    W_subset := hWH
    reduced_length := hlW
    image_volume := hvW
  }⟩

end PoincareMT.Proofs.M46
