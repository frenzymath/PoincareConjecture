import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_ExponentialSard
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_SliceInverse
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_68_UniqueBranch
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_69_StableNeighborhood












set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}




theorem stable_image_contains_regular_point
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T tau x E)
    (q0 : (G.slices (T - tau)).Point)
    {A : Set (G.slices (T - tau)).Point} (hA : IsOpen A)
    {B : Set (G.Horizontal x)} (hB : IsCompact B)
    (hBD : ∀ Z ∈ B, (Z, Real.sqrt tau) ∈ E.domain)
    (hBmin : ∀ Z (hZB : Z ∈ B),
      M14IsMinimizing (E.path Z (Real.sqrt tau) (hBD Z hZB) (Real.sqrt_pos.mpr H.tau_pos)))
    (hmin : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p)
    (hcapture : ∀ q ∈ A, ∀ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p → ∃ Z ∈ B,
        EqOn p.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 tau) ∧
        survivalSliceMap E tau H.tau_pos.le q0 Z = q)
    {q : (G.slices (T - tau)).Point} (hq : q ∈ A)
    (hdiff : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun q' : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q'.val) q)
    (hcritical : q ∉ survivalSliceMap E tau H.tau_pos.le q0 ''
      {Z | ∃ hZ : (Z, Real.sqrt tau) ∈ E.domain,
        ¬ Function.Bijective (E.differential Z (Real.sqrt tau) hZ)}) :
    q ∈ H.endpoint_slice_map '' H.carrier := by
  have hregular (Z : G.Horizontal x) (hZ : (Z, Real.sqrt tau) ∈ E.domain)
      (hpoint : survivalSliceMap E tau H.tau_pos.le q0 Z = q) :
      Function.Bijective (E.differential Z (Real.sqrt tau) hZ) := by
    by_contra hbad
    exact hcritical ⟨Z, ⟨hZ, hbad⟩, hpoint⟩
  obtain ⟨p, hp⟩ := hmin q hq
  obtain ⟨Z, hZB, _, hpoint⟩ := hcapture q hq p hp
  have hZD := hBD Z hZB
  have hbij := hregular Z hZD hpoint
  have hfiber : ∀ W ∈ B,
      survivalSliceMap E tau H.tau_pos.le q0 W =
        survivalSliceMap E tau H.tau_pos.le q0 Z → W = Z := by
    intro W hWB hWZ
    have hWq := hWZ.trans hpoint
    exact minimizing_branches_unique_of_differentiable hM04 hM12 LG E H.tau_pos q0
      hA hmin (hBD W hWB) hZD (hWq.symm ▸ hq) hWZ (hBmin W hWB) (hBmin Z hZB)
      (hregular W (hBD W hWB) hWq) hbij (hWq.symm ▸ hdiff)
  obtain ⟨e, hZe, heD, hef⟩ := survivalSlice_local_inverse E H.tau_pos.le q0 hZD hbij
  have hstable := stableInitialVector_of_compact_capture E H.tau_pos q0 hA hB hBD
    hmin hcapture hZD (hpoint.symm ▸ hq) hfiber hbij e hZe heD hef
  have hcarrier : Z ∈ H.carrier := (H.carrier_exact Z).mpr hstable
  refine ⟨Z, hcarrier, ?_⟩
  have heq : H.endpoint_slice_map Z = survivalSliceMap E tau H.tau_pos.le q0 Z := by
    apply Subtype.ext
    exact (H.endpoint_slice_map_val Z hcarrier).trans
      ((H.endpoint_map_eq Z hcarrier).trans (survivalSliceMap_val E H.tau_pos.le q0 hZD).symm)
  exact heq.trans hpoint





theorem stable_image_full_measure_of_compact_capture
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (H : M14StableSet G T tau x E)
    (q0 : (G.slices (T - tau)).Point)
    {A : Set (G.slices (T - tau)).Point} (hA : IsOpen A)
    {B : Set (G.Horizontal x)} (hB : IsCompact B)
    (hBD : ∀ Z ∈ B, (Z, Real.sqrt tau) ∈ E.domain)
    (hBmin : ∀ Z (hZB : Z ∈ B),
      M14IsMinimizing (E.path Z (Real.sqrt tau) (hBD Z hZB) (Real.sqrt_pos.mpr H.tau_pos)))
    (hmin : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p)
    (hcapture : ∀ q ∈ A, ∀ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p → ∃ Z ∈ B,
        EqOn p.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 tau) ∧
        survivalSliceMap E tau H.tau_pos.le q0 Z = q)
    (hlip : ∀ q ∈ A,
      q ∉ survivalSliceMap E tau H.tau_pos.le q0 ''
        {Z | ∃ hZ : (Z, Real.sqrt tau) ∈ E.domain,
          ¬ Function.Bijective (E.differential Z (Real.sqrt tau) hZ)} →
      ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsOpen S ∧ extChartAt (𝓡 n) q q ∈ S ∧
        S ⊆ (extChartAt (𝓡 n) q).target ∧
        ∃ K : ℝ≥0, LipschitzOnWith K
          ((fun q' : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q'.val) ∘
            (extChartAt (𝓡 n) q).symm) S) :
    calibratedMetricVolume (G.slices (T - tau)).metricOnPoints
      (A \ H.endpoint_slice_map '' H.carrier) = 0 := by
  let C := survivalSliceMap E tau H.tau_pos.le q0 ''
    {Z | ∃ hZ : (Z, Real.sqrt tau) ∈ E.domain,
      ¬ Function.Bijective (E.differential Z (Real.sqrt tau) hZ)}
  let N := {q : (G.slices (T - tau)).Point | q ∈ A \ C ∧
    ¬ MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun q' : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q'.val) q}
  have hN : calibratedMetricVolume (G.slices (T - tau)).metricOnPoints N = 0 :=
    comparison_nondifferentiability_null (G.slices (T - tau)).metricOnPoints
      (A \ C) (fun q hq => hlip q hq.1 hq.2)
  have hC : calibratedMetricVolume (G.slices (T - tau)).metricOnPoints C = 0 :=
    exponential_survival_criticalValues_null E H.tau_pos.le q0
  apply measure_mono_null _ (measure_union_null hN hC)
  intro q hq
  by_cases hc : q ∈ C
  · exact Or.inr hc
  by_cases hd : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ))
      (fun q' : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q'.val) q
  · exact (hq.2 (stable_image_contains_regular_point hM04 hM12 LG E H q0 hA hB hBD
      hBmin hmin hcapture hq.1 hd hc)).elim
  · exact Or.inl ⟨⟨hq.1, hc⟩, hd⟩

end PoincareConjecture.Proofs.M46
