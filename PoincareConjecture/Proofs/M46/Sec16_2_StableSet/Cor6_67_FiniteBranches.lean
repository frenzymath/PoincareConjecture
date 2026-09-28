import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_FiniteInverse
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_FiniteMinimum
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_RegularImage

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal

universe u v

namespace PoincareConjecture.Proofs.M46

private theorem finite_smooth_chart_lower_envelope
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {ι : Type v} [Finite ι] {f : M → ℝ} {g : ι → M → ℝ}
    {q : M} {N : Set M} (hN : N ∈ 𝓝 q)
    (hupper : ∀ z ∈ N, ∀ i, f z ≤ g i z)
    (hattained : ∀ z ∈ N, ∃ i, f z = g i z)
    (hsm : ∀ i, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 1 (g i) q) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsOpen S ∧ extChartAt (𝓡 n) q q ∈ S ∧
      S ⊆ (extChartAt (𝓡 n) q).target ∧
      ∃ K : ℝ≥0, LipschitzOnWith K (f ∘ (extChartAt (𝓡 n) q).symm) S := by
  let e := extChartAt (𝓡 n) q
  have hcoord (i : ι) : ContDiffAt ℝ 1 (g i ∘ e.symm) (e q) := by
    have h := (contMDiffAt_iff.mp (hsm i)).2
    simpa only [e, writtenInExtChartAt, extChartAt_model_space_eq_id, Function.comp_def,
      PartialEquiv.refl_coe, id_eq, modelWithCornersSelf_coe, range_id,
      contDiffWithinAt_univ] using h
  have hNcoord : e.target ∩ e.symm ⁻¹' N ∈ 𝓝 (e q) := by
    apply inter_mem (extChartAt_target_mem_nhds (I := 𝓡 n) q)
    have hN' : N ∈ 𝓝 (e.symm (e q)) := by
      simpa only [e, extChartAt_to_inv] using hN
    exact (continuousAt_extChartAt_symm (I := 𝓡 n) q).preimage_mem_nhds hN'
  obtain ⟨S, hS, hqS, hSsub, K, hLip⟩ :=
    finite_smooth_lower_envelope_locally_lipschitz hNcoord
      (fun z hz i => hupper (e.symm z) hz.2 i)
      (fun z hz => hattained (e.symm z) hz.2) hcoord
  exact ⟨S, hS, hqS, fun _ hz => (hSsub hz).1, K, hLip⟩

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}

theorem minimum_action_chart_lipschitz_of_compact_capture
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {A : Set (G.slices (T - tau)).Point} (hA : IsOpen A)
    {B : Set (G.Horizontal x)} (hB : IsCompact B)
    (hBD : ∀ Z ∈ B, (Z, Real.sqrt tau) ∈ E.domain)
    (hBmin : ∀ Z (hZB : Z ∈ B),
      M14IsMinimizing (E.path Z (Real.sqrt tau) (hBD Z hZB) (Real.sqrt_pos.mpr htau)))
    (hmin : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 tau x q.val, M14IsMinimizing p)
    (hcapture : ∀ q ∈ A, ∀ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p → ∃ Z ∈ B,
        EqOn p.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 tau) ∧
        survivalSliceMap E tau htau.le q0 Z = q)
    {q : (G.slices (T - tau)).Point} (hq : q ∈ A)
    (hcritical : q ∉ survivalSliceMap E tau htau.le q0 ''
      {Z | ∃ hZ : (Z, Real.sqrt tau) ∈ E.domain,
        ¬ Function.Bijective (E.differential Z (Real.sqrt tau) hZ)}) :
    ∃ S : Set (EuclideanSpace ℝ (Fin n)), IsOpen S ∧ extChartAt (𝓡 n) q q ∈ S ∧
      S ⊆ (extChartAt (𝓡 n) q).target ∧
      ∃ K : ℝ≥0, LipschitzOnWith K
        ((fun q' : (G.slices (T - tau)).Point => M14ActionValue G T 0 tau x q'.val) ∘
          (extChartAt (𝓡 n) q).symm) S := by
  classical
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let : FiniteDimensional ℝ (G.Horizontal x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let : T2Space (G.Horizontal x) :=
    FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x
  let f := survivalSliceMap E tau htau.le q0
  let D := {Z : G.Horizontal x | (Z, Real.sqrt tau) ∈ E.domain}
  let K := {Z : G.Horizontal x // Z ∈ B ∧ f Z = q}
  have hsm : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (𝓡 n) ∞ f D := fun Z hZ =>
    (survivalSliceMap_smooth E htau.le q0 hZ).contMDiffWithinAt
  have hex (i : K) :
      ∃ e : OpenPartialHomeomorph (G.Horizontal x) (G.slices (T - tau)).Point,
        i.val ∈ e.source ∧ e.source ⊆ D ∧ EqOn e f e.source ∧
        ContMDiffOn (𝓡 n) (𝓘(ℝ, G.Horizontal x)) ∞ e.symm e.target := by
    have hiD := hBD i.val i.property.1
    have hbij : Function.Bijective (E.differential i.val (Real.sqrt tau) hiD) := by
      by_contra hbad
      exact hcritical ⟨i.val, ⟨hiD, hbad⟩, i.property.2⟩
    obtain ⟨e, hie, heD, hef, heinv, _⟩ := M09.exists_manifold_local_inverse f D
      (survival_domain_open E _) hsm i.val hiD
      ((survivalSliceMap_differential_bijective_iff E htau.le q0 hiD).mpr hbij)
    exact ⟨e, hie, heD, hef, heinv⟩
  choose e hsource heD hef hinv using hex
  have hf : ContinuousOn f B := fun Z hZ =>
    (survivalSliceMap_smooth E htau.le q0 (hBD Z hZ)).continuousAt.continuousWithinAt
  obtain ⟨J, V, hV, hqV, htargets, hcover⟩ :=
    finite_inverse_fiber_capture hB hf q e hsource hef
  let cost (i : J) (z : (G.slices (T - tau)).Point) :=
    E.action ((e i.val).symm z) (Real.sqrt tau)
  have hupper (z : (G.slices (T - tau)).Point) (hz : z ∈ A ∩ V) (i : J) :
      M14ActionValue G T 0 tau x z.val ≤ cost i z := by
    obtain ⟨p, hp⟩ := hmin z hz.1
    have htarget := htargets i.val i.property hz.2
    have hsrc := (e i.val).map_target htarget
    have hpoint : f ((e i.val).symm z) = z :=
      (hef i.val hsrc).symm.trans ((e i.val).right_inv htarget)
    have hfinite : M14FiniteValueDomain G T 0 tau x (f ((e i.val).symm z)).val := by
      rw [hpoint]
      exact M14.finiteValueDomain_of_minimizing p hp
    have h := actionValue_le_survival_action E htau q0 (heD i.val hsrc) hfinite
    change M14ActionValue G T 0 tau x (f ((e i.val).symm z)).val ≤ cost i z at h
    rwa [hpoint] at h
  have hattained (z : (G.slices (T - tau)).Point) (hz : z ∈ A ∩ V) :
      ∃ i : J, M14ActionValue G T 0 tau x z.val = cost i z := by
    obtain ⟨p, hp⟩ := hmin z hz.1
    obtain ⟨Z, hZB, _, hpoint⟩ := hcapture z hz.1 p hp
    have hZV : f Z ∈ V := by
      change survivalSliceMap E tau htau.le q0 Z ∈ V
      rw [hpoint]
      exact hz.2
    obtain ⟨i, hi, hZi⟩ := hcover Z hZB hZV
    have heq : (e i).symm z = Z :=
      (congrArg (e i).symm ((hef i hZi).trans hpoint)).symm.trans ((e i).left_inv hZi)
    refine ⟨⟨i, hi⟩, ?_⟩
    change M14ActionValue G T 0 tau x z.val = E.action ((e i).symm z) (Real.sqrt tau)
    rw [heq]
    have h := minimizing_survival_action_eq E htau q0 (hBD Z hZB) (hBmin Z hZB)
    rw [hpoint] at h
    exact h.symm
  have hcost (i : J) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 1 (cost i) q := by
    have hpair : ContMDiffOn (𝓡 n)
        ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ))) ∞
        (fun z => ((e i.val).symm z, Real.sqrt tau)) (e i.val).target :=
      (hinv i.val).prodMk contMDiffOn_const
    have ha := (LG.exponential.action_differential T x E).1.comp hpair
      (fun z hz => ⟨heD i.val ((e i.val).map_target hz), Real.sqrt_pos.mpr htau⟩)
    exact ((ha q (htargets i.val i.property hqV)).contMDiffAt
      ((e i.val).open_target.mem_nhds (htargets i.val i.property hqV))).of_le (by simp)
  exact finite_smooth_chart_lower_envelope ((hA.inter hV).mem_nhds ⟨hq, hqV⟩)
    hupper hattained hcost

theorem stable_image_full_measure_of_compact_minimizers
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
    (hmin : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 tau x q.val, M14IsMinimizing p)
    (hcapture : ∀ q ∈ A, ∀ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p → ∃ Z ∈ B,
        EqOn p.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 tau) ∧
        survivalSliceMap E tau H.tau_pos.le q0 Z = q) :
    calibratedMetricVolume (G.slices (T - tau)).metricOnPoints
      (A \ H.endpoint_slice_map '' H.carrier) = 0 :=
  stable_image_full_measure_of_compact_capture hM04 hM12 LG E H q0 hA hB hBD hBmin hmin
    hcapture (fun _ hq hcritical => minimum_action_chart_lipschitz_of_compact_capture LG E
      H.tau_pos q0 hA hB hBD hBmin hmin hcapture hq hcritical)

end PoincareConjecture.Proofs.M46
