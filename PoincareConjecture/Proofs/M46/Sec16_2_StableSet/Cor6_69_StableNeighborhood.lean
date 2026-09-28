import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Cor6_67_SurvivalSlice












set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T tau : ℝ} {x : G.Point}



theorem survival_compact_fiber_neighborhood
    (E : M14ExponentialFamily G T x) (htau : 0 ≤ tau)
    (q0 : (G.slices (T - tau)).Point)
    {B U : Set (G.Horizontal x)} (hB : IsCompact B)
    (hBD : ∀ Z ∈ B, (Z, Real.sqrt tau) ∈ E.domain)
    (hU : IsOpen U) {Z0 : G.Horizontal x} (hZU : Z0 ∈ U)
    (hfiber : ∀ Z ∈ B,
      survivalSliceMap E tau htau q0 Z = survivalSliceMap E tau htau q0 Z0 → Z = Z0) :
    ∃ V : Set (G.slices (T - tau)).Point, IsOpen V ∧
      survivalSliceMap E tau htau q0 Z0 ∈ V ∧
      ∀ Z ∈ B, survivalSliceMap E tau htau q0 Z ∈ V → Z ∈ U := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨metric⟩
  let f := survivalSliceMap E tau htau q0
  have hf : ContinuousOn f B := fun Z hZ =>
    (survivalSliceMap_smooth E htau q0 (hBD Z hZ)).continuousAt.continuousWithinAt
  have hclosed : IsClosed (f '' (B \ U)) :=
    ((hB.diff hU).image_of_continuousOn (hf.mono sdiff_subset)).isClosed
  refine ⟨(f '' (B \ U))ᶜ, hclosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨Z, hZ, heq⟩
    exact hZ.2 (hfiber Z hZ.1 heq ▸ hZU)
  · intro Z hZ hV
    by_contra hnot
    exact hV ⟨Z, ⟨hZ, hnot⟩, rfl⟩




theorem stableInitialVector_of_compact_capture
    (E : M14ExponentialFamily G T x) (htau : 0 < tau)
    (q0 : (G.slices (T - tau)).Point)
    {A : Set (G.slices (T - tau)).Point} (hA : IsOpen A)
    {B : Set (G.Horizontal x)} (hB : IsCompact B)
    (hBD : ∀ Z ∈ B, (Z, Real.sqrt tau) ∈ E.domain)
    (hmin : ∀ q ∈ A, ∃ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p)
    (hcapture : ∀ q ∈ A, ∀ p : M14BackwardPath G T 0 tau x q.val,
      M14IsMinimizing p → ∃ Z ∈ B,
        EqOn p.curve (fun s => E.gamma Z (Real.sqrt s)) (Icc 0 tau) ∧
        survivalSliceMap E tau htau.le q0 Z = q)
    {Z0 : G.Horizontal x} (hZ0 : (Z0, Real.sqrt tau) ∈ E.domain)
    (hcenter : survivalSliceMap E tau htau.le q0 Z0 ∈ A)
    (hfiber : ∀ Z ∈ B,
      survivalSliceMap E tau htau.le q0 Z = survivalSliceMap E tau htau.le q0 Z0 →
        Z = Z0)
    (hbij : Function.Bijective (E.differential Z0 (Real.sqrt tau) hZ0))
    (e : OpenPartialHomeomorph (G.Horizontal x) (G.slices (T - tau)).Point)
    (hZe : Z0 ∈ e.source)
    (heD : ∀ Z ∈ e.source, (Z, Real.sqrt tau) ∈ E.domain)
    (hef : EqOn e (survivalSliceMap E tau htau.le q0) e.source) :
    M14StableInitialVector G T tau x E Z0 := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨metric⟩
  let f := survivalSliceMap E tau htau.le q0
  obtain ⟨V, hV, hZV, hlocal⟩ := survival_compact_fiber_neighborhood
    E htau.le q0 hB hBD e.open_source hZe hfiber
  let U := e.source ∩ f ⁻¹' (A ∩ V)
  have hf : ContinuousOn f e.source := fun Z hZ =>
    (survivalSliceMap_smooth E htau.le q0 (heD Z hZ)).continuousAt.continuousWithinAt
  have hU : IsOpen U := hf.isOpen_inter_preimage e.open_source (hA.inter hV)
  refine ⟨hZ0, hbij, U, hU, ⟨hZe, hcenter, hZV⟩, ?_⟩
  intro W hW
  have hWD : (W, Real.sqrt tau) ∈ E.domain := heD W hW.1
  have hunique_vector (p : M14BackwardPath G T 0 tau x (f W).val)
      (hp : M14IsMinimizing p) :
      EqOn p.curve (fun s => E.gamma W (Real.sqrt s)) (Icc 0 tau) := by
    obtain ⟨Z, hZB, htrace, hendpoint⟩ := hcapture (f W) hW.2.1 p hp
    have hZe' : Z ∈ e.source := hlocal Z hZB (hendpoint ▸ hW.2.2)
    have hZW : Z = W := e.injOn hZe' hW.1
      ((hef hZe').trans (hendpoint.trans (hef hW.1).symm))
    simpa only [hZW] using htrace
  obtain ⟨p, hp⟩ := hmin (f W) hW.2.1
  have hpath : ∃ p : M14BackwardPath G T 0 tau x (f W).val,
      EqOn p.curve (fun s => E.gamma W (Real.sqrt s)) (Icc 0 tau) ∧
      M14IsMinimizing p ∧
      ∀ q : M14BackwardPath G T 0 tau x (f W).val,
        M14IsMinimizing q → EqOn q.curve p.curve (Icc 0 tau) := by
    refine ⟨p, hunique_vector p hp, hp, ?_⟩
    intro q hq s hs
    exact (hunique_vector q hq hs).trans (hunique_vector p hp hs).symm
  refine ⟨hWD, ?_⟩
  rw [← survivalSliceMap_val E htau.le q0 hWD]
  exact hpath

end PoincareConjecture.Proofs.M46
