import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.ExponentialSublevel
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.ConfinedAttainment










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}



theorem actionConfinement_exponential_mem (C : ActionConfinement G T start x)
    (E : M14ExponentialFamily G T x) {b : ℝ} (hb : 0 < b)
    (hbStart : b ^ 2 ≤ T - start) {Z : G.Horizontal x}
    (hZ : (Z, b) ∈ E.domain) (hZaction : E.action Z b < C.barrier) :
    MapsTo (E.gamma Z) (Icc 0 b) C.cage := by
  have htrace := C.paths_mem (b ^ 2) (sq_pos_of_pos hb) hbStart
    (E.gamma Z b) (E.path Z b hZ hb) (by rwa [← E.action_eq Z b hZ hb])
  intro s hs
  have hsq : s ^ 2 ∈ Icc 0 (b ^ 2) :=
    ⟨sq_nonneg s, (sq_le_sq₀ hs.1 hb.le).mpr hs.2⟩
  have heq := E.path_coherent Z b hZ hb (s ^ 2) hsq
  rw [Real.sqrt_sq hs.1] at heq
  rw [← heq]
  exact htrace hsq





theorem exists_confined_slice_minimum
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    {b : ℝ} (hb : 0 < b) (hbStart : b ^ 2 ≤ T - start)
    {y0 : G.Point} (p0 : M14BackwardPath G T 0 (b ^ 2) x y0)
    (hp0 : M14BackwardLAction G p0 < C.barrier) :
    ∃ y : G.Point, ∃ p : M14BackwardPath G T 0 (b ^ 2) x y,
      M14IsMinimizing p ∧ M14BackwardLAction G p ≤ M14BackwardLAction G p0 ∧
      ∀ z : G.Point, ∀ q : M14BackwardPath G T 0 (b ^ 2) x z,
        M14BackwardLAction G p ≤ M14BackwardLAction G q := by
  classical
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let D := max 0 (M14BackwardLAction G p0)
  have hD : 0 ≤ D := le_max_left _ _
  have hDbarrier : D < C.barrier := max_lt
    (lt_of_le_of_lt (by positivity) C.barrier_large) hp0
  let B : Set (G.Horizontal x) := {Z | (Z, b) ∈ E.domain ∧ E.action Z b ≤ D}
  have hcompact : IsCompact B := exponential_action_sublevel_compact hM04 hM12 LG E hb hD
    C.cage_compact (fun Z hZ hZD =>
      actionConfinement_exponential_mem C E hb hbStart hZ (hZD.trans_lt hDbarrier))
  have hrepresent {z : G.Point} (q : M14BackwardPath G T 0 (b ^ 2) x z)
      (hq : M14BackwardLAction G q ≤ D) :
      ∃ Z ∈ B, E.action Z b ≤ M14BackwardLAction G q := by
    obtain ⟨p, hp⟩ := actionConfinement_attained hM12 C (sq_pos_of_pos hb) hbStart q
      (hq.trans_lt hDbarrier)
    obtain ⟨Z, hZsqrt, htrace, _⟩ := minimizing_exponential_branch LG E p hp
    have hZ : (Z, b) ∈ E.domain := by simpa only [Real.sqrt_sq hb.le] using hZsqrt
    have haction := (represented_minimizer_action E hb p hZ htrace).1
    exact ⟨Z, ⟨hZ, haction.le.trans ((hp q).trans hq)⟩, haction.le.trans (hp q)⟩
  obtain ⟨Z0, hZ0, _⟩ := hrepresent p0 (le_max_right _ _)
  have hcontinuous : ContinuousOn (fun Z => E.action Z b) B := by
    intro Z hZ
    have hcont := ((LG.exponential.action_differential T x E).2 Z b hZ.1 hb).1.continuousAt
    exact hcont.continuousWithinAt
  obtain ⟨Z, hZ, hmin⟩ := hcompact.exists_isMinOn ⟨Z0, hZ0⟩ hcontinuous
  let p := E.path Z b hZ.1 hb
  have hall (z : G.Point) (q : M14BackwardPath G T 0 (b ^ 2) x z) :
      M14BackwardLAction G p ≤ M14BackwardLAction G q := by
    rw [← E.action_eq Z b hZ.1 hb]
    by_cases hq : D ≤ M14BackwardLAction G q
    · exact hZ.2.trans hq
    · obtain ⟨W, hW, hWq⟩ := hrepresent q (le_of_not_ge hq)
      exact (hmin hW).trans hWq
  exact ⟨E.gamma Z b, p, hall _, hall _ p0, hall⟩

end PoincareConjecture.Proofs.M46
