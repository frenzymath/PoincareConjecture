import PoincareConjecture.Proofs.M02.Topology.EmbeddedThreeChord

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open Set

universe u

namespace PoincareConjecture.Proofs.M02.Topology

def embeddedThreeNearest
    {N : Nat} {X : Type u} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (e : C(X, EuclideanSpace Real (Fin N))) : EuclideanSpace Real (Fin N) → X :=
  fun z => Classical.choose (isCompact_univ.exists_isMinOn Set.univ_nonempty
    ((continuous_const : Continuous (fun _ : X => z)).dist e.continuous).continuousOn)

theorem embeddedThreeNearest_minimal
    {N : Nat} {X : Type u} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (e : C(X, EuclideanSpace Real (Fin N)))
    (z : EuclideanSpace Real (Fin N)) (q : X) :
    dist z (e (embeddedThreeNearest e z)) ≤ dist z (e q) :=
  (Classical.choose_spec (isCompact_univ.exists_isMinOn Set.univ_nonempty
    ((continuous_const : Continuous (fun _ : X => z)).dist e.continuous).continuousOn)).2
      (Set.mem_univ q)

variable {N : Nat} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace Real (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_embedded_three_nearest_neighborhood
    [T2Space M] [CompactSpace M] [Nonempty M]
    (e : C(M, EuclideanSpace Real (Fin N)))
    (hs : ContMDiff (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) ∞ e)
    (he : _root_.Topology.IsClosedEmbedding e)
    (hi : ∀ p : M, Function.Injective
      (mfderiv (𝓡 3) (𝓘(Real, EuclideanSpace Real (Fin N))) e p)) :
    ∃ r : Real, 0 < r ∧
      ContinuousOn (embeddedThreeNearest e)
        {z | Metric.infDist z (Set.range e) < r} ∧
      (∀ (p : M) (v : EuclideanSpace Real (Fin N)),
        v ∈ (embeddedThreeTangent e p)ᗮ → ‖v‖ < r →
          embeddedThreeNearest e (e p + v) = p) := by
  classical
  obtain ⟨C, hC, hchord⟩ := exists_embedded_three_normal_chord_bound e hs he hi
  let r : Real := 1 / (4 * C)
  have hr : 0 < r := by dsimp [r]; positivity
  have hunique (p : M) (v : EuclideanSpace Real (Fin N))
      (hv : v ∈ (embeddedThreeTangent e p)ᗮ) (hnv : ‖v‖ < r)
      (q : M) (hq : dist (e p + v) (e q) ≤ dist (e p + v) (e p)) : q = p := by
    apply he.injective
    by_contra hne
    have hw : 0 < ‖e q - e p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hcoef : 0 < 1 - 2 * C * ‖v‖ := by
      have hsmall : ‖v‖ * (4 * C) < 1 :=
        (lt_div_iff₀ (by positivity : 0 < 4 * C)).mp hnv
      nlinarith only [hsmall]
    have heq : e p + v - e q = v - (e q - e p) := by abel
    have hq' : ‖v - (e q - e p)‖ ≤ ‖v‖ := by
      simpa only [dist_eq_norm, heq, add_sub_cancel_left] using hq
    have hsq := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hq'
    have hip : inner Real v (e q - e p) ≤ C * ‖v‖ * ‖e q - e p‖ ^ 2 :=
      (le_abs_self _).trans (hchord p q v hv)
    have hstrict := mul_pos hcoef (sq_pos_of_pos hw)
    nlinarith only [hsq, norm_sub_sq_real v (e q - e p), hip, hstrict]
  have hnormal (p : M) (v : EuclideanSpace Real (Fin N))
      (hv : v ∈ (embeddedThreeTangent e p)ᗮ) (hnv : ‖v‖ < r) :
      embeddedThreeNearest e (e p + v) = p :=
    hunique p v hv hnv _ (embeddedThreeNearest_minimal e (e p + v) p)
  have hnear (z : EuclideanSpace Real (Fin N))
      (hz : Metric.infDist z (Set.range e) < r) :
      ∀ q : M, dist z (e q) ≤ dist z (e (embeddedThreeNearest e z)) →
        q = embeddedThreeNearest e z := by
    obtain ⟨y, ⟨q0, rfl⟩, hy⟩ :=
      (Metric.infDist_lt_iff (Set.range_nonempty e)).mp hz
    have hn : ‖z - e (embeddedThreeNearest e z)‖ < r := by
      simpa only [dist_eq_norm] using
        lt_of_le_of_lt (embeddedThreeNearest_minimal e z q0) hy
    have hv : z - e (embeddedThreeNearest e z) ∈
        (embeddedThreeTangent e (embeddedThreeNearest e z))ᗮ :=
      embedded_three_nearest_normal e hs z _ (embeddedThreeNearest_minimal e z)
    intro q hq
    apply hunique (embeddedThreeNearest e z) _ hv hn q
    simpa only [add_sub_cancel] using hq
  refine ⟨r, hr, ?_, hnormal⟩
  intro z hz
  apply ContinuousAt.continuousWithinAt
  rw [continuousAt_def]
  intro U hU
  obtain ⟨V, hVU, hVo, hVz⟩ := mem_nhds_iff.mp hU
  let a : Real := dist z (e (embeddedThreeNearest e z))
  have hgap (q : M) (hq : q ∈ Vᶜ) : a < dist z (e q) := by
    by_contra hn
    have heq := hnear z hz q (le_of_not_gt hn)
    exact hq (heq ▸ hVz)
  obtain ⟨b, hab, hb⟩ := (isClosed_compl_iff.mpr hVo).isCompact.exists_forall_le'
    ((continuous_const : Continuous (fun _ : M => z)).dist e.continuous).continuousOn hgap
  let eta : Real := (b - a) / 3
  have heta : 0 < eta := by dsimp [eta]; linarith only [hab]
  apply Metric.mem_nhds_iff.mpr
  refine ⟨eta, heta, ?_⟩
  intro z' hz'
  apply hVU
  by_contra hout
  have hdist : dist z' z < eta := Metric.mem_ball.mp hz'
  have hlower := hb (embeddedThreeNearest e z') hout
  have hmin := embeddedThreeNearest_minimal e z' (embeddedThreeNearest e z)
  have hfirst := dist_triangle z z' (e (embeddedThreeNearest e z'))
  have hsecond := dist_triangle z' z (e (embeddedThreeNearest e z))
  rw [dist_comm z z'] at hfirst
  change dist z' (e (embeddedThreeNearest e z')) ≤
    dist z' (e (embeddedThreeNearest e z)) at hmin
  change dist z' (e (embeddedThreeNearest e z)) ≤ dist z' z + a at hsecond
  dsimp [eta] at hdist
  linarith only [hlower, hmin, hfirst, hsecond, hdist, hab]

end PoincareConjecture.Proofs.M02.Topology
