import PoincareLib.Geometry.RicciFlow.Compactness.LocalControl
import PoincareLib.Geometry.RicciFlow.MetricComparison
import PoincareLib.Geometry.Riemannian.Curvature.NormBounds

/-!
# Precompact local cylinders at every interior time

The two-time curvature hypothesis compares each interior-time ball to a
uniformly larger zero-time ball. The latter is eventually precompact, so
the former is eventually precompact simultaneously at every interior time.
Diagonal selection retains this property on every earlier integer-radius
stage together with curvature control and the fixed noncollapse scale.

These are local-cylinder inputs to Morgan--Tian, Theorem 3.28, p. 51, and
Proposition 5.14, pp. 90--91. Positive-order Shi derivative estimates and
normal-coordinate extraction remain separate proof obligations.
-/

set_option autoImplicit false
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.PointedRicciFlowCompactnessHypotheses

/-- All reference-time balls of a fixed radius lie in uniformly bounded balls
at any other time, with one eventual threshold for every pair of times. -/
theorem exists_uniform_ball_containment
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ k in Filter.atTop,
      ∀ s ∈ Set.Ioo T' T, ∀ t ∈ Set.Ioo T' T,
        (H.sequence.flow k).ballAt s A ⊆ (H.sequence.flow k).ballAt t B := by
  obtain ⟨K, hK, hcurv⟩ := H.all_time_curvature_control A hA
  let L : ℝ := (n : ℝ) ^ 3 * K
  have hL : 0 ≤ L := mul_nonneg (by positivity) hK
  refine ⟨Real.exp (L * (T - T')) * A, mul_pos (Real.exp_pos _) hA, ?_⟩
  filter_upwards [hcurv] with k hk
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : T2Space C.carrier := C.t2Space
  intro s hs t ht
  have hRic : ∀ τ ∈ Set.Ioo T' T, ∀ x ∈ F.ballAt s A,
      ∀ v : C.tangent x,
        |(F.flow.connection τ).ricci x v v| ≤ L * (F.flow.metric τ).inner x v v := by
    intro τ hτ x hx v
    have hQ : 0 ≤ (F.flow.metric τ).inner x v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact ((F.flow.metric τ).pos x v hv).le
    have hnorm := (F.flow.connection τ).abs_ricci_quadratic_le_curvatureTensorNorm x v
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hk s hs τ hτ x hx) (by positivity)) hQ)
  have hball := F.flow.ball_subset_ball_of_ricci_bound (convex_Ioo T' T)
    (Set.Subset.refl _) F.base A L hs ht hRic
  have htime : |t - s| ≤ T - T' := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  intro x hx
  have hx' := hball hx
  exact hx'.trans_le (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htime hL)) hA.le))

/-- The eventual compactness threshold for a fixed radius works at every
interior time, despite the frozen input mentioning only zero-time balls. -/
theorem eventually_all_time_ball_compact
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (A : ℝ) (hA : 0 < A) :
    ∀ᶠ k in Filter.atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      ∀ t ∈ Set.Ioo T' T, IsCompact (closure (F.ballAt t A)) := by
  obtain ⟨B, hB, hcontain⟩ := H.exists_uniform_ball_containment A hA
  filter_upwards [hcontain, H.zero_time_ball_compact B hB] with k hk hcompact
  let C := H.sequence.carrier k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  change ∀ t ∈ Set.Ioo T' T, IsCompact (closure ((H.sequence.flow k).ballAt t A))
  intro t ht
  apply hcompact.of_isClosed_subset isClosed_closure
  exact closure_mono (hk t ht 0 ⟨H.time_bounds.1, H.time_bounds.2⟩)

/-- A single subsequence supplies precompact reference balls at every interior
time and two-time curvature bounds on all earlier integer-radius stages. -/
theorem exists_uniform_interior_local_control
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T) :
    ∃ r₀ κ : ℝ, 0 < r₀ ∧ 0 < κ ∧
      ∃ K : ℕ → ℝ, (∀ j, 0 ≤ K j) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k,
          ENNReal.ofReal (κ * r₀ ^ n) ≤ (H.sequence.flow (φ k)).zeroBallVolume r₀ ∧
          ∀ j, j ≤ k →
            let C := H.sequence.carrier (φ k)
            let F := H.sequence.flow (φ k)
            letI : TopologicalSpace C.carrier := C.topologicalSpace
            letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
            letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
            (∀ s ∈ Set.Ioo T' T, IsCompact (closure (F.ballAt s (j + 1)))) ∧
              ∀ s ∈ Set.Ioo T' T, ∀ t ∈ Set.Ioo T' T,
                ∀ x ∈ F.ballAt s (j + 1),
                  (F.flow.connection t).curvatureTensorNorm x ≤ K j := by
  obtain ⟨r₀, κ, hr₀, hκ, hvolume⟩ := H.noncollapsing
  choose K hK hbound using fun j : ℕ =>
    H.all_time_curvature_control (j + 1) (by positivity)
  have hlocal (j : ℕ) :=
    (H.eventually_all_time_ball_compact (j + 1) (by positivity)).and (hbound j)
  obtain ⟨φ, hφ, hstage⟩ :=
    Poincare.exists_strictMono_forall_le_of_eventually
      (fun j => hvolume.and (hlocal j))
  exact ⟨r₀, κ, hr₀, hκ, K, hK, φ, hφ, fun k =>
    ⟨(hstage k 0 (Nat.zero_le k)).1, fun j hj => (hstage k j hj).2⟩⟩

end PoincareMT.PointedRicciFlowCompactnessHypotheses
