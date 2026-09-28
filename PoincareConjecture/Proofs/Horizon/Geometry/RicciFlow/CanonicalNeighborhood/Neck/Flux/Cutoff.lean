import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension












set_option autoImplicit false

open Set Filter Function
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)


noncomputable def axialCutoff (φ : ℝ → ℝ) : M → ℝ :=
  N.carrier.indicator (fun x => φ (N.coordinate_inverse x).2)

theorem axialCutoff_eq_of_mem (φ : ℝ → ℝ) {x : M} (hx : x ∈ N.carrier) :
    N.axialCutoff φ x = φ (N.coordinate_inverse x).2 :=
  Set.indicator_of_mem hx _

theorem axialCutoff_eq_zero_of_not_mem (φ : ℝ → ℝ) {x : M}
    (hx : x ∉ N.carrier) : N.axialCutoff φ x = 0 :=
  Set.indicator_of_notMem hx _


theorem support_axialCutoff_subset {φ : ℝ → ℝ} {a b : ℝ}
    (hφ : support φ ⊆ Icc a b) :
    support (N.axialCutoff φ) ⊆ N.coordinate_map '' (univ ×ˢ Icc a b) := by
  intro x hx
  change N.axialCutoff φ x ≠ 0 at hx
  have hxc : x ∈ N.carrier := by
    by_contra hn
    exact hx (N.axialCutoff_eq_zero_of_not_mem φ hn)
  have hφx : φ (N.coordinate_inverse x).2 ≠ 0 := by
    simpa only [N.axialCutoff_eq_of_mem φ hxc] using hx
  refine ⟨N.coordinate_inverse x, ⟨mem_univ _, hφ hφx⟩, ?_⟩
  have hi := congrArg Subtype.val (N.coordinate_inverse_right x hxc)
  rw [N.coordinate_map_eq] at hi
  exact hi


theorem hasCompactSupport_axialCutoff {φ : ℝ → ℝ} {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹)
    (hφ : support φ ⊆ Icc a b) : HasCompactSupport (N.axialCutoff φ) :=
  HasCompactSupport.of_support_subset_isCompact (N.isCompact_coordinate_slab ha hb)
    (N.support_axialCutoff_subset hφ)


theorem contMDiff_axialCutoff {φ : ℝ → ℝ} {a b : ℝ}
    (ha : -N.epsilon⁻¹ < a) (hb : b < N.epsilon⁻¹)
    (hs : ContDiff ℝ ∞ φ) (hφ : support φ ⊆ Icc a b) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (N.axialCutoff φ) := by
  intro x
  by_cases hx : x ∈ N.carrier
  · have haxis := contMDiff_snd.contMDiffAt.comp x
      (N.coordinate_inverse_smooth.contMDiffAt (N.carrier_open.mem_nhds hx))
    apply (hs.contMDiff.contMDiffAt.comp x haxis).congr_of_eventuallyEq
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact N.axialCutoff_eq_of_mem φ hy
  · let K := N.coordinate_map '' (univ ×ˢ Icc a b)
    have hK : IsCompact K := N.isCompact_coordinate_slab ha hb
    have hxK : x ∉ K := by
      rintro ⟨z, hz, rfl⟩
      let zd : NeckDomain N.epsilon :=
        (z.1, ⟨z.2, ha.trans_le hz.2.1, hz.2.2.trans_lt hb⟩)
      apply hx
      have hm := (N.coordinate zd).property
      rw [N.coordinate_map_eq] at hm
      exact hm
    apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    by_contra hn
    exact hy (N.support_axialCutoff_subset hφ hn)

theorem axialCutoff_nonneg {φ : ℝ → ℝ} (hφ : ∀ s, 0 ≤ φ s) (x : M) :
    0 ≤ N.axialCutoff φ x := by
  by_cases hx : x ∈ N.carrier
  · rw [N.axialCutoff_eq_of_mem φ hx]
    exact hφ _
  · rw [N.axialCutoff_eq_zero_of_not_mem φ hx]


theorem gradient_axialCutoff (D : LeviCivitaData g) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {x : M} (hx : x ∈ N.carrier) :
    D.gradient (N.axialCutoff φ) x =
      deriv φ (N.coordinate_inverse x).2 •
        D.gradient (fun y => (N.coordinate_inverse y).2) x := by
  have he : N.axialCutoff φ =ᶠ[𝓝 x]
      φ ∘ (fun y => (N.coordinate_inverse y).2) := by
    filter_upwards [N.carrier_open.mem_nhds hx] with y hy
    exact N.axialCutoff_eq_of_mem φ hy
  have hg : D.gradient (N.axialCutoff φ) x =
      D.gradient (φ ∘ (fun y => (N.coordinate_inverse y).2)) x := by
    unfold LeviCivitaData.gradient mvfderiv
    rw [he.mfderiv_eq, he.eq_of_nhds]
  rw [hg]
  exact D.gradient_comp
    ((contMDiff_snd.contMDiffAt.comp x
      (N.coordinate_inverse_smooth.contMDiffAt
        (N.carrier_open.mem_nhds hx))).mdifferentiableAt (by simp))
    (hφ.differentiable (by simp) _)



theorem exists_axial_cutoff :
    ∃ ψ : M → ℝ, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ x, ψ x ∈ Icc 0 1) ∧
      (∀ x ∈ N.carrier, |(N.coordinate_inverse x).2| ≤ N.epsilon⁻¹ / 6 →
        ψ x = 1) ∧
      tsupport ψ ⊆ N.coordinate_map ''
        (univ ×ˢ Icc (-N.epsilon⁻¹ / 3) (N.epsilon⁻¹ / 3)) := by
  have hε : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  let φ : ContDiffBump (0 : ℝ) :=
    ⟨N.epsilon⁻¹ / 6, N.epsilon⁻¹ / 3, by positivity, by linarith⟩
  have hs : support (φ : ℝ → ℝ) ⊆ Icc (-N.epsilon⁻¹ / 3) (N.epsilon⁻¹ / 3) := by
    rw [φ.support_eq]
    intro s hs
    have hh : |s| < N.epsilon⁻¹ / 3 := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs
    exact ⟨by linarith [(abs_lt.mp hh).1], hh.le.trans' (le_abs_self _)⟩
  have ha : -N.epsilon⁻¹ < -N.epsilon⁻¹ / 3 := by linarith
  have hb : N.epsilon⁻¹ / 3 < N.epsilon⁻¹ := by linarith
  refine ⟨N.axialCutoff φ, N.contMDiff_axialCutoff ha hb φ.contDiff hs,
    N.hasCompactSupport_axialCutoff ha hb hs, ?_, ?_, ?_⟩
  · intro x
    refine ⟨N.axialCutoff_nonneg (fun _ => φ.nonneg) x, ?_⟩
    by_cases hx : x ∈ N.carrier
    · rw [N.axialCutoff_eq_of_mem φ hx]
      exact φ.le_one
    · rw [N.axialCutoff_eq_zero_of_not_mem φ hx]
      norm_num
  · intro x hx hsmall
    rw [N.axialCutoff_eq_of_mem φ hx]
    apply φ.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hsmall
  · exact closure_minimal (N.support_axialCutoff_subset hs)
      (N.isCompact_coordinate_slab ha hb).isClosed

end PoincareConjecture.EpsilonNeck
