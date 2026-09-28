import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LocalAxialTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem transition_axis_contDiffAt_m28 (N N' : EpsilonNeck g) (q : UnitTwoSphere)
    {s : ℝ} (hs : s ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hx : N'.coordinate_map (q, s) ∈ N.carrier) :
    ContDiffAt ℝ ∞ (fun t : ℝ => (N.coordinate_inverse (N'.coordinate_map (q, t))).2) s := by
  have hmap := (N'.coordinate_map_smooth.contMDiffAt
    (N'.cylinderDomain_open.mem_nhds
      (show (q, s) ∈ N'.cylinderDomain from ⟨mem_univ _, hs⟩))).comp s
    (contMDiffAt_const.prodMk contMDiffAt_id)
  have hinv := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).comp s hmap
  exact (contMDiffAt_snd.comp s hinv).contDiffAt

theorem exists_transition_axis_monotonicity_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M},
        ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon ≤ ε₀ →
        ∀ (q : UnitTwoSphere) (S : Set ℝ), IsPreconnected S →
        S ⊆ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹ →
        (∀ s ∈ S, N'.coordinate_map (q, s) ∈ N.carrier) →
          let f := fun t : ℝ => (N.coordinate_inverse (N'.coordinate_map (q, t))).2
          (StrictMonoOn f S ∨ StrictAntiOn f S) ∧
          ∀ a ∈ S, ∀ b ∈ S, a ≤ b →
            (0.9 : ℝ) * (b - a) ≤ |f b - f a| ∧
              |f b - f a| ≤ (1.1 : ℝ) * (b - a) := by
  obtain ⟨ε₀, hε₀, hsmall, hbounds⟩ := exists_transition_axis_deriv_bounds_m28.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hN' q S hS hdom hcarrier
  let f := fun t : ℝ => (N.coordinate_inverse (N'.coordinate_map (q, t))).2
  have hsmooth (s : ℝ) (hs : s ∈ S) : ContDiffAt ℝ ∞ f s :=
    N.transition_axis_contDiffAt_m28 N' q (hdom hs) (hcarrier s hs)
  have hcont : ContinuousOn f S :=
    fun s hs => (hsmooth s hs).continuousAt.continuousWithinAt
  have hcont' : ContinuousOn (deriv f) S := by
    intro s hs
    exact ((hsmooth s hs).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hderiv (s : ℝ) (hs : s ∈ S) :
      (0.9 : ℝ) ≤ |deriv f s| ∧ |deriv f s| ≤ (1.1 : ℝ) :=
    hbounds N N' hN hN' q (hdom hs) (hcarrier s hs)
  have hne (s : ℝ) (hs : s ∈ S) : deriv f s ≠ 0 := by
    intro heq
    have h := (hderiv s hs).1
    rw [heq, abs_zero] at h
    norm_num at h
  refine ⟨?_, ?_⟩
  · rcases hS.mapsTo_Ioi_or_Iio hcont' hne with hpos | hneg
    · exact Or.inl (strictMonoOn_of_deriv_pos hS.ordConnected.convex hcont
        (fun s hs => hpos (interior_subset hs)))
    · exact Or.inr (strictAntiOn_of_deriv_neg hS.ordConnected.convex hcont
        (fun s hs => hneg (interior_subset hs)))
  · intro a ha b hb hab
    rcases hab.eq_or_lt with rfl | hab
    · simp
    have hI : Icc a b ⊆ S := hS.ordConnected.out ha hb
    obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope f hab (hcont.mono hI)
      (fun s hs => ((hsmooth s (hI (Ioo_subset_Icc_self hs))).differentiableAt
        (by simp)).differentiableWithinAt)
    have hd := hderiv c (hI (Ioo_subset_Icc_self hc))
    have hdiff : 0 < b - a := sub_pos.mpr hab
    have hmul : |f b - f a| = |deriv f c| * (b - a) := by
      rw [heq, abs_div, abs_of_pos hdiff]
      exact (div_mul_cancel₀ _ hdiff.ne').symm
    rw [hmul]
    exact ⟨mul_le_mul_of_nonneg_right hd.1 hdiff.le,
      mul_le_mul_of_nonneg_right hd.2 hdiff.le⟩

end PoincareConjecture.EpsilonNeck
