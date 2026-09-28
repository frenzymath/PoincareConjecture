import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.Overlap.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Overlap.AxialOrientation


set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem transition_axis_monotonicity_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (hP : P.epsilon ≤ 1 / 200)
    (q : UnitTwoSphere) (S : Set ℝ) (hS : IsPreconnected S)
    (hdom : S ⊆ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹)
    (hcarrier : ∀ s ∈ S, P.coordinate_map (q, s) ∈ N.carrier) :
    let f := fun t : ℝ => (N.coordinate_inverse (P.coordinate_map (q, t))).2
    (StrictMonoOn f S ∨ StrictAntiOn f S) ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≤ b →
        (1 / 4 : ℝ) * (b - a) ≤ |f b - f a| ∧
          |f b - f a| ≤ (3 / 2 : ℝ) * (b - a) := by
  let f := fun t : ℝ => (N.coordinate_inverse (P.coordinate_map (q, t))).2
  have hsmooth (s : ℝ) (hs : s ∈ S) : ContDiffAt ℝ ∞ f s :=
    N.transition_axis_contDiffAt P q (hdom hs) (hcarrier s hs)
  have hcont : ContinuousOn f S :=
    fun s hs => (hsmooth s hs).continuousAt.continuousWithinAt
  have hcont' : ContinuousOn (deriv f) S := by
    intro s hs
    exact ((hsmooth s hs).derivWithin (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hderiv (s : ℝ) (hs : s ∈ S) :
      (1 / 4 : ℝ) ≤ |deriv f s| ∧ |deriv f s| ≤ (3 / 2 : ℝ) :=
    N.transition_axis_deriv_bounds_of_epsilon_le P hN hP q (hdom hs) (hcarrier s hs)
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

theorem transition_band_orientation_of_epsilon_le
    (N P : EpsilonNeck g) (hN : N.epsilon ≤ 1 / 200) (hP : P.epsilon ≤ 1 / 200)
    (S : Set ℝ) (hS : IsPreconnected S)
    (hdom : S ⊆ Ioo (-P.epsilon⁻¹) P.epsilon⁻¹)
    (hcarrier : ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ S → P.coordinate_map (q, s) ∈ N.carrier)
    (hnontrivial : ∃ a ∈ S, ∃ b ∈ S, a < b) :
    let f := fun (q : UnitTwoSphere) (t : ℝ) =>
      (N.coordinate_inverse (P.coordinate_map (q, t))).2
    (∀ q, StrictMonoOn (f q) S) ∨ (∀ q, StrictAntiOn (f q) S) := by
  obtain ⟨a, ha, b, hb, hab⟩ := hnontrivial
  let f := fun (q : UnitTwoSphere) (t : ℝ) =>
    (N.coordinate_inverse (P.coordinate_map (q, t))).2
  have hline (q : UnitTwoSphere) : StrictMonoOn (f q) S ∨ StrictAntiOn (f q) S :=
    (N.transition_axis_monotonicity_of_epsilon_le P hN hP q S hS hdom (hcarrier q)).1
  have hcont (s : ℝ) (hs : s ∈ S) : Continuous (fun q : UnitTwoSphere => f q s) := by
    have hmap : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : UnitTwoSphere => N.coordinate_inverse (P.coordinate_map (q, s))) := by
      intro q
      exact (N.coordinate_inverse_smooth.contMDiffAt
        (N.carrier_open.mem_nhds (hcarrier q s hs))).comp q
          (P.coordinateSlice_contMDiff (hdom hs) q)
    exact hmap.continuous.snd
  have hne (q : UnitTwoSphere) (_ : q ∈ (univ : Set UnitTwoSphere)) :
      f q b - f q a ≠ 0 := by
    rcases hline q with h | h
    · exact (sub_pos.mpr (h ha hb hab)).ne'
    · exact (sub_neg.mpr (h ha hb hab)).ne
  rcases isPreconnected_univ.mapsTo_Ioi_or_Iio
      ((hcont b hb).sub (hcont a ha)).continuousOn hne with hpos | hneg
  · left
    intro q
    rcases hline q with h | h
    · exact h
    · have hp : 0 < f q b - f q a := hpos (mem_univ q)
      have hn := h ha hb hab
      linarith
  · right
    intro q
    rcases hline q with h | h
    · have hn : f q b - f q a < 0 := hneg (mem_univ q)
      have hp := h ha hb hab
      linarith
    · exact h

end PoincareConjecture.EpsilonNeck
