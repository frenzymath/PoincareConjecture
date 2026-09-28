import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.CapTopology.NeckCollar
import PoincareConjecture.Proofs.M28.Mathlib.LastLevel

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem exists_signed_level_before_neck_exit (N : EpsilonNeck g)
    {γ : ℝ → M} {s c b : ℝ} (hsc : s < c)
    (hγ : ContinuousOn γ (Icc s c)) (hγs : γ s = N.center)
    (hinside : MapsTo γ (Ico s c) N.carrier) (hout : γ c ∉ N.carrier)
    (hbpos : 0 < b) (hb : b < N.epsilon⁻¹) :
    ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∃ v ∈ Ioo s c,
        sigma * (N.coordinate_inverse (γ v)).2 = b ∧
        ∀ t ∈ Ioo v c, b < sigma * (N.coordinate_inverse (γ t)).2 := by
  let K : Set M := N.coordinate_map '' (univ ×ˢ Icc (-b) b)
  have hK : IsCompact K := N.isCompact_coordinate_slab_intrinsic
    (by linarith) hb
  have hKsub : K ⊆ N.carrier := N.coordinate_slab_subset_carrier_m28 (by linarith) hb
  have hKout : γ c ∈ Kᶜ := fun h => hout (hKsub h)
  have hnhds : γ ⁻¹' Kᶜ ∈ 𝓝[Icc s c] c :=
    (hγ c (right_mem_Icc.mpr hsc.le)).preimage_mem_nhdsWithin
      (hK.isClosed.isOpen_compl.mem_nhds hKout)
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhdsWithin_iff.mp hnhds
  obtain ⟨u, hu, huc⟩ := exists_between
    (show max s (c - delta) < c from max_lt hsc (by linarith))
  have hsu : s < u := (le_max_left _ _).trans_lt hu
  have hdu : c - u < delta := by
    have h := (le_max_right s (c - delta)).trans_lt hu
    linarith
  have havoid (t : ℝ) (ht : t ∈ Ico u c) : γ t ∉ K := by
    apply hball
    refine ⟨?_, ⟨hsu.le.trans ht.1, ht.2.le⟩⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2.le)]
    linarith [ht.1]
  let axis : ℝ → ℝ := fun t => (N.coordinate_inverse (γ t)).2
  have haxis : ContinuousOn axis (Ico s c) :=
    continuous_snd.comp_continuousOn
      (N.coordinate_inverse_smooth.continuousOn.comp
        (hγ.mono Ico_subset_Icc_self) hinside)
  have habs (t : ℝ) (ht : t ∈ Ico u c) : b < |axis t| := by
    by_contra h
    have hle : |axis t| ≤ b := le_of_not_gt h
    apply havoid t ht
    refine ⟨N.coordinate_inverse (γ t), ⟨mem_univ _, ?_⟩,
      N.coordinate_map_coordinate_inverse (hinside ⟨hsu.le.trans ht.1, ht.2⟩)⟩
    exact abs_le.mp hle
  have hne (t : ℝ) (ht : t ∈ Ico u c) : axis t ≠ 0 := by
    have h := habs t ht
    intro heq
    rw [heq, abs_zero] at h
    exact (not_lt_of_ge hbpos.le) h
  have hsign : ∃ sigma : ℝ, (sigma = 1 ∨ sigma = -1) ∧
      ∀ t ∈ Ico u c, b < sigma * axis t := by
    rcases isPreconnected_Ico.mapsTo_Ioi_or_Iio
      (haxis.mono (Ico_subset_Ico_left hsu.le)) hne with hpos | hneg
    · refine ⟨1, Or.inl rfl, ?_⟩
      intro t ht
      simpa only [one_mul, abs_of_pos (show 0 < axis t from hpos ht)] using habs t ht
    · refine ⟨-1, Or.inr rfl, ?_⟩
      intro t ht
      simpa only [neg_one_mul, abs_of_neg (show axis t < 0 from hneg ht)] using habs t ht
  obtain ⟨sigma, hsigma, hlate⟩ := hsign
  have hzero : axis s = 0 := by
    dsimp only [axis]
    rw [hγs]
    exact (N.mem_central_sphere_iff_of_mem_carrier
      (N.central_sphere_subset N.center_on_central_sphere)).mp N.center_on_central_sphere
  have htest : ContinuousOn (fun t => sigma * axis t) (Icc s u) :=
    continuousOn_const.mul (haxis.mono
      (fun t ht => ⟨ht.1, ht.2.trans_lt huc⟩))
  obtain ⟨v, hv, hlevel, habove⟩ := exists_last_eq_of_continuousOn hsu.le htest
    (show sigma * axis s ≤ b by simpa only [hzero, mul_zero] using hbpos.le)
    (hlate u ⟨le_rfl, huc⟩)
  have hsv : s < v := lt_of_le_of_ne hv.1 (by
    intro heq
    subst v
    have hbzero : b = 0 := hlevel.symm.trans (by rw [hzero, mul_zero])
    exact hbpos.ne' hbzero)
  refine ⟨sigma, hsigma, v, ⟨hsv, hv.2.trans_lt huc⟩, hlevel, ?_⟩
  intro t ht
  by_cases htu : t ≤ u
  · exact habove t ⟨ht.1, htu⟩
  · exact hlate t ⟨(lt_of_not_ge htu).le, ht.2⟩

end PoincareConjecture.M28
