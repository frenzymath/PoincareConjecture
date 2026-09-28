import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_MetricHalfplaneFan













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem defining_ray_derivative
    {phi : AnnulusCoordinates → ℝ} {ell : AnnulusCoordinates →L[ℝ] ℝ}
    {q : AnnulusCoordinates} (hphi : HasFDerivAt phi ell q) (w : AnnulusCoordinates) :
    HasDerivAt (fun r : ℝ => phi (q + r • w)) (ell w) 0 := by
  have hray : HasDerivAt (fun r : ℝ => q + r • w) w 0 := by
    convert! (hasDerivAt_const (0 : ℝ) q).add
      ((hasDerivAt_id (0 : ℝ)).smul_const w) using 1
    simp
  have hd : HasFDerivAt phi ell (q + (0 : ℝ) • w) := by simpa using hphi
  exact hd.comp_hasDerivAt 0 hray

private theorem linear_pos_on_open_nonnegative
    (ell : AnnulusCoordinates →L[ℝ] ℝ) (hell : ell ≠ 0)
    {S : Set AnnulusCoordinates} (hS : IsOpen S)
    (hnonneg : ∀ w ∈ S, 0 ≤ ell w) {w : AnnulusCoordinates} (hw : w ∈ S) :
    0 < ell w := by
  have hv : ∃ v, ell v ≠ 0 := by
    by_contra h
    push Not at h
    exact hell (ContinuousLinearMap.ext h)
  obtain ⟨v, hv⟩ := hv
  have hsurj : Function.Surjective ell := by
    intro r
    refine ⟨(r / ell v) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  have himage : ell '' S ⊆ Ici (0 : ℝ) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hnonneg z hz
  have hopen : IsOpen (ell '' S) := ell.isOpenMap hsurj S hS
  have hmem := interior_mono himage
    (hopen.interior_eq.symm ▸ mem_image_of_mem ell hw)
  simpa only [interior_Ici, mem_Ioi] using hmem






theorem m64Intrinsic_regional_tangent_sector_unique_of_ray
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hfront : ∀ i j, i ≠ j →
      (F i '' convexHull ℝ (range (b i))) ∩ (F j '' convexHull ℝ (range (b j))) ⊆
        frontier (F i '' convexHull ℝ (range (b i)))) {q w : AnnulusCoordinates}
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      q + r • w ∈ ⋃ i, F i '' convexHull ℝ (range (b i)))
    (htransverse : ∀ i, q ∈ F i '' convexHull ℝ (range (b i)) →
      ∀ k, (b i).coord k ((F i).symm q) = 0 →
        fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w ≠ 0) :
    ∃! i, q ∈ F i '' convexHull ℝ (range (b i)) ∧
      ∀ k, (b i).coord k ((F i).symm q) = 0 →
        0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w := by
  classical
  have hex : ∃ i, q ∈ F i '' convexHull ℝ (range (b i)) ∧
      ∀ k, (b i).coord k ((F i).symm q) = 0 →
        0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w := by
    by_contra hnone
    have havoid (i : I) :
        ∀ᶠ r in 𝓝[>] (0 : ℝ), q + r • w ∉ F i '' convexHull ℝ (range (b i)) := by
      by_cases hqi : q ∈ F i '' convexHull ℝ (range (b i))
      · have hnot : ¬ ∀ k, (b i).coord k ((F i).symm q) = 0 →
            0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w :=
          fun h => hnone ⟨i, hqi, h⟩
        push Not at hnot
        obtain ⟨k, hzero, hle⟩ := hnot
        have hqt : q ∈ (F i).target := by
          obtain ⟨z, hz, rfl⟩ := hqi
          exact (F i).map_source (hsource i hz)
        exact m64Intrinsic_coordinate_triangle_ray_exits (F i) (b i) (hFi i) (hsource i)
          hqt k hzero (lt_of_le_of_ne hle (htransverse i hqi k hzero))
      · have hclosed : IsClosed (F i '' convexHull ℝ (range (b i))) :=
          (((finite_range (b i)).isCompact_convexHull ℝ).image_of_continuousOn
            ((F i).continuousOn.mono (hsource i))).isClosed
        have hpath : ContinuousAt (fun r : ℝ => q + r • w) 0 := by fun_prop
        have hnot : ∀ᶠ r in 𝓝 (0 : ℝ),
            q + r • w ∉ F i '' convexHull ℝ (range (b i)) := by
          change (fun r : ℝ => q + r • w) ⁻¹'
            (F i '' convexHull ℝ (range (b i)))ᶜ ∈ 𝓝 (0 : ℝ)
          exact hpath.preimage_mem_nhds (by
            simpa only [zero_smul, add_zero] using hclosed.isOpen_compl.mem_nhds hqi)
        exact hnot.filter_mono nhdsWithin_le_nhds
    obtain ⟨r, hr, hnot⟩ := (hray.and (eventually_all.mpr havoid)).exists
    obtain ⟨i, hi⟩ := mem_iUnion.mp hr
    exact hnot i hi
  obtain ⟨i, hi, hpos⟩ := hex
  refine ⟨i, ⟨hi, hpos⟩, ?_⟩
  intro j hj
  by_contra hji
  exact m64Intrinsic_coordinate_triangle_tangent_sectors_disjoint
    (F i) (F j) (b i) (b j) (hFi i) (hFi j) (hsource i) (hsource j)
    (hfront i j (Ne.symm hji)) hi hj.1 hpos hj.2






theorem m64Intrinsic_boundary_tangent_partition_ae
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hfront : ∀ i j, i ≠ j →
      (F i '' convexHull ℝ (range (b i))) ∩ (F j '' convexHull ℝ (range (b j))) ⊆
        frontier (F i '' convexHull ℝ (range (b i))))
    {q : AnnulusCoordinates} {phi : AnnulusCoordinates → ℝ}
    {ell : AnnulusCoordinates →L[ℝ] ℝ} (hphi : HasFDerivAt phi ell q)
    (hzero : phi q = 0)
    (hregion : ∀ᶠ z in 𝓝 q,
      z ∈ ⋃ i, F i '' convexHull ℝ (range (b i)) ↔ 0 ≤ phi z) :
    ∀ᵐ w : AnnulusCoordinates, 0 < ell w → ∃! i,
      q ∈ F i '' convexHull ℝ (range (b i)) ∧
        ∀ k, (b i).coord k ((F i).symm q) = 0 →
          0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w := by
  have htransverse (i : I) : ∀ᵐ w : AnnulusCoordinates,
      q ∈ F i '' convexHull ℝ (range (b i)) →
        ∀ k, (b i).coord k ((F i).symm q) = 0 →
          fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w ≠ 0 := by
    by_cases hqi : q ∈ F i '' convexHull ℝ (range (b i))
    · have hqt : q ∈ (F i).target := by
        obtain ⟨z, hz, rfl⟩ := hqi
        exact (F i).map_source (hsource i hz)
      have hk (k : Fin 3) : ∀ᵐ w : AnnulusCoordinates,
          fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w ≠ 0 := by
        rw [ae_iff]
        simpa only [not_not] using
          m64Intrinsic_inverse_coordinate_kernel_null (F i) (b i) (hF i) (hFi i) hqt k
      filter_upwards [ae_all_iff.mpr hk] with w hw
      exact fun _ k _ => hw k
    · exact Eventually.of_forall (fun _ h => (hqi h).elim)
  filter_upwards [ae_all_iff.mpr htransverse] with w hw
  intro hwpos
  have hd := defining_ray_derivative hphi w
  have hs := hd.tendsto_slope_zero_right.eventually_const_lt hwpos
  have hpath : Tendsto (fun r : ℝ => q + r • w) (𝓝[>] 0) (𝓝 q) := by
    have hc : ContinuousAt (fun r : ℝ => q + r • w) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hray : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      q + r • w ∈ ⋃ i, F i '' convexHull ℝ (range (b i)) := by
    filter_upwards [hs, hpath.eventually hregion, self_mem_nhdsWithin] with r hr hreg hrpos
    apply hreg.mpr
    have hrpos' : 0 < r := hrpos
    simp only [zero_add, zero_smul, add_zero, hzero, sub_zero, smul_eq_mul] at hr
    exact ((mul_pos_iff_of_pos_left (inv_pos.mpr hrpos')).mp hr).le
  exact m64Intrinsic_regional_tangent_sector_unique_of_ray F b hFi hsource hfront hray hw







theorem m64Intrinsic_boundary_tangent_sector_inward
    {I : Type*}
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    {q : AnnulusCoordinates} {phi : AnnulusCoordinates → ℝ}
    {ell : AnnulusCoordinates →L[ℝ] ℝ} (hphi : HasFDerivAt phi ell q)
    (hzero : phi q = 0) (hell : ell ≠ 0)
    (hregion : ∀ᶠ z in 𝓝 q,
      z ∈ ⋃ i, F i '' convexHull ℝ (range (b i)) ↔ 0 ≤ phi z)
    (i : I) (hqi : q ∈ F i '' convexHull ℝ (range (b i)))
    (w : AnnulusCoordinates)
    (hw : ∀ k, (b i).coord k ((F i).symm q) = 0 →
      0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w) : 0 < ell w := by
  let C : Set AnnulusCoordinates := {v | ∀ k, (b i).coord k ((F i).symm q) = 0 →
    0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q v}
  have hopen : IsOpen C := by
    have hk (k : Fin 3) : IsOpen {v : AnnulusCoordinates |
        (b i).coord k ((F i).symm q) = 0 →
          0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q v} := by
      by_cases h : (b i).coord k ((F i).symm q) = 0
      · simp only [h, true_implies]
        exact isOpen_lt continuous_const (ContinuousLinearMap.continuous _)
      · simpa only [h, false_implies, ofPred_true] using isOpen_univ
    simpa only [C, ofPred_forall] using isOpen_iInter_of_finite hk
  apply linear_pos_on_open_nonnegative ell hell hopen ?_ hw
  intro v hv
  have hd := defining_ray_derivative hphi v
  have henter := m64Intrinsic_coordinate_triangle_ray_enters (F i) (b i)
    (hFi i) (hsource i) hqi hv
  have hpath : Tendsto (fun r : ℝ => q + r • v) (𝓝[>] 0) (𝓝 q) := by
    have hc : ContinuousAt (fun r : ℝ => q + r • v) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [henter, hpath.eventually hregion, self_mem_nhdsWithin] with r hr hreg hrpos
  have hnonneg := hreg.mp (mem_iUnion.mpr ⟨i, interior_subset hr⟩)
  have hrpos' : 0 < r := hrpos
  simp only [zero_add, zero_smul, add_zero, hzero, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr hrpos'.le) hnonneg

end PoincareConjecture
