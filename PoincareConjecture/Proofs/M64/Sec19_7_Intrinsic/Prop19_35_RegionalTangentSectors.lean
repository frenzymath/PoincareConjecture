import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionParentFans
import Mathlib.Analysis.Calculus.Deriv.Slope













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem positive_after_simple_zero
    {f : ℝ → ℝ} {v : ℝ} (hf : HasDerivAt f v 0) (hzero : f 0 = 0) (hv : 0 < v) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < f r := by
  have hs := hf.tendsto_slope_zero_right.eventually_const_lt hv
  filter_upwards [hs, self_mem_nhdsWithin] with r hr hrpos
  have hrpos' : 0 < r := hrpos
  simp only [zero_add, hzero, sub_zero, smul_eq_mul] at hr
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hrpos')).mp hr

private theorem inverse_coord_differentiable
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {q : AnnulusCoordinates} (hq : q ∈ F.target) (k : Fin 3) :
    DifferentiableAt ℝ (fun x => b.coord k (F.symm x)) q := by
  let c : AnnulusCoordinates →ᴬ[ℝ] ℝ :=
    { toAffineMap := b.coord k, cont := (b.coord k).continuous_of_finiteDimensional }
  have hdi : DifferentiableAt ℝ F.symm q :=
    (((contMDiffOn_iff_contDiffOn.mp hFi) q hq).contDiffAt
      (F.open_target.mem_nhds hq)).differentiableAt (by simp)
  exact ((c.contDiff : ContDiff ℝ ∞ c).differentiable (by simp)).differentiableAt.comp q hdi

private theorem inverse_coord_ray_derivative
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {q : AnnulusCoordinates} (hq : q ∈ F.target) (w : AnnulusCoordinates) (k : Fin 3) :
    HasDerivAt (fun r : ℝ => b.coord k (F.symm (q + r • w)))
      (fderiv ℝ (fun x => b.coord k (F.symm x)) q w) 0 := by
  have hray : HasDerivAt (fun r : ℝ => q + r • w) w 0 := by
    convert! (hasDerivAt_const (0 : ℝ) q).add
      ((hasDerivAt_id (0 : ℝ)).smul_const w) using 1
    simp
  have hd := (inverse_coord_differentiable F b hFi hq k).hasFDerivAt
  have hd' : HasFDerivAt (fun x => b.coord k (F.symm x))
      (fderiv ℝ (fun x => b.coord k (F.symm x)) q) (q + (0 : ℝ) • w) := by
    simpa only [zero_smul, add_zero] using hd
  convert! hd'.comp_hasDerivAt 0 hray using 1







theorem m64Intrinsic_coordinate_triangle_ray_enters
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) {q w : AnnulusCoordinates}
    (hq : q ∈ F '' convexHull ℝ (range b))
    (hpositive : ∀ k, b.coord k (F.symm q) = 0 →
      0 < fderiv ℝ (fun x => b.coord k (F.symm x)) q w) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), q + r • w ∈ interior (F '' convexHull ℝ (range b)) := by
  have hqt : q ∈ F.target := by
    obtain ⟨z, hz, rfl⟩ := hq
    exact F.map_source (hsource hz)
  have hqinv : F.symm q ∈ convexHull ℝ (range b) := by
    obtain ⟨z, hz, rfl⟩ := hq
    rwa [F.left_inv (hsource hz)]
  have hnonneg (k : Fin 3) : 0 ≤ b.coord k (F.symm q) := by
    have h : ∀ j, 0 ≤ b.coord j (F.symm q) := by
      simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using hqinv
    exact h k
  have hcoords (k : Fin 3) :
      ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < b.coord k (F.symm (q + r • w)) := by
    have hd := inverse_coord_ray_derivative F b hFi hqt w k
    by_cases hzero : b.coord k (F.symm q) = 0
    · exact positive_after_simple_zero hd
        (by simpa only [zero_smul, add_zero] using hzero) (hpositive k hzero)
    · have hbase : 0 < b.coord k (F.symm (q + (0 : ℝ) • w)) := by
        simpa only [zero_smul, add_zero] using lt_of_le_of_ne (hnonneg k) (Ne.symm hzero)
      exact (hd.continuousAt.tendsto.eventually_const_lt hbase).filter_mono nhdsWithin_le_nhds
  have hray : ContinuousAt (fun r : ℝ => q + r • w) 0 := by fun_prop
  have htarget : ∀ᶠ r in 𝓝 (0 : ℝ), q + r • w ∈ F.target :=
    hray.preimage_mem_nhds (by
      simpa only [zero_smul, add_zero] using (F.open_target.mem_nhds hqt))
  filter_upwards [eventually_all.mpr hcoords, htarget.filter_mono nhdsWithin_le_nhds]
    with r hr hrt
  rw [interior_smooth_coordinate_image F hsource]
  refine ⟨F.symm (q + r • w), ?_, F.right_inv hrt⟩
  rw [b.interior_convexHull]
  exact hr






theorem m64Intrinsic_coordinate_triangle_ray_exits
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hsource : convexHull ℝ (range b) ⊆ F.source) {q w : AnnulusCoordinates}
    (hq : q ∈ F.target) (k : Fin 3) (hzero : b.coord k (F.symm q) = 0)
    (hnegative : fderiv ℝ (fun x => b.coord k (F.symm x)) q w < 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), q + r • w ∉ F '' convexHull ℝ (range b) := by
  have hd := inverse_coord_ray_derivative F b hFi hq w k
  have hneg := positive_after_simple_zero hd.neg
    (by
      change -(b.coord k (F.symm (q + (0 : ℝ) • w))) = 0
      simp only [zero_smul, add_zero, hzero, neg_zero]) (neg_pos.mpr hnegative)
  filter_upwards [hneg] with r hr
  change 0 < -(b.coord k (F.symm (q + r • w))) at hr
  rintro ⟨z, hz, hzq⟩
  have hnonneg : 0 ≤ b.coord k z := by
    have h : ∀ j, 0 ≤ b.coord j z := by
      simpa only [b.convexHull_eq_nonneg_coord, mem_ofPred_eq] using hz
    exact h k
  rw [← hzq, F.left_inv (hsource hz)] at hr
  linarith






theorem m64Intrinsic_coordinate_triangle_tangent_sectors_disjoint
    (F G : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b c : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (hGi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ G.symm G.target)
    (hFsource : convexHull ℝ (range b) ⊆ F.source)
    (hGsource : convexHull ℝ (range c) ⊆ G.source)
    (hfront : (F '' convexHull ℝ (range b)) ∩ (G '' convexHull ℝ (range c)) ⊆
      frontier (F '' convexHull ℝ (range b))) {q w : AnnulusCoordinates}
    (hqF : q ∈ F '' convexHull ℝ (range b))
    (hqG : q ∈ G '' convexHull ℝ (range c))
    (hFpositive : ∀ k, b.coord k (F.symm q) = 0 →
      0 < fderiv ℝ (fun x => b.coord k (F.symm x)) q w) :
    ¬ (∀ k, c.coord k (G.symm q) = 0 →
      0 < fderiv ℝ (fun x => c.coord k (G.symm x)) q w) := by
  intro hGpositive
  have hF := m64Intrinsic_coordinate_triangle_ray_enters F b hFi hFsource hqF hFpositive
  have hG := m64Intrinsic_coordinate_triangle_ray_enters G c hGi hGsource hqG hGpositive
  obtain ⟨r, hrF, hrG⟩ := (hF.and hG).exists
  exact (hfront ⟨interior_subset hrF, interior_subset hrG⟩).2 hrF







theorem m64Intrinsic_regional_tangent_sector_unique
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hfront : ∀ i j, i ≠ j →
      (F i '' convexHull ℝ (range (b i))) ∩ (F j '' convexHull ℝ (range (b j))) ⊆
        frontier (F i '' convexHull ℝ (range (b i)))) {q w : AnnulusCoordinates}
    (hq : q ∈ interior (⋃ i, F i '' convexHull ℝ (range (b i))))
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
        have hevent : ∀ᶠ r in 𝓝 (0 : ℝ),
            q + r • w ∉ F i '' convexHull ℝ (range (b i)) := by
          change (fun r : ℝ => q + r • w) ⁻¹'
            (F i '' convexHull ℝ (range (b i)))ᶜ ∈ 𝓝 (0 : ℝ)
          exact hpath.preimage_mem_nhds (by
            simpa only [zero_smul, add_zero] using (hclosed.isOpen_compl.mem_nhds hqi))
        exact hevent.filter_mono nhdsWithin_le_nhds
    have hpath : ContinuousAt (fun r : ℝ => q + r • w) 0 := by fun_prop
    have hregion : ∀ᶠ r in 𝓝 (0 : ℝ),
        q + r • w ∈ ⋃ i, F i '' convexHull ℝ (range (b i)) :=
      hpath.preimage_mem_nhds (by
        simpa only [zero_smul, add_zero] using (mem_interior_iff_mem_nhds.mp hq))
    obtain ⟨r, hr, hnot⟩ := ((hregion.filter_mono nhdsWithin_le_nhds).and
      (eventually_all.mpr havoid)).exists
    obtain ⟨i, hi⟩ := mem_iUnion.mp hr
    exact hnot i hi
  obtain ⟨i, hi, hpositive⟩ := hex
  refine ⟨i, ⟨hi, hpositive⟩, ?_⟩
  intro j hj
  by_contra hji
  exact m64Intrinsic_coordinate_triangle_tangent_sectors_disjoint
    (F i) (F j) (b i) (b j) (hFi i) (hFi j) (hsource i) (hsource j)
    (hfront i j (Ne.symm hji)) hi hj.1 hpositive hj.2

end PoincareConjecture
