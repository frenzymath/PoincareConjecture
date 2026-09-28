import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryTangentSectors
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SectorFan













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture

private theorem corner_ray_sign
    {phi : AnnulusCoordinates → ℝ} {ell : AnnulusCoordinates →L[ℝ] ℝ}
    {q w : AnnulusCoordinates} (hphi : HasFDerivAt phi ell q)
    (hzero : phi q = 0) (hw : ell w ≠ 0) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (0 ≤ phi (q + r • w) ↔ 0 < ell w) ∧
      (phi (q + r • w) ≤ 0 ↔ ell w < 0) := by
  have hray : HasDerivAt (fun r : ℝ => q + r • w) w 0 := by
    convert! (hasDerivAt_const (0 : ℝ) q).add
      ((hasDerivAt_id (0 : ℝ)).smul_const w) using 1
    simp
  have hd : HasDerivAt (fun r : ℝ => phi (q + r • w)) (ell w) 0 := by
    have hp : HasFDerivAt phi ell (q + (0 : ℝ) • w) := by simpa using hphi
    exact hp.comp_hasDerivAt 0 hray
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · filter_upwards [hd.tendsto_slope_zero_right.eventually_lt_const hneg,
      self_mem_nhdsWithin] with r hr hrpos
    have hrpos' : 0 < r := hrpos
    simp only [zero_add, zero_smul, add_zero, hzero, sub_zero, smul_eq_mul] at hr
    have hp : phi (q + r • w) < 0 := by
      have hinv := inv_pos.mpr hrpos'
      nlinarith
    exact ⟨iff_of_false (not_le_of_gt hp) (not_lt_of_ge hneg.le),
      iff_of_true hp.le hneg⟩
  · filter_upwards [hd.tendsto_slope_zero_right.eventually_const_lt hpos,
      self_mem_nhdsWithin] with r hr hrpos
    have hrpos' : 0 < r := hrpos
    simp only [zero_add, zero_smul, add_zero, hzero, sub_zero, smul_eq_mul] at hr
    have hp : 0 < phi (q + r • w) :=
      (mul_pos_iff_of_pos_left (inv_pos.mpr hrpos')).mp hr
    exact ⟨iff_of_true hp.le hpos,
      iff_of_false (not_le_of_gt hp) (not_lt_of_ge hpos.le)⟩






theorem m64Intrinsic_corner_tangent_partition_ae
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hfront : ∀ i j, i ≠ j →
      (F i '' convexHull ℝ (range (b i))) ∩ (F j '' convexHull ℝ (range (b j))) ⊆
        frontier (F i '' convexHull ℝ (range (b i))))
    {q : AnnulusCoordinates} {phi : AnnulusCoordinates → ℝ × ℝ}
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (hphi : HasFDerivAt phi L.toContinuousLinearMap q) (hzero : phi q = 0)
    (positive : Bool)
    (hregion : ∀ᶠ z in 𝓝 q,
      z ∈ ⋃ i, F i '' convexHull ℝ (range (b i)) ↔
        if positive then 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2
        else (phi z).1 ≤ 0 ∨ (phi z).2 ≤ 0) :
    ∀ᵐ w : AnnulusCoordinates,
      ((if positive then 0 < (L w).1 ∧ 0 < (L w).2
        else ¬ (0 < (L w).1 ∧ 0 < (L w).2)) →
        ∃! i, q ∈ F i '' convexHull ℝ (range (b i)) ∧
          ∀ k, (b i).coord k ((F i).symm q) = 0 →
            0 < fderiv ℝ (fun z => (b i).coord k ((F i).symm z)) q w) ∧
      (∀ i, q ∈ F i '' convexHull ℝ (range (b i)) →
        (∀ k, (b i).coord k ((F i).symm q) = 0 →
          0 < fderiv ℝ (fun z => (b i).coord k ((F i).symm z)) q w) →
        if positive then 0 < (L w).1 ∧ 0 < (L w).2
        else ¬ (0 < (L w).1 ∧ 0 < (L w).2)) := by
  let ell0 := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp L.toContinuousLinearMap
  let ell1 := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp L.toContinuousLinearMap
  have hell0 : ell0 ≠ 0 := by
    intro h
    have hh := congrArg (fun f : AnnulusCoordinates →L[ℝ] ℝ => f (L.symm (1, 0))) h
    simp [ell0] at hh
  have hell1 : ell1 ≠ 0 := by
    intro h
    have hh := congrArg (fun f : AnnulusCoordinates →L[ℝ] ℝ => f (L.symm (0, 1))) h
    simp [ell1] at hh
  have hline0 : ∀ᵐ w : AnnulusCoordinates, ell0 w ≠ 0 := by
    simpa only [ae_iff, not_not] using m64Intrinsic_linear_kernel_null ell0 hell0
  have hline1 : ∀ᵐ w : AnnulusCoordinates, ell1 w ≠ 0 := by
    simpa only [ae_iff, not_not] using m64Intrinsic_linear_kernel_null ell1 hell1
  have htransverse (i : I) : ∀ᵐ w : AnnulusCoordinates,
      q ∈ F i '' convexHull ℝ (range (b i)) →
        ∀ k, (b i).coord k ((F i).symm q) = 0 →
          fderiv ℝ (fun z => (b i).coord k ((F i).symm z)) q w ≠ 0 := by
    by_cases hqi : q ∈ F i '' convexHull ℝ (range (b i))
    · have hqt : q ∈ (F i).target := by
        obtain ⟨z, hz, rfl⟩ := hqi
        exact (F i).map_source (hsource i hz)
      have hk (k : Fin 3) : ∀ᵐ w : AnnulusCoordinates,
          fderiv ℝ (fun z => (b i).coord k ((F i).symm z)) q w ≠ 0 := by
        rw [ae_iff]
        simpa only [not_not] using
          m64Intrinsic_inverse_coordinate_kernel_null (F i) (b i) (hF i) (hFi i) hqt k
      filter_upwards [ae_all_iff.mpr hk] with w hw
      exact fun _ k _ => hw k
    · exact Eventually.of_forall (fun _ h => (hqi h).elim)
  filter_upwards [hline0, hline1, ae_all_iff.mpr htransverse] with w hw0 hw1 hw
  have hsign0 := corner_ray_sign hphi.fst (congrArg Prod.fst hzero) hw0
  have hsign1 := corner_ray_sign hphi.snd (congrArg Prod.snd hzero) hw1
  have hpath : Tendsto (fun r : ℝ => q + r • w) (𝓝[>] 0) (𝓝 q) := by
    have hc : ContinuousAt (fun r : ℝ => q + r • w) 0 := by fun_prop
    simpa only [zero_smul, add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsign : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (q + r • w ∈ ⋃ i, F i '' convexHull ℝ (range (b i))) ↔
        if positive then 0 < (L w).1 ∧ 0 < (L w).2
        else ¬ (0 < (L w).1 ∧ 0 < (L w).2) := by
    filter_upwards [hpath.eventually hregion, hsign0, hsign1] with r hr hs0 hs1
    rw [hr]
    change ell0 w ≠ 0 at hw0
    change ell1 w ≠ 0 at hw1
    cases positive
    · simp only [Bool.false_eq_true, if_false, hs0.2, hs1.2]
      change (ell0 w < 0 ∨ ell1 w < 0) ↔ ¬ (0 < ell0 w ∧ 0 < ell1 w)
      rcases lt_or_gt_of_ne hw0 with h0 | h0 <;>
        rcases lt_or_gt_of_ne hw1 with h1 | h1 <;> simp [h0, h1, not_lt_of_ge h0.le,
          not_lt_of_ge h1.le]
    · simpa using hs0.1.and hs1.1
  constructor
  · intro hin
    have hray := hsign.mono (fun _ hr => hr.mpr hin)
    exact m64Intrinsic_regional_tangent_sector_unique_of_ray F b hFi hsource hfront hray hw
  · intro i hqi hi
    have henter := m64Intrinsic_coordinate_triangle_ray_enters (F i) (b i)
      (hFi i) (hsource i) hqi hi
    obtain ⟨r, hr, hs⟩ := (henter.and hsign).exists
    exact hs.mp (mem_iUnion.mpr ⟨i, interior_subset hr⟩)

end PoincareConjecture
