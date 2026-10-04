import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Regional.TangentSectors
import Mathlib.Analysis.Calculus.FDeriv.Affine
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Almost-everywhere partition by actual regional tangent sectors

The derivative of an inverse barycentric coordinate is nonzero, because
the chart differential is invertible and the affine coordinate is
nonconstant. Its kernel is null. Thus almost every physical direction at
an interior regional vertex belongs to exactly one occupied sector.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- Invertibility of the actual smooth chart forces every inverse barycentric coordinate
differential to be nonzero. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481,
especially Claim 19.40, pp. 470-471; the explicit project tangent-fan derivation is reviewed
in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical Checks. -/
theorem m64Intrinsic_inverse_coordinate_derivative_ne_zero
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {q : AnnulusCoordinates} (hq : q ∈ F.target) (k : Fin 3) :
    fderiv ℝ (fun x => b.coord k (F.symm x)) q ≠ 0 := by
  let c : AnnulusCoordinates →ᴬ[ℝ] ℝ :=
    { toAffineMap := b.coord k, cont := (b.coord k).continuous_of_finiteDimensional }
  have hD : F.MDifferentiable (𝓡 2) (𝓡 2) :=
    ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
  have hsurj : Function.Surjective (fderiv ℝ F.symm q) := by
    have h := hD.symm.mfderiv_surjective hq
    simp only [mfderiv_eq_fderiv, TangentSpace] at h
    exact h
  have hdi : DifferentiableAt ℝ F.symm q :=
    (((contMDiffOn_iff_contDiffOn.mp hFi) q hq).contDiffAt
      (F.open_target.mem_nhds hq)).differentiableAt (by simp)
  have hderiv : fderiv ℝ (fun x => b.coord k (F.symm x)) q =
      c.contLinear.comp (fderiv ℝ F.symm q) := by
    exact (c.hasFDerivAt.comp q hdi.hasFDerivAt).fderiv
  obtain ⟨j, hjk⟩ := exists_ne k
  obtain ⟨w, hw⟩ := hsurj (b k - b j)
  have hval : fderiv ℝ (fun x => b.coord k (F.symm x)) q w = 1 := by
    rw [hderiv, ContinuousLinearMap.comp_apply, hw]
    change (b.coord k).linear (b k - b j) = 1
    have hl : (b.coord k).linear (b k - b j) = b.coord k (b k) - b.coord k (b j) :=
      (b.coord k).linearMap_vsub _ _
    rw [hl, b.coord_apply_eq, b.coord_apply_ne hjk.symm]
    norm_num
  intro hzero
  rw [hzero, zero_apply] at hval
  norm_num at hval

/-- Tangent directions parallel to an actual coordinate side form a null linear subspace; no
transversality hypothesis is supplied. Source: Morgan--Tian Proposition 19.35, printed pp.
467-481, especially Claim 19.40, pp. 470-471; the explicit project tangent-fan derivation is
reviewed in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical
Checks. -/
theorem m64Intrinsic_inverse_coordinate_kernel_null
    (F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {q : AnnulusCoordinates} (hq : q ∈ F.target) (k : Fin 3) :
    volume {w : AnnulusCoordinates | fderiv ℝ (fun x => b.coord k (F.symm x)) q w = 0} = 0 := by
  let L := fderiv ℝ (fun x => b.coord k (F.symm x)) q
  have hne : L ≠ 0 := m64Intrinsic_inverse_coordinate_derivative_ne_zero F b hF hFi hq k
  change volume (LinearMap.ker L.toLinearMap : Set AnnulusCoordinates) = 0
  apply Measure.addHaar_submodule
  rw [Ne, LinearMap.ker_eq_top]
  intro hzero
  apply hne
  ext w
  have h := congrArg (fun A : AnnulusCoordinates →ₗ[ℝ] ℝ => A w) hzero
  change L.toLinearMap w = 0 at h
  exact h

/-- Almost every direction at an interior point of the actual finite region lies in exactly
one occupied tangent sector. The exceptional directions are removed using the proved nullity
of the actual side differentials, rather than an assumed angular partition. Source:
Morgan--Tian Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp. 470-471;
the explicit project tangent-fan derivation is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical Checks. -/
theorem m64Intrinsic_regional_tangent_partition_ae
    {I : Type*} [Finite I]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hfront : ∀ i j, i ≠ j →
      (F i '' convexHull ℝ (range (b i))) ∩ (F j '' convexHull ℝ (range (b j))) ⊆
        frontier (F i '' convexHull ℝ (range (b i)))) {q : AnnulusCoordinates}
    (hq : q ∈ interior (⋃ i, F i '' convexHull ℝ (range (b i)))) :
    ∀ᵐ w : AnnulusCoordinates, ∃! i, q ∈ F i '' convexHull ℝ (range (b i)) ∧
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
  exact m64Intrinsic_regional_tangent_sector_unique F b hFi hsource hfront hq hw

/-- The actual occupied tangent sectors split every measurable tangent set with no overlap
and no lost area. This includes tangent disks and metric ellipses and supplies an exact area
identity for corner fans. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481,
especially Claim 19.40, pp. 470-471; the explicit project tangent-fan derivation is reviewed
in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-fans.md`, Mathematical Checks. -/
theorem m64Intrinsic_regional_tangent_sector_volume_sum
    {I : Type*} [Fintype I]
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
    (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hfront : ∀ i j, i ≠ j →
      (F i '' convexHull ℝ (range (b i))) ∩ (F j '' convexHull ℝ (range (b j))) ⊆
        frontier (F i '' convexHull ℝ (range (b i)))) {q : AnnulusCoordinates}
    (hq : q ∈ interior (⋃ i, F i '' convexHull ℝ (range (b i))))
    (A : Set AnnulusCoordinates) (hA : MeasurableSet A) :
    (∑ i, volume (A ∩ {w : AnnulusCoordinates |
      q ∈ F i '' convexHull ℝ (range (b i)) ∧
      ∀ k, (b i).coord k ((F i).symm q) = 0 →
        0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w})) = volume A := by
  classical
  let C (i : I) : Set AnnulusCoordinates := {w |
    q ∈ F i '' convexHull ℝ (range (b i)) ∧
    ∀ k, (b i).coord k ((F i).symm q) = 0 →
      0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w}
  have hopen (i : I) : IsOpen (C i) := by
    have hk (k : Fin 3) : IsOpen {w : AnnulusCoordinates |
        (b i).coord k ((F i).symm q) = 0 →
          0 < fderiv ℝ (fun x => (b i).coord k ((F i).symm x)) q w} := by
      by_cases hzero : (b i).coord k ((F i).symm q) = 0
      · simp only [hzero, true_implies]
        exact isOpen_lt continuous_const (ContinuousLinearMap.continuous _)
      · simp only [hzero, false_implies, ofPred_true]
        exact isOpen_univ
    by_cases hqi : q ∈ F i '' convexHull ℝ (range (b i))
    · simpa only [C, hqi, true_and, ofPred_forall] using isOpen_iInter_of_finite hk
    · simp only [C, hqi, false_and, ofPred_false]
      exact isOpen_empty
  have hdisj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro w hi hj
    exact m64Intrinsic_coordinate_triangle_tangent_sectors_disjoint
      (F i) (F j) (b i) (b j) (hFi i) (hFi j) (hsource i) (hsource j)
      (hfront i j hij) hi.1 hj.1 hi.2 hj.2
  have hcover : (⋃ i, C i) =ᵐ[volume] (univ : Set AnnulusCoordinates) := by
    filter_upwards [m64Intrinsic_regional_tangent_partition_ae F b hF hFi hsource hfront hq]
      with w hw
    obtain ⟨i, hi, _⟩ := hw
    exact propext ⟨fun _ => mem_univ w, fun _ => mem_iUnion.mpr ⟨i, hi⟩⟩
  change (∑ i, volume (A ∩ C i)) = volume A
  calc
    (∑ i, volume (A ∩ C i)) = volume (⋃ i, A ∩ C i) := by
      symm
      simpa only [tsum_fintype] using measure_iUnion
        (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right)
        (fun i => hA.inter (hopen i).measurableSet)
    _ = volume (A ∩ ⋃ i, C i) := by rw [inter_iUnion]
    _ = volume A := by
      apply measure_congr
      filter_upwards [hcover] with w hw
      change (w ∈ ⋃ i, C i) = (w ∈ (univ : Set AnnulusCoordinates)) at hw
      change (w ∈ A ∧ w ∈ ⋃ i, C i) = (w ∈ A)
      have hw' : w ∈ ⋃ i, C i := hw.symm ▸ mem_univ w
      exact propext ⟨And.left, fun h => ⟨h, hw'⟩⟩

end PoincareMT
