import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AreaDensity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Topology.Covering.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal Manifold ContDiff Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem m64Intrinsic_exists_global_normal_chart
    (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : ContDiff ℝ ∞ e)
    (hi : ∀ x : AnnulusCoordinates, Function.Injective (fderiv ℝ e x))
    (hglobal : Function.Injective e) :
    ∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
      (F : AnnulusCoordinates → AnnulusCoordinates) = e ∧
        F.source = (Set.univ : Set AnnulusCoordinates) ∧
        ContDiffOn ℝ ∞ F F.source ∧
        ContDiffOn ℝ ∞ F.symm F.target := by
  have hlocal : IsLocalHomeomorph e := by
    apply IsLocalHomeomorph.mk e
    intro x
    let A : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates :=
      (LinearEquiv.ofBijective (fderiv ℝ e x).toLinearMap
        ⟨hi x,
          (LinearMap.injective_iff_surjective
            (f := (fderiv ℝ e x).toLinearMap)).mp (hi x)⟩).toContinuousLinearEquiv
    have hA : A.toContinuousLinearMap = fderiv ℝ e x := rfl
    have hderiv : HasFDerivAt e A.toContinuousLinearMap x := by
      rw [hA]
      exact (he.differentiable (by simp) x).hasFDerivAt
    let F := he.contDiffAt.toOpenPartialHomeomorph e hderiv (by simp)
    refine ⟨F, he.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by simp), ?_⟩
    intro y hy
    exact congr_fun (he.contDiffAt.toOpenPartialHomeomorph_coe hderiv (by simp)) y
  have hopen : Topology.IsOpenEmbedding e := hlocal.isOpenEmbedding_of_injective hglobal
  let F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates :=
    hopen.toOpenPartialHomeomorph e
  have hF : (F : AnnulusCoordinates → AnnulusCoordinates) = e := by
    simp [F]
  have hsource : F.source = (Set.univ : Set AnnulusCoordinates) := by
    simp [F]
  have hinv : ContDiffOn ℝ ∞ F.symm F.target := by
    intro y hy
    let x : AnnulusCoordinates := F.symm y
    let A : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates :=
      (LinearEquiv.ofBijective (fderiv ℝ e x).toLinearMap
        ⟨hi x,
          (LinearMap.injective_iff_surjective
            (f := (fderiv ℝ e x).toLinearMap)).mp (hi x)⟩).toContinuousLinearEquiv
    have hA : A.toContinuousLinearMap = fderiv ℝ e x := rfl
    have hD : HasFDerivAt F A.toContinuousLinearMap x := by
      rw [hA, ← hF]
      exact (he.differentiable (by simp) x).hasFDerivAt
    have hFx : ContDiffAt ℝ ∞ F x := by
      rw [hF]
      exact he.contDiffAt
    exact (F.contDiffAt_symm hy hD hFx).contDiffWithinAt
  refine ⟨F, hF, hsource, ?_, hinv⟩
  rw [hsource]
  rw [hF]
  exact he.contDiffOn

theorem m64Intrinsic_global_normal_chart_area_lower
    (G : RiemannianMetric 2 AnnulusCoordinates)
    (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : ContDiff ℝ ∞ e)
    (hi : ∀ x : AnnulusCoordinates, Function.Injective (fderiv ℝ e x))
    (hglobal : Function.Injective e)
    {S : Set AnnulusCoordinates} (hS : MeasurableSet S)
    {c : ℝ} (speed : ℝ → ℝ)
    (hbound : ∀ x ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (speed (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        G.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x v)
          (mfderiv (𝓡 2) (𝓡 2) e x v))
    (himage : e '' S ⊆ standardAnnulusDomain) :
    (∫⁻ x in S, ENNReal.ofReal (c ^ 2 * speed (x 0))) ≤
      ENNReal.ofReal (intrinsicAnnulusArea G) := by
  obtain ⟨F, hF, hsource, hFdiff, hFinv⟩ :=
    m64Intrinsic_exists_global_normal_chart e he hi hglobal
  have hFmd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source := by
    rw [contMDiffOn_iff_contDiffOn]
    exact hFdiff
  have hFinvmd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target := by
    rw [contMDiffOn_iff_contDiffOn]
    exact hFinv
  have hSsource : S ⊆ F.source := by
    rw [hsource]
    exact Set.subset_univ S
  have hboundF : ∀ x ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (speed (x 0) ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        G.inner (F x) (mfderiv (𝓡 2) (𝓡 2) F x v)
          (mfderiv (𝓡 2) (𝓡 2) F x v) := by
    intro x hx v
    rw [hF]
    exact hbound x hx v
  have himageF : F '' S ⊆ standardAnnulusDomain := by
    simpa [hF] using himage
  exact m64Intrinsic_chart_area_lower G F hFmd hFinvmd hS hSsource speed
    hboundF himageF

theorem m64Intrinsic_compact_normal_fiber_finite
    (e : AnnulusCoordinates → AnnulusCoordinates)
    (hlocal : IsLocalHomeomorph e)
    {K : Set AnnulusCoordinates} (hK : IsCompact K)
    (y : AnnulusCoordinates) :
    (K ∩ e ⁻¹' {y}).Finite := by
  have hclosed : IsClosed (e ⁻¹' {y}) :=
    isClosed_singleton.preimage hlocal.continuous
  have hcompact : IsCompact (K ∩ e ⁻¹' {y}) := hK.inter_right hclosed
  have hdiscrete : IsDiscrete (K ∩ e ⁻¹' {y}) := by
    apply IsDiscrete.of_openPartialHomeomorph e inter_subset_right
    intro x hx
    obtain ⟨φ, hxφ, hφ⟩ := hlocal x
    exact ⟨φ, hxφ, hφ.symm⟩
  exact hcompact.finite hdiscrete

theorem m64Intrinsic_compact_normal_fiber_bounded_multiplicity
    (e : AnnulusCoordinates → AnnulusCoordinates)
    (hlocal : IsLocalHomeomorph e)
    {K : Set AnnulusCoordinates} (hK : IsCompact K) :
    ∃ n : ℕ, ∀ y : AnnulusCoordinates,
      (K ∩ e ⁻¹' {y}).ncard ≤ n := by
  classical
  let F : AnnulusCoordinates → OpenPartialHomeomorph AnnulusCoordinates
      AnnulusCoordinates := fun x => Classical.choose (hlocal x)
  have hFx (x : AnnulusCoordinates) : x ∈ (F x).source := by
    exact (Classical.choose_spec (hlocal x)).1
  have heF (x : AnnulusCoordinates) : e = (F x : AnnulusCoordinates → AnnulusCoordinates) := by
    exact (Classical.choose_spec (hlocal x)).2
  let U : AnnulusCoordinates → Set AnnulusCoordinates := fun x => (F x).source
  have hUopen (x : AnnulusCoordinates) : IsOpen (U x) := by
    exact (F x).open_source
  have hUcover : K ⊆ ⋃ x : AnnulusCoordinates, U x := by
    intro x hx
    exact mem_iUnion.2 ⟨x, hFx x⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUopen hUcover
  refine ⟨t.card, ?_⟩
  intro y
  let A : AnnulusCoordinates → Set AnnulusCoordinates := fun x =>
    (K ∩ e ⁻¹' {y}) ∩ U x
  have hAfinite (x : AnnulusCoordinates) : (A x).Finite := by
    have hfinite : (K ∩ e ⁻¹' {y}).Finite :=
      m64Intrinsic_compact_normal_fiber_finite e hlocal hK y
    exact hfinite.subset inter_subset_left
  have hAsubsingleton (x : AnnulusCoordinates) : (A x).Subsingleton := by
    intro a ha b hb
    have hae : e a = y := by simpa [A] using ha.1.2
    have hbe : e b = y := by simpa [A] using hb.1.2
    have hab : e a = e b := hae.trans hbe.symm
    have hUinj : (U x).InjOn e := by
      intro p hp q hq hpq
      rw [heF x] at hpq
      exact (F x).injOn hp hq hpq
    exact hUinj ha.2 hb.2 hab
  have hsub : K ∩ e ⁻¹' {y} ⊆ ⋃ x ∈ t, A x := by
    intro z hz
    obtain ⟨x, hxt, hzU⟩ := mem_iUnion₂.mp (ht hz.1)
    exact mem_iUnion₂.2 ⟨x, hxt, ⟨hz, hzU⟩⟩
  have hUnionFinite : (⋃ x ∈ t, A x).Finite := by
    exact t.finite_toSet.biUnion (fun x _ => hAfinite x)
  calc
    (K ∩ e ⁻¹' {y}).ncard ≤ (⋃ x ∈ t, A x).ncard :=
      Set.ncard_le_ncard hsub hUnionFinite
    _ ≤ ∑ x ∈ t, (A x).ncard := Finset.set_ncard_biUnion_le t A
    _ ≤ ∑ x ∈ t, 1 := by
      apply Finset.sum_le_sum
      intro x hx
      exact (Set.ncard_le_one (hAfinite x)).2 (fun a ha b hb => hAsubsingleton x ha hb)
    _ = t.card := by simp

end PoincareConjecture
