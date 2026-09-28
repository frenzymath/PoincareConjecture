import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Local
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.LevelSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Partition







set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M)
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)

local instance global_finrank :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

include hf hreg in


theorem integral_coarea
    {h : M → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (hs : tsupport h ⊆ U) :
    (∫ x in (U : Set M), h x * g.tangentNorm x (g.gradient f x)
      ∂g.volumeMeasure) =
    ∫ c : ℝ, ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (n + 1))) M
  let eAt : ∀ p : M, p ∈ tsupport h →
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (n + 1))) M := fun p hp =>
    Classical.choose (exists_regular_coordinates hf U (hs hp) (hreg p (hs hp)))
  have eAt_target : ∀ (p : M) (hp : p ∈ tsupport h),
      p ∈ (eAt p hp).target := fun p hp =>
    (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).1
  have eAt_subset : ∀ (p : M) (hp : p ∈ tsupport h),
      (eAt p hp).target ⊆ U := fun p hp =>
    (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).2.1
  have eAt_smooth : ∀ (p : M) (hp : p ∈ tsupport h),
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (eAt p hp) (eAt p hp).source :=
    fun p hp => (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).2.2.1
  have eAt_smooth_symm : ∀ (p : M) (hp : p ∈ tsupport h),
      ContMDiffOn (𝓡 (n + 1)) (𝓡 (n + 1)) ∞ (eAt p hp).symm (eAt p hp).target :=
    fun p hp => (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).2.2.2.1
  have eAt_level : ∀ (p : M) (hp : p ∈ tsupport h) (y : EuclideanSpace ℝ (Fin (n + 1))),
      y ∈ (eAt p hp).source → f ((eAt p hp) y) = y 0 :=
    fun p hp => (Classical.choose_spec (exists_regular_coordinates hf U (hs hp)
      (hreg p (hs hp)))).2.2.2.2
  have hcover : tsupport h ⊆ ⋃ p : tsupport h, (eAt p p.2).target := by
    intro x hx
    exact mem_iUnion_of_mem ⟨x, hx⟩ (eAt_target x hx)
  obtain ⟨s, H, hHcont, hHcompact, hHsupport, hHsum⟩ :=
    Poincare.Coarea.exists_finite_continuous_decomposition
      (fun p : tsupport h => (eAt p p.2).target)
      (fun p => (eAt p p.2).open_target)
      hh hc hcover
  have hlocal : ∀ i : s,
      (∫ x, H i x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) =
      ∫ c : ℝ, ∫ z, H i (openLevelIncl f U c z)
        ∂g.regularLevelVolume hf U hreg c := by
    intro i
    let p : tsupport h := i.1
    let e := eAt p p.2
    have htarget : e.target ⊆ U := eAt_subset p p.2
    exact g.integral_coarea_of_chart_support hf U hreg e htarget
      (eAt_level p p.2) (eAt_smooth p p.2) (eAt_smooth_symm p p.2)
      (hHcont i) (hHcompact i) ((hHsupport i).trans inter_subset_left)
  have hleft : ∀ i : s, Integrable (fun x =>
      H i x * g.tangentNorm x (g.gradient f x)) g.volumeMeasure := by
    intro i
    exact g.integrable_volumeMeasure_of_hasCompactSupport
      ((hHcont i).mul (g.continuous_tangentNorm_gradient hf)) (hHcompact i).mul_right
  have hright : ∀ i : s, Integrable (fun c : ℝ =>
      ∫ z, H i (openLevelIncl f U c z) ∂g.regularLevelVolume hf U hreg c) := by
    intro i
    let p : tsupport h := i.1
    let e := eAt p p.2
    have htarget : e.target ⊆ U := eAt_subset p p.2
    exact (integrable_regularLevelIntegral_of_chart_support g hf U hreg
      (eAt p p.2) htarget (eAt_level p p.2) (eAt_smooth p p.2)
      (eAt_smooth_symm p p.2) (hHcont i) (hHcompact i)
      ((hHsupport i).trans inter_subset_left))
  have hinner : ∀ (c : ℝ) (i : s), Integrable (fun z => H i (openLevelIncl f U c z))
      (g.regularLevelVolume hf U hreg c) := fun c i =>
    g.integrable_regularLevelVolume_of_hasCompactSupport hf U hreg c
      (hHcont i) (hHcompact i) (((hHsupport i).trans inter_subset_right).trans hs)
  calc
    (∫ x in (U : Set M), h x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure) =
        ∫ x, h x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), zero_mul]
    _ = ∫ x, ∑ i : s, H i x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Finset.sum_mul, hHsum]
    _ = ∑ i : s, ∫ x, H i x * g.tangentNorm x (g.gradient f x) ∂g.volumeMeasure :=
      integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i : s, ∫ c : ℝ, ∫ z, H i (openLevelIncl f U c z)
        ∂g.regularLevelVolume hf U hreg c := Finset.sum_congr rfl (fun i _ => hlocal i)
    _ = ∫ c : ℝ, ∑ i : s, ∫ z, H i (openLevelIncl f U c z)
        ∂g.regularLevelVolume hf U hreg c :=
      (integral_finsetSum _ (fun i _ => hright i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with c
      rw [← integral_finsetSum _ (fun i _ => hinner c i)]
      apply integral_congr_ae
      filter_upwards [] with z
      exact hHsum (openLevelIncl f U c z)

end PoincareConjecture.RiemannianMetric
