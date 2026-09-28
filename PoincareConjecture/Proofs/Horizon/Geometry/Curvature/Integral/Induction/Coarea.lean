import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Slab







set_option autoImplicit false

open Set MeasureTheory TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (g : RiemannianMetric (n + 1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M)
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)



theorem continuousOn_regularLevelIntegral_compact_slab
    {a b : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hKU : f ⁻¹' Icc a b ⊆ U) {h : M → ℝ} (hh : ContinuousOn h U) :
    ContinuousOn (fun c => ∫ z, h (openLevelIncl f U c z)
      ∂g.regularLevelVolume hf U hreg c) (Icc a b) := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (n + 1))) M
  obtain ⟨χ, hχone, hχcompact, hχsupport, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hcompact U.isOpen hKU
  let P := fun x => χ x * h x
  have hPs : tsupport P ⊆ U := tsupport_mul_subset_left.trans hχsupport
  have hPc : HasCompactSupport P := (show HasCompactSupport (χ : M → ℝ) from hχcompact).mul_right
  have hP : Continuous P :=
    (χ.continuous.continuousOn.mul hh).continuous_of_tsupport_subset U.isOpen hPs
  apply (g.continuous_regularLevelIntegral hf U hreg hP hPc hPs).continuousOn.congr
  intro c hc
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : openLevelIncl f U c z ∈ f ⁻¹' Icc a b := by
    change f (openLevelIncl f U c z) ∈ Icc a b
    rwa [show f (openLevelIncl f U c z) = c from z.2]
  simp only [P, hχone hz, Pi.one_apply, one_mul]



theorem integral_coarea_compact_slab
    {a b : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hKU : f ⁻¹' Icc a b ⊆ U) {h : M → ℝ} (hh : ContinuousOn h U) :
    (∫ x in f ⁻¹' Icc a b, h x ∂g.volumeMeasure) =
      ∫ c in Icc a b, ∫ z,
        h (openLevelIncl f U c z) /
          g.tangentNorm (openLevelIncl f U c z)
            (g.gradient f (openLevelIncl f U c z))
        ∂g.regularLevelVolume hf U hreg c := by
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (n + 1))) M
  obtain ⟨χ, hχone, hχcompact, hχsupport, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hcompact U.isOpen hKU
  let s := fun x => g.tangentNorm x (g.gradient f x)
  have hs : Continuous s := g.continuous_tangentNorm_gradient hf
  have hsne (x : M) (hx : x ∈ U) : s x ≠ 0 :=
    ((g.tangentNorm_gradient_pos_iff f x).mpr (hreg x hx)).ne'
  let P := fun x => χ x * (h x / s x)
  have hPs : tsupport P ⊆ U := tsupport_mul_subset_left.trans hχsupport
  have hPc : HasCompactSupport P := (show HasCompactSupport (χ : M → ℝ) from hχcompact).mul_right
  have hP : Continuous P :=
    (χ.continuous.continuousOn.mul (hh.div hs.continuousOn hsne)).continuous_of_tsupport_subset
      U.isOpen hPs
  have hPeq (x : M) (hx : x ∈ f ⁻¹' Icc a b) : P x = h x / s x := by
    dsimp only [P]
    rw [hχone hx, Pi.one_apply, one_mul]
  calc
    (∫ x in f ⁻¹' Icc a b, h x ∂g.volumeMeasure) =
        ∫ x in f ⁻¹' Icc a b, P x * s x ∂g.volumeMeasure := by
      apply setIntegral_congr_fun (isClosed_Icc.preimage hf.continuous).measurableSet
      intro x hx
      change h x = P x * s x
      rw [hPeq x hx, div_mul_cancel₀ _ (hsne x (hKU hx))]
    _ = ∫ c in Icc a b, ∫ z, P (openLevelIncl f U c z)
        ∂g.regularLevelVolume hf U hreg c :=
      g.integral_coarea_Icc hf U hreg hP hPc hPs a b
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro c hc
      apply integral_congr_ae
      filter_upwards [] with z
      apply hPeq
      change f (openLevelIncl f U c z) ∈ Icc a b
      rwa [show f (openLevelIncl f U c z) = c from z.2]

end PoincareConjecture.RiemannianMetric
