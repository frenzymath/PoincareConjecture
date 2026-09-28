import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.HypersurfaceFields
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.RegularDomain
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Slab








set_option autoImplicit false

open Set MeasureTheory
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {g : RiemannianMetric (n + 1) M}



theorem integral_hypersurface_bochner_slab (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : a < b) (hc : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x ∈ f ⁻¹' Icc a b,
      mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) :
    let U := g.regularDomain hf
    (∫ x in f ⁻¹' Icc a b, D.levelBochnerDifference f x ∂g.volumeMeasure) =
      (∫ z, D.levelMeanCurvature f (openLevelIncl f U b z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) b) -
      ∫ z, D.levelMeanCurvature f (openLevelIncl f U a z)
        ∂g.regularLevelVolume hf U (g.regularDomain_regular hf) a := by
  let U := g.regularDomain hf
  have hUq : (U : Set M) ⊆ {x | 0 < D.levelQ f x} := by
    intro x hx
    change 0 < Real.sqrt (D.levelQ f x) at hx
    exact Real.sqrt_pos.mp hx
  apply g.integral_slab_eq_level_sub_of_cutoff hf U (g.regularDomain_regular hf)
    hab hc (fun x hx => (g.mem_regularDomain_iff hf x).mpr (hreg x hx))
    ((D.continuousOn_levelBochnerDifference hf).mono hUq)
    ((D.continuousOn_levelMeanCurvature hf).mono hUq)
  intro η hη _ hηs
  have hs : tsupport (η ∘ f) ⊆ f ⁻¹' Icc a b :=
    (tsupport_comp_subset_preimage η hf.continuous).trans
      (preimage_mono (hηs.trans Ioo_subset_Icc_self))
  have hηc : HasCompactSupport (η ∘ f) :=
    HasCompactSupport.intro
      (hc.of_isClosed_subset (isClosed_tsupport (η ∘ f)) hs)
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  have hq : ∀ x ∈ tsupport (η ∘ f),
      0 < g.inner x (D.gradient f x) (D.gradient f x) := by
    intro x hx
    exact hUq ((g.mem_regularDomain_iff hf x).mpr (hreg x (hs hx)))
  exact D.integral_hypersurface_bochner_level_cutoff hf hη hηc hq

end PoincareConjecture.LeviCivitaData
