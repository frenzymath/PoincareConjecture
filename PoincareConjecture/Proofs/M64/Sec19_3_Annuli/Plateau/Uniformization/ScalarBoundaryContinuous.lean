import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryH3
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Embedding.Continuous

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem exists_annular_boundary_continuous_correction :
    ∃ u : H1Zero D scalarAnnulus,
      (∀ v : H1Zero D scalarAnnulus,
        gradientEnergy D scalarAnnulus u v = boundaryForcing D scalarAnnulus
          annularBoundaryExtension annularBoundaryExtension_smooth
          annularBoundaryExtension_compact v) ∧
      ∀ x : closure scalarAnnulus,
        ∃ (e : OpenPartialHomeomorph Plane Plane) (V : Set Plane) (F : Plane → ℝ),
          (x : Plane) ∈ e.target ∧ e.symm x ∈ V ∧ IsOpen V ∧
          IsCompact (closure V) ∧ closure V ⊆ e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          (∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0) ∧ Continuous F ∧
          (fun z => toL2 D scalarAnnulus u (e z))
            =ᵐ[volume.restrict (V ∩ {z : Plane | 0 < z 0})] F ∧
          ∀ z : Plane, z 0 ≤ 0 → F z = 0 := by
  obtain ⟨u, hu, hboundary⟩ := exists_annular_boundary_H3_correction D
  refine ⟨u, hu, ?_⟩
  intro x
  obtain ⟨e, χ, W, hx, hxW, hW, hWc, hWs, he, hei, hχ, hc, hs, hone, hflat, hu3⟩ :=
    hboundary x
  obtain ⟨V, hV, hxV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm x)) hW (singleton_subset_iff.mpr hxW)
  obtain ⟨ψ, hψ, hψc, _, hψone, hψs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hVc hW hVW
  have hVW' : V ⊆ W := subset_closure.trans hVW
  let U := chartPullback e (fun y => χ y * toL2 D scalarAnnulus u y)
  let Half : Set Plane := {z | 0 < z 0}
  have hH : IsOpen Half := BoundaryTangential.isOpen_halfSpace
  have hu0 : Weak.MemW01p 2 U Half :=
    Boundary.memW01p_chartPullback_toL2 e he hei χ hχ hc hs hflat u
  have hw0 := BoundaryTangential.memW01p_mul_smooth hH hu0 hψ hψc
  have hw3 := BoundaryLocalization.memWkp_mul_smooth_of_tsupport_subset 3
    hH hW hu3 hψ hψc hψs
  obtain ⟨F, hF, hUF, hzero⟩ :=
    BoundaryEmbedding.exists_continuous_zero_extension hψc.mul_right hw0 hw3
  refine ⟨e, V, F, hx, hxV (mem_singleton _), hV, hVc,
    hVW.trans (subset_closure.trans hWs), he, hei, hflat, hF, ?_, hzero⟩
  filter_upwards [ae_restrict_of_ae hUF, ae_restrict_mem (hV.inter hH).measurableSet]
    with z hz hzV
  change Half.indicator (ψ * U) z = F z at hz
  simpa only [indicator_of_mem (show z ∈ Half from hzV.2), Pi.mul_apply,
    hψone z (subset_closure hzV.1),
    one_mul, U, chartPullback_apply e _ (hWs (subset_closure (hVW' hzV.1))),
    hone z (hVW' hzV.1)] using hz

end PoincareConjecture.M64Uniformization
