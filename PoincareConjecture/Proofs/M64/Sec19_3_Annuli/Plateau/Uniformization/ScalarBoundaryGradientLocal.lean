import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryGradient
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarBoundaryH3














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology InnerProductSpace

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet
open Poincare.Analysis.Sobolev
open Weak Euclidean

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)









theorem exists_annular_boundary_continuous_gradient :
    ∃ u : H1Zero D scalarAnnulus,
      (∀ v : H1Zero D scalarAnnulus,
        gradientEnergy D scalarAnnulus u v = boundaryForcing D scalarAnnulus
          annularBoundaryExtension annularBoundaryExtension_smooth
          annularBoundaryExtension_compact v) ∧
      ∀ x : closure scalarAnnulus,
        ∃ (e : OpenPartialHomeomorph Plane Plane) (χ : Plane → ℝ)
          (V U : Set Plane) (ψ : Plane → ℝ) (G : Fin 2 → Plane → ℝ),
          (x : Plane) ∈ e.target ∧ e.symm x ∈ U ∧ IsOpen U ∧
          IsCompact (closure U) ∧ closure U ⊆ V ∧ IsOpen V ∧
          IsCompact (closure V) ∧ closure V ⊆ e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
          ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
          ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
          tsupport χ ⊆ e.target ∧ (∀ z ∈ V, χ (e z) = 1) ∧
          (∀ z ∈ e.source, e z ∈ scalarAnnulus ↔ 0 < z 0) ∧
          ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ V ∧
          (∀ z ∈ U, ψ z = 1) ∧ (∀ i, Continuous (G i)) ∧
          ∀ i, chosenWeakPartial' 2 i
              (fun z => ψ z * chartPullback e
                (fun y => χ y * toL2 D scalarAnnulus u y) z)
              {z : Plane | 0 < z 0} =ᵐ[
                volume.restrict {z : Plane | 0 < z 0}] G i := by
  obtain ⟨u, hforce, hboundary⟩ := exists_annular_boundary_H3_correction D
  refine ⟨u, hforce, ?_⟩
  intro x
  obtain ⟨e, χ, V, hx, hxV, hV, hVc, hVs, he, hei, hχ, hc, hs, hone, hflat,
    hu3⟩ := hboundary x
  obtain ⟨U, hU, hxU, hUV, hUc⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := e.symm (x : Plane))) hV
    (singleton_subset_iff.mpr hxV)
  obtain ⟨ψ, hψ, hψc, -, hψone, hψs⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff hUc hV hUV
  obtain ⟨G, hGc, hG⟩ := exists_continuous_halfSpace_gradient_of_local_H3
    hV hu3 hψ hψc hψs
  refine ⟨e, χ, V, U, ψ, G, hx, hxU (mem_singleton _), hU, hUc, hUV, hV,
    hVc, hVs, he, hei, hχ, hc, hs, hone, hflat, hψ, hψc, hψs, ?_, hGc, ?_⟩
  · intro z hz
    exact hψone z (subset_closure hz)
  · exact hG

end PoincareConjecture.M64Uniformization
