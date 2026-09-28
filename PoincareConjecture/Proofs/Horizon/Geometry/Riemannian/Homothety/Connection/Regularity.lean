import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Connection.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Connection.Cutoff
import Mathlib.Geometry.Manifold.VectorBundle.Hom












set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Homothety

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M]


theorem exists_smooth_field_eventuallyEq (U : Set M) (hU : IsOpen U)
    (V : (x : M) → TangentSpace (𝓡 n) x)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U)
    (x : M) (hx : x ∈ U) :
    ∃ W : (p : M) → TangentSpace (𝓡 n) p,
      ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) ∧
        W =ᶠ[nhds x] V := by
  obtain ⟨b, hb, hsupp, hnear⟩ := exists_smooth_cutoff (n := n) U hU x hx
  refine ⟨b • V, hb.contMDiffOn.smul_section_of_tsupport hU hsupp hV, ?_⟩
  filter_upwards [hnear] with p hp
  change b p • V p = V p
  change b p = 1 at hp
  rw [hp, one_smul]


theorem connection_contMDiffOn (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (U : Set M) (hU : IsOpen U) (V : (x : M) → TangentSpace (𝓡 n) x)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U) :
    ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun q : M ↦ TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q)
        p (D.connection V p)) U := by
  intro x hx
  obtain ⟨W, hW, hWV⟩ := exists_smooth_field_eventuallyEq U hU V hV x hx
  have hW' : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (∞ + 1) (T% W) Set.univ := hW.contMDiffOn.of_le (by decide)
  have hDW := D.smooth.contMDiff.contMDiff hW'
  have hnear :
      (fun p ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun q : M ↦ TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q)
        p (D.connection W p)) =ᶠ[nhds x]
      (fun p ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (E := fun q : M ↦ TangentSpace (𝓡 n) q →L[ℝ] TangentSpace (𝓡 n) q)
        p (D.connection V p)) := by
    filter_upwards [hWV.eventuallyEq_nhds, hU.mem_nhds hx] with p hp hUp
    have H := D.connection.isCovariantDerivativeOn.congr_of_eventuallyEq
      ((hW p).mdifferentiableAt (by simp))
      ((hV.contMDiffAt (hU.mem_nhds hUp)).mdifferentiableAt (by simp)) Filter.univ_mem hp
    exact congrArg (Bundle.TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) p) H
  exact ((contMDiffOn_univ.mp hDW).contMDiffAt.congr_of_eventuallyEq
    hnear.symm).contMDiffWithinAt


theorem connection_apply_contMDiffOn (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (U : Set M) (hU : IsOpen U) (V W : (x : M) → TangentSpace (𝓡 n) x)
    (hV : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% V) U)
    (hW : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% W) U) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% (fun p ↦ D.connection W p (V p))) U :=
  (connection_contMDiffOn g D U hU W hW).clm_bundle_apply hV

end PoincareConjecture.Homothety
