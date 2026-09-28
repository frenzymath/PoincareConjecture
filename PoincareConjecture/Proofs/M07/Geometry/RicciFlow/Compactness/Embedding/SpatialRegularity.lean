import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.TimeIndependent
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SmoothSpacetimeEmbedding

variable {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
  {F : BasedFlow n T' T C} {G : BasedFlow n T' T D}
  {U : Set C.carrier}

theorem spatialMap_contMDiffAt
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U) {t : ℝ} (ht : t ∈ Ioo T' T)
    {x : C.carrier} (hx : x ∈ U) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun y ↦ (e.toFun (t, y)).2) x := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : TopologicalSpace D.carrier := D.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  have hdomain : Ioo T' T ×ˢ U ∈ 𝓝 (t, x) := by
    exact (isOpen_Ioo.prod hU).mem_nhds ⟨ht, hx⟩
  have hspacetime := e.smooth_on.contMDiffAt hdomain
  have hslice : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun y : C.carrier ↦ (t, y)) x := by
    exact contMDiffAt_const.prodMk contMDiffAt_id
  exact (hspacetime.comp x hslice).snd

theorem spatialMap_mfderiv_injective
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U) {t : ℝ} (ht : t ∈ Ioo T' T)
    {x : C.carrier} (hx : x ∈ U) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) (fun y ↦ (e.toFun (t, y)).2) x) := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : TopologicalSpace D.carrier := D.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let f : C.carrier → D.carrier := fun y ↦ (e.toFun (t, y)).2
  let g : D.carrier → C.carrier := fun y ↦ (e.inverse (t, y)).2
  have hpair (y : C.carrier) : e.toFun (t, y) = (t, f y) :=
    Prod.ext (e.time_preserving t y) rfl
  have hmaps : MapsTo (fun y : D.carrier ↦ (t, y)) (f '' U)
      (e.toFun '' (Ioo T' T ×ˢ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(t, y), ⟨ht, hy⟩, hpair y⟩
  have hinv : ContMDiffWithinAt (𝓡 n) (𝓡 n) ∞ g (f '' U) (f x) := by
    have hs := e.smooth_inverse_on (t, f x) (hmaps ⟨x, hx, rfl⟩)
    have hslice : ContMDiffWithinAt (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : D.carrier ↦ (t, y)) (f '' U) (f x) :=
      contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
    exact (hs.comp (f x) hslice hmaps).snd
  have hleft : ∀ y ∈ U, (g ∘ f) y = id y := by
    intro y hy
    have h := congrArg Prod.snd (e.left_inverse (t, y) ⟨ht, hy⟩)
    simpa only [hpair, Function.comp_apply, id_eq, g] using h
  have hf : MDifferentiableAt (𝓡 n) (𝓡 n) f x :=
    (e.spatialMap_contMDiffAt hU ht hx).mdifferentiableAt (by simp)
  have hu : UniqueMDiffWithinAt (𝓡 n) U x := hU.uniqueMDiffWithinAt hx
  have hcomp := mfderivWithin_comp x (hinv.mdifferentiableWithinAt (by simp))
    hf.mdifferentiableWithinAt (fun y hy ↦ ⟨y, hy, rfl⟩) hu
  rw [mfderivWithin_congr_of_mem hleft hx, mfderivWithin_id hu,
    mfderivWithin_eq_mfderiv hu hf] at hcomp
  change Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)
  intro v w hvw
  have h := congrArg (mfderivWithin (𝓡 n) (𝓡 n) g (f '' U) (f x)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hcomp] at h
  exact h

theorem spatialMap_mfderiv_bijective
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U) {t : ℝ} (ht : t ∈ Ioo T' T)
    {x : C.carrier} (hx : x ∈ U) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) (fun y ↦ (e.toFun (t, y)).2) x) := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : TopologicalSpace D.carrier := D.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  have hi := e.spatialMap_mfderiv_injective hU ht hx
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 n) x) =
      Module.finrank ℝ (TangentSpace (𝓡 n) ((e.toFun (t, x)).2)) := by
    unfold TangentSpace
    rfl
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) ((e.toFun (t, x)).2)) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
  refine ⟨hi, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hi

noncomputable def spatialMap_mfderiv_linearEquiv
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U) {t : ℝ} (ht : t ∈ Ioo T' T)
    {x : C.carrier} (hx : x ∈ U) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
    letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
    TangentSpace (𝓡 n) x ≃ₗ[ℝ]
      TangentSpace (𝓡 n) ((e.toFun (t, x)).2) := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : TopologicalSpace D.carrier := D.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  letI : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 n) ((e.toFun (t, x)).2)) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
  have hb := e.spatialMap_mfderiv_bijective hU ht hx
  exact LinearEquiv.ofBijective (mfderiv (𝓡 n) (𝓡 n)
    (fun y ↦ (e.toFun (t, y)).2) x).toLinearMap hb

end PoincareConjecture.SmoothSpacetimeEmbedding
