import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.LocalDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.AncientSpacetimeEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {tau : ℝ} {R : AncientRescaling K tau}
  {L : AncientLimitFlow n} {J : Set ℝ} {U : Set L.carrier.carrier}

theorem spatialMap_contMDiffAt
    (e : AncientSpacetimeEmbedding (K := K) (R := R) L (J ×ˢ U))
    (hU : @IsOpen L.carrier.carrier L.carrier.topologicalSpace U)
    {t : ℝ} (ht : t ∈ J) {x : L.carrier.carrier} (hx : x ∈ U) :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier := L.carrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ L.carrier.carrier := L.carrier.isManifold
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun y => (e.toFun (t, y)).2) x := by
  let : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier := L.carrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ L.carrier.carrier := L.carrier.isManifold
  have hslice : ContMDiffWithinAt (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun y : L.carrier.carrier => (t, y)) U x :=
    contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
  have hs := ((e.smooth_on (t, x) ⟨ht, hx⟩).comp x hslice
    (fun y hy => ⟨ht, hy⟩)).snd
  exact hs.contMDiffAt (hU.mem_nhds hx)

theorem spatialMap_mfderiv_injective
    (e : AncientSpacetimeEmbedding (K := K) (R := R) L (J ×ˢ U))
    (hU : @IsOpen L.carrier.carrier L.carrier.topologicalSpace U)
    {t : ℝ} (ht : t ∈ J) {x : L.carrier.carrier} (hx : x ∈ U) :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier := L.carrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ L.carrier.carrier := L.carrier.isManifold
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) (fun y => (e.toFun (t, y)).2) x) := by
  let : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier := L.carrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ L.carrier.carrier := L.carrier.isManifold
  let f : L.carrier.carrier → M := fun y => (e.toFun (t, y)).2
  let g : M → L.carrier.carrier := fun y => (e.inverse (t, y)).2
  have hpair (y : L.carrier.carrier) : e.toFun (t, y) = (t, f y) :=
    Prod.ext (e.time_preserving t y) rfl
  have hmaps : MapsTo (fun y : M => (t, y)) (f '' U) (e.toFun '' (J ×ˢ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(t, y), ⟨ht, hy⟩, hpair y⟩
  have hinv : ContMDiffWithinAt (𝓡 n) (𝓡 n) ∞ g (f '' U) (f x) := by
    have hs := e.smooth_inverse_on (t, f x) (hmaps ⟨x, hx, rfl⟩)
    have hslice : ContMDiffWithinAt (𝓡 n) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun y : M => (t, y)) (f '' U) (f x) :=
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
    hf.mdifferentiableWithinAt (fun y hy => ⟨y, hy, rfl⟩) hu
  rw [mfderivWithin_congr_of_mem hleft hx, mfderivWithin_id hu,
    mfderivWithin_eq_mfderiv hu hf] at hcomp
  change Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x)
  intro v w hvw
  have h := congrArg (mfderivWithin (𝓡 n) (𝓡 n) g (f '' U) (f x)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hcomp] at h
  exact h

theorem spatialMap_mfderiv_bijective
    (e : AncientSpacetimeEmbedding (K := K) (R := R) L (J ×ˢ U))
    (hU : @IsOpen L.carrier.carrier L.carrier.topologicalSpace U)
    {t : ℝ} (ht : t ∈ J) {x : L.carrier.carrier} (hx : x ∈ U) :
    letI : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier := L.carrier.chartedSpace
    letI : IsManifold (𝓡 n) ∞ L.carrier.carrier := L.carrier.isManifold
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) (fun y => (e.toFun (t, y)).2) x) := by
  let : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) L.carrier.carrier := L.carrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ L.carrier.carrier := L.carrier.isManifold
  have hi := e.spatialMap_mfderiv_injective hU ht hx
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 n) x) =
      Module.finrank ℝ (TangentSpace (𝓡 n) ((e.toFun (t, x)).2)) := by
    unfold TangentSpace
    rfl
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) ((e.toFun (t, x)).2)) := by
    unfold TangentSpace
    exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.finiteDimensional_of_finite
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hi⟩

end PoincareConjecture.AncientSpacetimeEmbedding
