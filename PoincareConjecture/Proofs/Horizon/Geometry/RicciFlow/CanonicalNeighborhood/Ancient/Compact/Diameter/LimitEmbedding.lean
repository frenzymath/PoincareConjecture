import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.Exhaustion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace NormalizedKappaSpacetimeEmbedding

variable {kappa : ℝ} {source target : BasedKappaSolution kappa}
  {J : Set ℝ} {U : Set target.carrier.carrier}

theorem spatial_contMDiffAt
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : t ∈ J)
    {x : target.carrier.carrier} (hx : x ∈ U) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y ↦ (e.toFun (t, y)).2) x := by
  have hs := e.smooth_on.comp
    (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun y hy ↦ ⟨ht, hy⟩)
  exact (hs x hx).snd.contMDiffAt (hU.mem_nhds hx)

theorem spatial_mfderiv_injective
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : t ∈ J)
    {x : target.carrier.carrier} (hx : x ∈ U) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun y ↦ (e.toFun (t, y)).2) x) := by
  let f := fun y ↦ (e.toFun (t, y)).2
  let g := fun y ↦ (e.inverse (t, y)).2
  have hpair (y : target.carrier.carrier) : e.toFun (t, y) = (t, f y) :=
    Prod.ext (e.time_preserving t y) rfl
  have hmaps : MapsTo (fun y : source.carrier.carrier ↦ (t, y))
      (f '' U) (e.toFun '' (J ×ˢ U)) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(t, y), ⟨ht, hy⟩, hpair y⟩
  have hinv : ContMDiffWithinAt (𝓡 3) (𝓡 3) ∞ g (f '' U) (f x) := by
    have hs := e.smooth_inverse_on.comp
      (contMDiff_const.prodMk contMDiff_id).contMDiffOn hmaps
    exact (hs (f x) (mem_image_of_mem f hx)).snd
  have hleft : EqOn (g ∘ f) id U := by
    intro y hy
    have h := congrArg Prod.snd (e.left_inverse (t, y) ⟨ht, hy⟩)
    simpa only [hpair, Function.comp_apply, id_eq, g] using h
  have hf : MDifferentiableAt (𝓡 3) (𝓡 3) f x :=
    (e.spatial_contMDiffAt hU ht hx).mdifferentiableAt (by simp)
  have hu := hU.uniqueMDiffWithinAt (I := 𝓡 3) hx
  have hcomp := mfderivWithin_comp x (hinv.mdifferentiableWithinAt (by simp))
    hf.mdifferentiableWithinAt (fun y hy ↦ mem_image_of_mem f hy) hu
  rw [mfderivWithin_congr_of_mem hleft hx, mfderivWithin_id hu,
    mfderivWithin_eq_mfderiv hu hf] at hcomp
  intro v w hvw
  have h := congrArg (mfderivWithin (𝓡 3) (𝓡 3) g (f '' U) (f x)) hvw
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← hcomp] at h
  exact h

theorem spatial_isOpen_image
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) (J ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : t ∈ J) :
    IsOpen ((fun y ↦ (e.toFun (t, y)).2) '' U) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hi := e.spatial_mfderiv_injective hU ht hx
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 3) x) =
      Module.finrank ℝ (TangentSpace (𝓡 3) (e.toFun (t, x)).2) := rfl
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.finiteDimensional_of_finite
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (e.toFun (t, x)).2) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.finiteDimensional_of_finite
  have hbij : Function.Bijective
      (mfderiv (𝓡 3) (𝓡 3) (fun y ↦ (e.toFun (t, y)).2) x) :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hi⟩
  rw [← Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective
    (e.spatial_contMDiffAt hU ht hx) hbij]
  exact image_mem_map (hU.mem_nhds hx)

theorem spatial_surjective_of_compact
    (e : NormalizedKappaSpacetimeEmbedding (source := source) (target := target) (J ×ˢ U))
    (hU : U = univ) (hcompact : IsCompact (univ : Set target.carrier.carrier))
    {t : ℝ} (ht : t ∈ J) :
    Function.Surjective (fun y ↦ (e.toFun (t, y)).2) := by
  let f := fun y ↦ (e.toFun (t, y)).2
  have hopen : IsOpen (range f) := by
    simpa only [hU, image_univ] using e.spatial_isOpen_image (hU ▸ isOpen_univ) ht
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun x ↦
    (e.spatial_contMDiffAt (hU ▸ isOpen_univ) ht (hU ▸ mem_univ x)).continuousAt
  have hclosed : IsClosed (range f) := by
    simpa only [image_univ] using (hcompact.image hcont).isClosed
  have hfull : range f = univ :=
    (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨f target.base, mem_range_self target.base⟩)
  exact range_eq_univ.mp hfull

end NormalizedKappaSpacetimeEmbedding

namespace M23InteriorConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}

theorem eventually_exhaustion_eq_univ (G : M23InteriorConvergence S)
    (hcompact : IsCompact (univ : Set G.limit.carrier.carrier)) :
    ∀ᶠ k in atTop, G.exhaustion k = univ := by
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [eventually_ge_atTop j] with k hk
  exact univ_subset_iff.mp (hj.trans (hmono hk))

end M23InteriorConvergence

end PoincareConjecture
