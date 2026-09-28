import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.CoordinateRegularity











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



theorem contDiffWithinAt_family_pullback_inner (F : RicciFlow n M J)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → M} {τ : E → ℝ} {A : Set E} {p : E} (hp : τ p ∈ J)
    (hA : MapsTo τ A J) (hτ : ContDiffAt ℝ ∞ τ p)
    (hf : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ f p) (v w : E) :
    ContDiffWithinAt ℝ ∞ (fun z => (F.metric (τ z)).inner (f z)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) f z v)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) f z w)) A p := by
  have hmap : MapsTo (fun z => (τ z, f z)) A (J ×ˢ (univ : Set M)) :=
    fun z hz => ⟨hA hz, mem_univ _⟩
  have hg := (F.smooth (τ p, f p) ⟨hp, mem_univ _⟩).comp p
    (hτ.contMDiffAt.prodMk hf).contMDiffWithinAt hmap
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf v).contMDiffWithinAt
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf w).contMDiffWithinAt
  have hh := (Bundle.contMDiffWithinAt_totalSpace.mp h).2
  simp only [Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.trivialization_apply] at hh
  convert! contMDiffWithinAt_iff_contDiffWithinAt.mp hh using 1



theorem contDiffOn_clock_spatialPullback_inner (F : RicciFlow n M J)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → M} {U : Set E} (hU : IsOpen U)
    (hφ : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ φ U)
    {τ : ℝ → ℝ} (hτ : ContDiff ℝ ∞ τ) {K : Set ℝ} (hK : MapsTo τ K J)
    (v w : E) :
    ContDiffOn ℝ ∞ (fun z : ℝ × E => (F.metric (τ z.1)).inner (φ z.2)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) φ z.2 v)
      (mfderiv 𝓘(ℝ, E) (𝓡 n) φ z.2 w)) (K ×ˢ U) := by
  let f : ℝ × E → M := fun z => φ z.2
  have hf {z : ℝ × E} (hz : z.2 ∈ U) :
      ContMDiffAt 𝓘(ℝ, ℝ × E) (𝓡 n) ∞ f z :=
    ((hφ z.2 hz).contMDiffAt (hU.mem_nhds hz)).comp z contDiffAt_snd.contMDiffAt
  intro p hp
  apply (F.contDiffWithinAt_family_pullback_inner (τ := fun z : ℝ × E => τ z.1)
    (f := f) (p := p) (hK hp.1)
    (fun _ hz => hK hz.1) (hτ.contDiffAt.comp p contDiffAt_fst)
    (hf hp.2) (0, v) (0, w)).congr_of_eventuallyEq_of_mem ?_ hp
  filter_upwards [Filter.mem_of_superset self_mem_nhdsWithin (fun z hz => hz.2)]
    with z hz
  have ha := RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp)) v
  have hb := RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp)) w
  rw [← ha, ← hb]



theorem contDiffOn_chartMetric (F : RicciFlow n M J) (q : M) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric z.1).inner ((extChartAt (𝓡 n) q).symm z.2)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm z.2
          (EuclideanSpace.basisFun (Fin n) ℝ a))
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm z.2
          (EuclideanSpace.basisFun (Fin n) ℝ b)))
      (J ×ˢ (extChartAt (𝓡 n) q).target) := by
  exact F.contDiffOn_clock_spatialPullback_inner (isOpen_extChartAt_target q)
    (contMDiffOn_extChartAt_symm q) contDiff_id (fun _ hz => hz)
    (EuclideanSpace.basisFun (Fin n) ℝ a) (EuclideanSpace.basisFun (Fin n) ℝ b)

end PoincareConjecture.RicciFlow
