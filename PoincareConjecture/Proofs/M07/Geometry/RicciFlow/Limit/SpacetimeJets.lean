import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.CoordinateTime
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SpatialJets
import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set Filter Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem contDiffAt_family_pullback_inner
    {J : Set ℝ} {g : ℝ → RiemannianMetric n M}
    (hg : IsSmoothFamilyOn g J)
    {f : ℝ × EuclideanSpace ℝ (Fin n) → M}
    {p : ℝ × EuclideanSpace ℝ (Fin n)} (hJ : J ∈ 𝓝 p.1)
    (hf : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ f p)
    (v w : ℝ × EuclideanSpace ℝ (Fin n)) :
    ContDiffAt ℝ ∞ (fun z => (g z.1).inner (f z)
      (mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) f z v)
      (mfderiv 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) f z w)) p := by
  have hdom : J ×ˢ (univ : Set M) ∈ 𝓝 (p.1, f p) :=
    prod_mem_nhds hJ Filter.univ_mem
  have hfst : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => z.1) p :=
    contDiffAt_fst.contMDiffAt
  have hmetric := (hg.contMDiffAt hdom).comp p (hfst.prodMk hf)
  have h := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (contMDiffAt_mfderiv_const_vector hf v) (contMDiffAt_mfderiv_const_vector hf w)
  have hh := (Bundle.contMDiffAt_totalSpace.mp h).2
  simp at hh
  convert! contMDiffAt_iff_contDiffAt.mp hh using 1

theorem IsSmoothFamilyOn.contDiffAt_spacetime_chart_coefficient
    {J : Set ℝ} {g : ℝ → RiemannianMetric n M}
    (hg : IsSmoothFamilyOn g J) (hJ : IsOpen J) (q : M)
    {p : ℝ × EuclideanSpace ℝ (Fin n)} (ht : p.1 ∈ J)
    (hp : p.2 ∈ (extChartAt (𝓡 n) q).target) (a b : Fin n) :
    ContDiffAt ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g z.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm z.2
        (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) p := by
  let c := extChartAt (𝓡 n) q
  let f : ℝ × EuclideanSpace ℝ (Fin n) → M := fun z => c.symm z.2
  have hf {z : ℝ × EuclideanSpace ℝ (Fin n)} (hz : z.2 ∈ c.target) :
      ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ f z := by
    have hc := (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q hz).contMDiffAt
      (extChartAt_target_mem_nhds' hz)
    exact hc.comp z contDiffAt_snd.contMDiffAt
  apply (contDiffAt_family_pullback_inner hg (hJ.mem_nhds ht)
    (hf hp) (0, EuclideanSpace.basisFun (Fin n) ℝ a)
      (0, EuclideanSpace.basisFun (Fin n) ℝ b)).congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.preimage_mem_nhds (extChartAt_target_mem_nhds' hp)]
    with z hz
  have ha := mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp))
    (EuclideanSpace.basisFun (Fin n) ℝ a)
  have hb := mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp))
    (EuclideanSpace.basisFun (Fin n) ℝ b)
  rw [← ha, ← hb]
  rfl

private theorem tendsto_spatial_slice_jet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : Type*} {l : Filter α} {fseq : α → ℝ × E → ℝ} {f : ℝ × E → ℝ}
    {t : ℝ} {x : E} (hseq : ∀ k, ContDiffAt ℝ ∞ (fseq k) (t, x))
    (hf : ContDiffAt ℝ ∞ f (t, x)) (r : ℕ)
    (h : Tendsto (fun k => iteratedFDeriv ℝ r (fseq k) (t, x)) l
      (𝓝 (iteratedFDeriv ℝ r f (t, x)))) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y => fseq k (t, y)) x) l
      (𝓝 (iteratedFDeriv ℝ r (fun y => f (t, y)) x)) := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r => ContinuousLinearMap.inr ℝ ℝ E)
  have hs (F : ℝ × E → ℝ) (hF : ContDiffAt ℝ ∞ F (t, x)) :
      iteratedFDeriv ℝ r (fun y => F (t, y)) x = P (iteratedFDeriv ℝ r F (t, x)) := by
    ext v
    exact Poincare.Analysis.iteratedFDeriv_spatial_slice F hF r v
  simpa only [hs _ hf, hs _ (hseq _), Function.comp_def] using
    P.continuous.continuousAt.tendsto.comp h

private theorem deriv_time_slice_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → ℝ} {t : ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f (t, x)) :
    deriv (fun s => f (s, x)) t =
      iteratedFDeriv ℝ 1 f (t, x) (fun _ => (1, 0)) := by
  have hs : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  simpa only [Function.comp_def, iteratedFDeriv_one_apply] using
    ((hf.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hs).deriv

theorem spatial_and_time_jets_of_spacetime_jets
    {α : Type*} {l : Filter α} {J : Set ℝ}
    (gseq : α → ℝ → RiemannianMetric n M) (g : ℝ → RiemannianMetric n M)
    (hseq : ∀ k, IsSmoothFamilyOn (gseq k) J) (hg : IsSmoothFamilyOn g J)
    (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J) (x : M)
    (h : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin n,
      Tendsto (fun k => iteratedFDeriv ℝ r
        (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          (gseq k z.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm z.2
            (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b)) (t, extChartAt (𝓡 n) x x)) l
        (𝓝 (iteratedFDeriv ℝ r
          (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
            (g z.1).pullbackCoefficients (extChartAt (𝓡 n) x).symm z.2
              (EuclideanSpace.basisFun (Fin n) ℝ a)
              (EuclideanSpace.basisFun (Fin n) ℝ b)) (t, extChartAt (𝓡 n) x x)))) :
    (∀ r : ℕ, r ≤ 2 → ∀ a b : Fin n,
      Tendsto (fun k => iteratedFDeriv ℝ r
        (fun y => (gseq k t).pullbackCoefficients (extChartAt (𝓡 n) x).symm y
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) (extChartAt (𝓡 n) x x)) l
        (𝓝 (iteratedFDeriv ℝ r
          (fun y => (g t).pullbackCoefficients (extChartAt (𝓡 n) x).symm y
            (EuclideanSpace.basisFun (Fin n) ℝ a)
            (EuclideanSpace.basisFun (Fin n) ℝ b)) (extChartAt (𝓡 n) x x)))) ∧
    (∀ a b : Fin n,
      Tendsto (fun k => deriv (fun s => (gseq k s).pullbackCoefficients
        (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)
        (EuclideanSpace.basisFun (Fin n) ℝ a)
        (EuclideanSpace.basisFun (Fin n) ℝ b)) t) l
        (𝓝 (deriv (fun s => (g s).pullbackCoefficients
          (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)
          (EuclideanSpace.basisFun (Fin n) ℝ a)
          (EuclideanSpace.basisFun (Fin n) ℝ b)) t))) := by
  have hreg (G : ℝ → RiemannianMetric n M) (hG : IsSmoothFamilyOn G J)
      (a b : Fin n) := hG.contDiffAt_spacetime_chart_coefficient hJ x
        (p := (t, extChartAt (𝓡 n) x x)) ht
        (mem_extChartAt_target x) a b
  constructor
  · intro r hr a b
    exact tendsto_spatial_slice_jet (fun k => hreg (gseq k) (hseq k) a b)
      (hreg g hg a b) r (h r hr a b)
  · intro a b
    have h' := (continuous_eval_const (fun _ : Fin 1 =>
      (1, (0 : EuclideanSpace ℝ (Fin n))))).continuousAt.tendsto.comp (h 1 (by omega) a b)
    simpa only [Function.comp_def, ← deriv_time_slice_eq (hreg g hg a b),
      ← deriv_time_slice_eq (hreg (gseq _) (hseq _) a b)] using h'

theorem tendsto_spacetime_jet_of_compact_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : Type*} {l : Filter α} {fseq : α → E → ℝ} {f : E → ℝ}
    {S : Set E} (r : ℕ)
    (h : ∀ K : Set E, IsCompact K → K ⊆ S →
      TendstoUniformlyOn (fun k y => iteratedFDeriv ℝ r (fseq k) y)
        (fun y => iteratedFDeriv ℝ r f y) l K)
    {p : E} (hp : p ∈ S) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fseq k) p) l
      (𝓝 (iteratedFDeriv ℝ r f p)) :=
  (h {p} isCompact_singleton (singleton_subset_iff.mpr hp)).tendsto_at (mem_singleton p)

end PoincareConjecture.RiemannianMetric
