import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerCompactnessJets
import Mathlib.Geometry.Manifold.WhitneyEmbedding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped Topology Manifold ContDiff

noncomputable section

universe u

namespace PoincareConjecture.M60

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def SUChartReadable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : M → E) : Prop :=
  ∀ p : M, ∃ b : M, p ∈ (extChartAt (𝓡 n) b).source ∧
    ∃ L : E →L[ℝ] EuclideanSpace ℝ (Fin n),
      (fun q => L (e q)) =ᶠ[𝓝 p] (extChartAt (𝓡 n) b)

theorem suCompactObservation_exists [CompactSpace M] [T2Space M] :
    ∃ (d : ℕ) (e : M → EuclideanSpace ℝ (Fin d)),
      ContMDiff (𝓡 n) (𝓡 d) ∞ e ∧ IsClosedEmbedding e ∧ SUChartReadable (n := n) e := by
  obtain ⟨ι, f, -⟩ := SmoothBumpCovering.exists_isSubordinate
    (𝓡 n) isClosed_univ (fun (x : M) _ => univ_mem)
  let := f.fintype
  let F := ι → EuclideanSpace ℝ (Fin n) × ℝ
  let d := Module.finrank ℝ F
  let A : F ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let w : M → F := fun x i => (f i x • extChartAt (𝓡 n) (f.c i) x, f i x)
  have hw : ContMDiff (𝓡 n) 𝓘(ℝ, F) ∞ w := contMDiff_pi_space.mpr fun i =>
    ((f i).contMDiff_smul contMDiffOn_extChartAt).prodMk_space (f i).contMDiff
  have hwi : Function.Injective w := by
    intro x y hxy
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj (congrFun hxy (f.ind x (mem_univ x)))
    rw [f.apply_ind x (mem_univ x)] at h₂
    rw [← h₂, f.apply_ind x (mem_univ x), one_smul, one_smul] at h₁
    exact (extChartAt (𝓡 n) (f.c _)).injOn
      (f.mem_extChartAt_ind_source x (mem_univ x))
      (f.mem_extChartAt_source_of_eq_one h₂.symm) h₁
  let e := A ∘ w
  have he : ContMDiff (𝓡 n) (𝓡 d) ∞ e :=
    A.toDiffeomorph.contMDiff.comp hw
  have hei : IsClosedEmbedding e := he.continuous.isClosedEmbedding
    (A.injective.comp hwi)
  refine ⟨d, e, he, hei, fun p => ?_⟩
  let i := f.ind p (mem_univ p)
  let L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ).comp
      (ContinuousLinearMap.proj i)).comp A.symm.toContinuousLinearMap
  refine ⟨f.c i, f.mem_extChartAt_ind_source p (mem_univ p), L, ?_⟩
  filter_upwards [f.eventuallyEq_one p (mem_univ p)] with q hq
  simp only [L, e, Function.comp_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe, A.symm_apply_apply, ContinuousLinearMap.coe_fst', w]
  change f i q • (extChartAt (𝓡 n) (f.c i)) q = _
  rw [show f i q = 1 from hq, one_smul]

theorem suChartReadable_contMDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e : M → E} (he : SUChartReadable (n := n) e) {f : LoopPlane → M}
    (hf : Continuous f) (hc : ContDiff ℝ 1 (e ∘ f)) :
    ContMDiff (𝓡 2) (𝓡 n) 1 f := by
  intro z
  obtain ⟨b, hb, L, hL⟩ := he (f z)
  let c := extChartAt (𝓡 n) b
  have hLz : L (e (f z)) = c (f z) := hL.self_of_nhds
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) 1 c.symm (L (e (f z))) := by
    rw [hLz]
    exact ((contMDiffOn_extChartAt_symm (n := ∞) b _ (c.map_source hb)).contMDiffAt
      ((isOpen_extChartAt_target b).mem_nhds (c.map_source hb))).of_le (by simp)
  have hj : ContMDiffAt (𝓡 2) (𝓡 n) 1 (fun x => L (e (f x))) z :=
    (L.contDiff.comp hc).contMDiff.contMDiffAt
  apply (hi.comp z hj).congr_of_eventuallyEq
  filter_upwards [hL.comp_tendsto hf.continuousAt,
    hf.continuousAt ((isOpen_extChartAt_source b).mem_nhds hb)] with x hx hxs
  change L (e (f x)) = c (f x) at hx
  change f x = c.symm (L (e (f x)))
  rw [hx, c.left_inv hxs]

theorem suTarget_C1_subsequence [CompactSpace M] [T2Space M]
    {d : ℕ} (e : M → EuclideanSpace ℝ (Fin d))
    (he : ContMDiff (𝓡 n) (𝓡 d) ∞ e) (hei : IsClosedEmbedding e)
    (hread : SUChartReadable (n := n) e)
    (f : ℕ → LoopPlane → M) (hf : ∀ j, ContMDiff (𝓡 2) (𝓡 n) ∞ (f j))
    (hequi : Equicontinuous (fun j z => ((e ∘ f j) z, fderiv ℝ (e ∘ f j) z)))
    (hbound : ∀ z, ∃ C : ℝ, ∀ j, ‖((e ∘ f j) z, fderiv ℝ (e ∘ f j) z)‖ ≤ C) :
    ∃ (v : C(LoopPlane, M)) (k : ℕ → ℕ),
      ContMDiff (𝓡 2) (𝓡 n) 1 v ∧ StrictMono k ∧
      Tendsto (fun j => (⟨f (k j), (hf (k j)).continuous⟩ : C(LoopPlane, M)))
        atTop (𝓝 v) ∧
      TendstoLocallyUniformly (fun j => e ∘ f (k j)) (e ∘ v) atTop ∧
      TendstoLocallyUniformly (fun j => fderiv ℝ (e ∘ f (k j)))
        (fderiv ℝ (e ∘ v)) atTop := by
  obtain ⟨u, k, hu, hk, hlim, hderiv⟩ := suC1_compactOpen_subsequence
    (fun j => e ∘ f j)
    (fun j => (contMDiff_iff_contDiff.mp (he.comp (hf j))).of_le (by simp)) hequi hbound
  have hrange (z) : u z ∈ range e := hei.isClosed_range.mem_of_tendsto
    (hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z))
    (Eventually.of_forall fun j => mem_range_self (f (k j) z))
  let v : LoopPlane → M := fun z => hei.isEmbedding.toHomeomorph.symm ⟨u z, hrange z⟩
  have hev : e ∘ v = u := by
    funext z
    exact congrArg Subtype.val (hei.isEmbedding.toHomeomorph.apply_symm_apply ⟨u z, hrange z⟩)
  have hv : Continuous v := hei.isEmbedding.continuous_iff.mpr (hev ▸ hu.continuous)
  have hvc : ContMDiff (𝓡 2) (𝓡 n) 1 v :=
    suChartReadable_contMDiff hread hv (hev ▸ hu)
  refine ⟨⟨v, hv⟩, k, hvc, hk, ?_, ?_, ?_⟩
  · apply (ContinuousMap.isEmbedding_postcomp
      (⟨e, he.continuous⟩ : C(M, EuclideanSpace ℝ (Fin d))) hei.isEmbedding).tendsto_nhds_iff.mpr
    apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
    change TendstoLocallyUniformly (fun j => e ∘ f (k j)) (e ∘ v) atTop
    rwa [hev]
  · simpa only [ContinuousMap.coe_mk, hev] using hlim
  · simpa only [ContinuousMap.coe_mk, hev] using hderiv

end PoincareConjecture.M60
