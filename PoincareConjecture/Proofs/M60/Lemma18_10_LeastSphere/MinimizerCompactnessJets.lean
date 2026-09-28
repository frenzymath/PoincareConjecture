import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerMaxGradient
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.UniformSpace.CompleteSeparated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace PoincareConjecture.M60

theorem suC1_compactOpen_subsequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : ℕ → LoopPlane → E) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hequi : Equicontinuous (fun j z => (f j z, fderiv ℝ (f j) z)))
    (hbound : ∀ z, ∃ C : ℝ, ∀ j, ‖(f j z, fderiv ℝ (f j) z)‖ ≤ C) :
    ∃ (u : LoopPlane → E) (k : ℕ → ℕ), ContDiff ℝ 1 u ∧ StrictMono k ∧
      TendstoLocallyUniformly (fun j => f (k j)) u atTop ∧
    TendstoLocallyUniformly (fun j => fderiv ℝ (f (k j))) (fderiv ℝ u) atTop := by
  let : T2Space (UniformOnFun LoopPlane (E × (LoopPlane →L[ℝ] E))
      {K | IsCompact K}) := UniformOnFun.t2Space_of_covering (by
    apply eq_univ_iff_forall.mpr
    intro z
    exact mem_sUnion.mpr ⟨{z}, isCompact_singleton, mem_singleton z⟩)
  let J : ℕ → C(LoopPlane, E × (LoopPlane →L[ℝ] E)) := fun j =>
    ⟨fun z => (f j z, fderiv ℝ (f j) z),
      (hf j).continuous.prodMk ((hf j).continuous_fderiv (by norm_num))⟩
  have hequi' : Equicontinuous (fun v : range J => (v.1 : LoopPlane → _)) := by
    have hJ : (fun v : range J => (fun z => J v.2.choose z)) =
        (fun v : range J => (v.1 : LoopPlane → _)) := by
      funext v z
      exact congrArg (fun w : C(LoopPlane, E × (LoopPlane →L[ℝ] E)) => w z)
        v.2.choose_spec
    rw [← hJ]
    exact hequi.comp fun v : range J => v.2.choose
  have hc : IsCompact (closure (range J)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := ContinuousMap.toFun) (fun _ h => h)
      ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
      (fun K _ => hequi'.equicontinuousOn K) (by
        intro K _ z _
        obtain ⟨C, hC⟩ := hbound z
        refine ⟨Metric.closedBall 0 C, isCompact_closedBall _ _, ?_⟩
        rintro _ ⟨j, rfl⟩
        simpa only [mem_closedBall_zero_iff, J, ContinuousMap.coe_mk] using hC j)
  obtain ⟨v, _, k, hk, hlim⟩ := hc.tendsto_subseq
    (fun j => subset_closure (mem_range_self j))
  have ht := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
  let u : LoopPlane → E := fun z => (v z).1
  let V : LoopPlane → LoopPlane →L[ℝ] E := fun z => (v z).2
  have hu : TendstoLocallyUniformly (fun j => f (k j)) u atTop :=
    uniformContinuous_fst.comp_tendstoLocallyUniformly ht
  have hV : TendstoLocallyUniformly (fun j => fderiv ℝ (f (k j))) V atTop :=
    uniformContinuous_snd.comp_tendstoLocallyUniformly ht
  have hdu (z) : HasFDerivAt u (V z) z :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      (tendstoLocallyUniformlyOn_univ.mpr hV)
      (fun j x _ => ((hf (k j)).differentiable_one x).hasFDerivAt)
      (fun x _ => hu.tendstoLocallyUniformlyOn.tendsto_at (mem_univ x)) (mem_univ z)
  have hVu : V = fderiv ℝ u := funext fun z => (hdu z).fderiv.symm
  refine ⟨u, k, contDiff_one_iff_hasFDerivAt.mpr
    ⟨V, continuous_snd.comp v.continuous, hdu⟩, hk, hu, ?_⟩
  rwa [← hVu]

end PoincareConjecture.M60
