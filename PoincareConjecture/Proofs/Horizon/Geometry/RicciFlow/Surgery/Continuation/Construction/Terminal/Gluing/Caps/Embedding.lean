import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Inclusions

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

def capEmbedding (i : ι) :
    OpenPartialHomeomorph (R i).output.carrier (cutCarrier I R U hU hd hc).carrier := by
  letI : Nonempty (R i).output.carrier := ⟨(R i).tip⟩
  exact (capInclusion_openEmbedding I R U hU hd hc i).toOpenPartialHomeomorph _

@[simp] theorem capEmbedding_apply (i : ι) (x : (R i).output.carrier) :
    capEmbedding I R U hU hd hc i x = capInclusion I R U hU hd hc i x := rfl

@[simp] theorem capEmbedding_source (i : ι) :
    (capEmbedding I R U hU hd hc i).source = univ := rfl

@[simp] theorem capEmbedding_target (i : ι) :
    (capEmbedding I R U hU hd hc i).target =
      range (capInclusion I R U hU hd hc i) := by
  simp [capEmbedding]

theorem capEmbedding_symm_smooth (i : ι) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (capEmbedding I R U hU hd hc i).symm
      (capEmbedding I R U hU hd hc i).target := by
  intro y hy
  rw [capEmbedding_target] at hy
  obtain ⟨x, rfl⟩ := hy
  let h := capInclusion_localDiffeomorph I R U hU hd hc i x
  apply (h.localInverse_contMDiffAt.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [h.localInverse.open_source.mem_nhds h.localInverse_mem_source] with z hz
  have heq := h.localInverse_right_inv hz
  have hs : h.localInverse z ∈ (capEmbedding I R U hU hd hc i).source := mem_univ _
  have hinv := (capEmbedding I R U hU hd hc i).left_inv hs
  change (capEmbedding I R U hU hd hc i).symm
    (capInclusion I R U hU hd hc i (h.localInverse z)) = h.localInverse z at hinv
  rwa [heq] at hinv

theorem capEmbedding_differentiable (i : ι) :
    (capEmbedding I R U hU hd hc i).MDifferentiable (𝓡 3) (𝓡 3) := by
  refine ⟨?_, (capEmbedding_symm_smooth I R U hU hd hc i).mdifferentiableOn (by simp)⟩
  exact (capInclusion_localDiffeomorph I R U hU hd hc i).contMDiff.mdifferentiable
    (by simp) |>.mdifferentiableOn

theorem capEmbedding_symm_metric (i : ι)
    {y : (cutCarrier I R U hU hd hc).carrier}
    (hy : y ∈ (capEmbedding I R U hU hd hc i).target)
    (v w : TangentSpace (𝓡 3) y) :
    (R i).metric.inner ((capEmbedding I R U hU hd hc i).symm y)
      (mfderiv (𝓡 3) (𝓡 3) (capEmbedding I R U hU hd hc i).symm y v)
      (mfderiv (𝓡 3) (𝓡 3) (capEmbedding I R U hU hd hc i).symm y w) =
        (cutMetric I R U hU hd hc).inner y v w := by
  let e := capEmbedding I R U hU hd hc i
  have hv := congrArg (fun A => A v)
    ((capEmbedding_differentiable I R U hU hd hc i).comp_symm_deriv hy)
  have hw := congrArg (fun A => A w)
    ((capEmbedding_differentiable I R U hU hd hc i).comp_symm_deriv hy)
  change mfderiv (𝓡 3) (𝓡 3) e (e.symm y)
    (mfderiv (𝓡 3) (𝓡 3) e.symm y v) = v at hv
  change mfderiv (𝓡 3) (𝓡 3) e (e.symm y)
    (mfderiv (𝓡 3) (𝓡 3) e.symm y w) = w at hw
  have hm := capInclusion_metric I R U hU hd hc i (e.symm y)
    (mfderiv (𝓡 3) (𝓡 3) e.symm y v) (mfderiv (𝓡 3) (𝓡 3) e.symm y w)
  change (cutMetric I R U hU hd hc).inner (e (e.symm y))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v))
    (mfderiv (𝓡 3) (𝓡 3) e (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y w)) = _ at hm
  erw [e.right_inv hy, hv, hw] at hm
  exact hm.symm

end PoincareConjecture.Surgery.Terminal.Gluing
