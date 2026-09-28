import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.ClosedGraph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.MetricSurgeryResult

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {g : RiemannianMetric 3 M} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} {I : MetricSurgeryInput K g}
  (R : MetricSurgeryResult g₀ I)

def negativeOverlap : OpenPartialHomeomorph M R.output.carrier where
  toFun := R.collapse
  invFun := R.retained_inverse
  source := I.negativeHalf
  target := R.collapse '' (I.negativeHalf : Set M)
  map_source' _ hx := mem_image_of_mem _ hx
  map_target' y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    simpa only [R.retained_left_inverse (I.negativeHalf_subset_retainedCollar hx)] using hx
  left_inv' x hx := R.retained_left_inverse (I.negativeHalf_subset_retainedCollar hx)
  right_inv' y hy := R.retained_right_inverse (image_subset_range _ _ hy)
  open_source := I.negativeHalf.isOpen
  open_target := R.retained_image_isOpen I.negativeHalf I.negativeHalf_subset_retainedCollar
  continuousOn_toFun :=
    (R.retained_smooth.mono I.negativeHalf_subset_retainedCollar).continuousOn
  continuousOn_invFun := (R.retained_inverse_smooth.mono
    (image_mono I.negativeHalf_subset_retainedCollar)).continuousOn

def collarOverlap (U : Opens M) (hU : Nonempty U) :
    OpenPartialHomeomorph U R.output.carrier := R.negativeOverlap.subtypeRestr hU

@[simp] theorem collarOverlap_apply (U : Opens M) (hU : Nonempty U) (x : U) :
    R.collarOverlap U hU x = R.collapse x.val := rfl

theorem collarOverlap_source (U : Opens M) (hU : Nonempty U) :
    (R.collarOverlap U hU).source = {x : U | x.val ∈ I.negativeHalf} := by
  exact OpenPartialHomeomorph.subtypeRestr_source _ _

theorem collarOverlap_smooth (U : Opens M) (hU : Nonempty U) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (R.collarOverlap U hU)
      (R.collarOverlap U hU).source := by
  intro x hx
  rw [R.collarOverlap_source] at hx
  have hxc := I.negativeHalf_subset_retainedCollar hx
  exact (((R.retained_smooth x.val hxc).contMDiffAt
    (I.retainedCollar.isOpen.mem_nhds hxc)).comp x
      contMDiff_subtype_val.contMDiffAt).contMDiffWithinAt

theorem collarOverlap_inverse_smooth (U : Opens M) (hU : Nonempty U) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (R.collarOverlap U hU).symm
      (R.collarOverlap U hU).target := by
  have ht : (R.collarOverlap U hU).target ⊆
      R.collapse '' (I.retainedCollar : Set M) :=
    (R.negativeOverlap.subtypeRestr_target_subset hU).trans
      (image_mono I.negativeHalf_subset_retainedCollar)
  have hs : ContMDiffOn (𝓡 3) (𝓡 3) ∞
      (Subtype.val ∘ (R.collarOverlap U hU).symm) (R.collarOverlap U hU).target :=
    (R.retained_inverse_smooth.mono ht).congr (fun y hy =>
      R.negativeOverlap.subtypeRestr_symm_apply hU hy)
  intro y hy
  exact (ContMDiffWithinAt.subtypeVal_comp_iff U _ _ _).mp (hs y hy)

theorem collarOverlap_closed_graph (U : Opens M) (hU : Nonempty U)
    (hcentral : Disjoint (U : Set M) I.neck.central_sphere) :
    IsClosed {p : U × R.output.carrier |
      p.1 ∈ (R.collarOverlap U hU).source ∧ R.collarOverlap U hU p.1 = p.2} := by
  simpa only [R.collarOverlap_source, mem_ofPred_eq, R.collarOverlap_apply] using
    R.isClosed_negative_graph U hcentral

theorem collarOverlap_metric (U : Opens M) (hU : Nonempty U)
    (x : U) (hx : x ∈ (R.collarOverlap U hU).source)
    (v w : TangentSpace (𝓡 3) x) :
    R.metric.inner (R.collarOverlap U hU x)
      (mfderiv (𝓡 3) (𝓡 3) (R.collarOverlap U hU) x v)
      (mfderiv (𝓡 3) (𝓡 3) (R.collarOverlap U hU) x w) =
        (I.sourceCarrier.openSubsetMetric U g).inner x v w := by
  rw [R.collarOverlap_source] at hx
  have hd (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (R.collarOverlap U hU) x z =
        mfderiv (𝓡 3) (𝓡 3) R.collapse x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x z) :=
    mfderiv_comp_apply x
      (((R.retained_smooth x (I.negativeHalf_subset_retainedCollar hx)).contMDiffAt
        (I.retainedCollar.isOpen.mem_nhds
          (I.negativeHalf_subset_retainedCollar hx))).mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) x) z
  rw [hd v, hd w]
  exact R.retained_metric x (Or.inl hx) _ _

end PoincareConjecture.MetricSurgeryResult
