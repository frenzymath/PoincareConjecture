import PoincareConjecture.Proofs.M47.TerminalSourcePhysicalComponent
import PoincareConjecture.Proofs.M47.TerminalGermsOpenCharts










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace E M] [ChartedSpace E N]
  [IsManifold (𝓡 3) ∞ N] [T3Space N]


def terminalSourceComponentMap (g : RiemannianMetric 3 N) (p : N)
    (f : M → N) {B : ℝ} (hball : ∀ x, f x ∈ g.ball p B) :
    M → Poincare.connectedComponentOpens E p :=
  fun x => ⟨f x, RiemannianMetric.mem_of_edist_lt_top
    (U := Poincare.connectedComponentOpens E p) isClosed_connectedComponent g
    mem_connectedComponent ((hball x).trans_le le_top)⟩

omit [T3Space N] in


theorem terminalSourceComponentMap_geometry
    (g : RiemannianMetric 3 N) (p : N) (f : M → N) {B : ℝ}
    (hball : ∀ x, f x ∈ g.ball p B) (hopen : Topology.IsOpenEmbedding f)
    (hsmooth : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f) :
    Topology.IsOpenEmbedding (terminalSourceComponentMap g p f hball) ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (terminalSourceComponentMap g p f hball) := by
  let C := Poincare.connectedComponentOpens E p
  refine ⟨?_, ?_⟩
  · exact Topology.IsOpenEmbedding.of_comp _ C.isOpen.isOpenEmbedding_subtypeVal hopen
  · exact terminalGerms_open_codomain_localDiffeomorph C hsmooth

omit [T3Space N] in


theorem terminalSourceComponentMap_metric
    (g : RiemannianMetric 3 N) (p : N) (f : M → N) {B : ℝ}
    (hball : ∀ x, f x ∈ g.ball p B)
    (hsmooth : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ f)
    (x : M) (v w : TangentSpace (𝓡 3) x) :
    let fC := terminalSourceComponentMap g p f hball
    (g.connectedComponentMetric p).inner (fC x)
      (mfderiv (𝓡 3) (𝓡 3) fC x v) (mfderiv (𝓡 3) (𝓡 3) fC x w) =
      g.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) := by
  let C := Poincare.connectedComponentOpens E p
  let fC := terminalSourceComponentMap g p f hball
  have hfC : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ fC :=
    terminalGerms_open_codomain_localDiffeomorph C hsmooth
  have hchain := mfderiv_comp x
    ((Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3) C).mdifferentiable (by simp) (fC x))
    (hfC.mdifferentiable (by simp) x)
  change mfderiv (𝓡 3) (𝓡 3) f x =
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : C → N) (fC x)).comp
      (mfderiv (𝓡 3) (𝓡 3) fC x) at hchain
  change g.inner (f x)
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : C → N) (fC x)
      (mfderiv (𝓡 3) (𝓡 3) fC x v))
    (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : C → N) (fC x)
      (mfderiv (𝓡 3) (𝓡 3) fC x w)) = _
  exact congrArg₂ (fun a b : E => g.inner (f x) a b)
    (congrArg (fun A => A v) hchain).symm (congrArg (fun A => A w) hchain).symm

omit [TopologicalSpace M] [ChartedSpace E M] in


theorem terminalSourceComponentMap_distances
    (g : RiemannianMetric 3 N) (p : N) (f : M → N) {B : ℝ}
    (hball : ∀ x, f x ∈ g.ball p B) :
    letI := terminalSourceComponentMetricSpace g p
    ∀ x y, edist (terminalSourceComponentMap g p f hball x)
        (terminalSourceComponentMap g p f hball y) = g.edist (f x) (f y) ∧
      dist (terminalSourceComponentMap g p f hball x)
        (terminalSourceComponentMap g p f hball y) = (g.edist (f x) (f y)).toReal := by
  let : MetricSpace (Poincare.connectedComponentOpens E p) := terminalSourceComponentMetricSpace g p
  intro x y
  exact terminalSourceComponent_distances g p _ _

end PoincareConjecture.M47
