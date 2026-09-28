import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.ModelSpaces
import Mathlib.Topology.Connected.Clopen



noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold



theorem surjective_of_compact_of_bijective_mfderiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N]
    [CompactSpace M] [Nonempty M] [ConnectedSpace N] [T2Space N]
    {f : M -> N} (hf : ContMDiff 𝓘(Real, E) 𝓘(Real, F) ∞ f)
    (hbij : ∀ x, Function.Bijective (mfderiv 𝓘(Real, E) 𝓘(Real, F) f x)) :
    Function.Surjective f := by
  have hopen : IsOpenMap f := IsOpenMap.of_nhds_le fun x =>
    (map_nhds_eq_of_contMDiffAt_bijective_mfderiv_modelSpaces (hf x) (hbij x)).ge
  have hclopen : IsClopen (range f) :=
    ⟨(isCompact_range hf.continuous).isClosed, hopen.isOpen_range⟩
  exact range_eq_univ.mp (hclopen.eq_univ (range_nonempty f))

end Poincare.Geometry.Manifold
