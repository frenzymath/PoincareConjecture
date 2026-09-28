import PoincareConjecture.Proofs.M63.Mathlib.PeriodicDerivativeConvergence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated









set_option autoImplicit false

open Filter
open scoped Topology NNReal

universe u v

namespace PoincareConjecture.M63




theorem exists_periodic_derivative_limit_along_filter
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {A : Type v} (l : Filter A) [l.IsCountablyGenerated] [l.NeBot]
    {P : Real} [Fact (0 < P)]
    (f df : A -> C(AddCircle P, E)) (f0 : C(AddCircle P, E))
    (hder : forall j (x : Real), HasDerivAt
      (fun y : Real => f j (y : AddCircle P)) (df j (x : AddCircle P)) x)
    {L : NNReal} (hlip : forall j, LipschitzWith L
      (fun x : Real => df j (x : AddCircle P)))
    (hlim : Tendsto f l (nhds f0)) :
    Exists fun g : C(AddCircle P, E) => And (Tendsto df l (nhds g))
      (forall x : Real, HasDerivAt (fun y : Real => f0 (y : AddCircle P))
        (g (x : AddCircle P)) x) := by
  obtain ⟨u, hu⟩ := Filter.exists_seq_tendsto l
  obtain ⟨g, _hg, hgf⟩ := exists_periodic_derivative_limit
    (f ∘ u) (df ∘ u) f0 (fun j x => hder (u j) x)
      (fun j => hlip (u j)) (hlim.comp hu)
  refine ⟨g, ?_, hgf⟩
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro w hw
  obtain ⟨g', hg', hgf'⟩ := exists_periodic_derivative_limit
    (f ∘ w) (df ∘ w) f0 (fun j x => hder (w j) x)
      (fun j => hlip (w j)) (hlim.comp hw)
  have heq : g' = g := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact (hgf' x).unique (hgf x)
  simpa only [heq] using hg'

end PoincareConjecture.M63
