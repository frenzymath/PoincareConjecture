import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessClosed
import PoincareConjecture.Proofs.M63.Mathlib.CompactEmbeddedRetraction
import Mathlib.Geometry.Manifold.WhitneyEmbedding

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem c2ShrinkingCurve_unique_closed (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {s T : ℝ} {c d : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Icc s T))
    (hd : M63C2ShrinkingCurveOn F d (Icc s T))
    (hinit : ∀ x, c x s = d x s) :
    ∀ t ∈ Icc s T, ∀ x, c x t = d x t := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Nonempty M := ⟨c 0 s⟩
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  exact c2ShrinkingCurve_unique_closed_of_retraction he hU heU hρ hρe hc hd hinit

theorem c2ShrinkingCurve_unique_half_open (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    {c d : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Ico a T))
    (hd : M63C2ShrinkingCurveOn F d (Ico a T))
    (hinit : ∀ x, c x a = d x a) :
    ∀ t ∈ Ico a T, ∀ x, c x t = d x t := by
  exact unique_half_open_of_unique_closed
    (fun _ _ _ _ _ hc hd hinit => c2ShrinkingCurve_unique_closed F hcompact hc hd hinit)
    haT hTb hc hd hinit

end PoincareConjecture.M63
