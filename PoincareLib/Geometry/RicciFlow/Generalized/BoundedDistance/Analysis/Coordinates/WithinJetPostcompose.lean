import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Linear evaluation of converging within jets

Fixed linear readouts preserve actual within-jet convergence. In the
partial parabolic limit this extracts scalar metric coefficients from
the bilinear coefficients without losing included time endpoints;
Morgan--Tian Proposition 5.14, pp. 90-91, task derivation 09.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

/-- Continuous linear postcomposition preserves uniform convergence of
actual within jets, with finite regularity and any index filter
(task derivation 09). -/
theorem TendstoUniformlyOn.iteratedFDerivWithin_postcompose
    {𝕜 E F G α : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {l : Filter α} {S K : Set E} {f : α → E → F} {g : E → F}
    {n : ℕ∞ω} {r : ℕ}
    (hjet : TendstoUniformlyOn
      (fun k => iteratedFDerivWithin 𝕜 r (f k) S)
      (iteratedFDerivWithin 𝕜 r g S) l K)
    (L : F →L[𝕜] G) (hS : UniqueDiffOn 𝕜 S) (hK : K ⊆ S)
    (hf : ∀ᶠ k in l, ContDiffOn 𝕜 n (f k) S)
    (hg : ContDiffOn 𝕜 n g S) (hr : r ≤ n) :
    TendstoUniformlyOn
      (fun k => iteratedFDerivWithin 𝕜 r (L ∘ f k) S)
      (iteratedFDerivWithin 𝕜 r (L ∘ g) S) l K := by
  have h := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin r => E) F G L).uniformContinuous.comp_tendstoUniformlyOn hjet
  apply (h.congr ?_).congr_right ?_
  · filter_upwards [hf] with k hk x hx
    exact (L.iteratedFDerivWithin_comp_left (hk x (hK hx)) hS (hK hx) hr).symm
  · intro x hx
    exact (L.iteratedFDerivWithin_comp_left (hg x (hK hx)) hS (hK hx) hr).symm
