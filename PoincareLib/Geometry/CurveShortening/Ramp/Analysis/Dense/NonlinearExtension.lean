import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Nonlinear extension from a dense core

Lipschitz bounds on each bounded part of an actual dense core construct
a continuous map on the whole normed group. Only the target is complete.
MT2007 Claim 19.1, p. 437; `2026-09-21-dense-nonlinear-extension.md`.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace PoincareMT.M63

/-- A map on a dense subset that is Lipschitz on each bounded core ball
has an actual continuous extension to the ambient normed group.
MT2007 Claim 19.1, p. 437; nonlinear dense extension derivation.
The source and its dense subset need not be complete or linear. -/
theorem exists_continuous_extension_of_bounded_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [CompleteSpace F]
    (s : Set E) (hs : Dense s) (f : s → F)
    (hf : ∀ R : ℝ, 0 < R → ∃ K : NNReal,
      LipschitzOnWith K f {u : s | ‖(u : E)‖ ≤ R}) :
    ∃ Ffull : E → F, Continuous Ffull ∧ ∀ u : s, Ffull u = f u := by
  let e : s → E := Subtype.val
  have hd : IsDenseInducing e := hs.isDenseInducing_val
  have hu : IsUniformInducing e := isUniformEmbedding_subtype_val.isUniformInducing
  have hc (x : E) : Cauchy (Filter.map f (Filter.comap e (𝓝 x))) := by
    let : NeBot (Filter.comap e (𝓝 x)) := hd.comap_nhds_neBot x
    have hsource : Cauchy (Filter.comap e (𝓝 x)) :=
      cauchy_nhds.comap hu.comap_uniformity.le
    obtain ⟨K, hK⟩ := hf (‖x‖ + 1) (by positivity)
    have hball : {y : E | ‖y‖ ≤ ‖x‖ + 1} ∈ 𝓝 x :=
      continuous_norm.continuousAt.preimage_mem_nhds (Iic_mem_nhds (by linarith))
    have hle : Filter.comap e (𝓝 x) ≤ 𝓟 {u : s | ‖(u : E)‖ ≤ ‖x‖ + 1} := by
      simpa only [Filter.comap_principal, e, Set.preimage_ofPred_eq] using
        (Filter.comap_mono (m := e) (Filter.le_principal_iff.mpr hball))
    exact hsource.map_of_le hK.uniformContinuousOn hle
  have hlim (x : E) : ∃ y : F, Tendsto f (Filter.comap e (𝓝 x)) (𝓝 y) :=
    CompleteSpace.complete (hc x)
  exact ⟨hd.extend f, hd.continuous_extend_of_cauchy hc, hd.extend_eq' hlim⟩

end PoincareMT.M63
