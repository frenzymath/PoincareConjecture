import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.UnitInterval

/-!
# Propagating local kernel-leaf constancy along segments

A continuous operator field locally constant along its own kernel
planes is constant along every such segment contained in a convex
domain. This supplies the uniqueness step in matching the ambient
fields of Cairns 1940, pp. 804--806; see M76 derivation 55.
-/

set_option autoImplicit false

open Set Filter unitInterval
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Local constancy on kernel leaves propagates along a segment
inside a convex domain. The field need only be continuous there.
See Cairns Hypotheses III--IV, pp. 804--805 and M76 derivation 55. -/
theorem ContinuousOn.eq_of_sub_mem_ker_of_convex {G : E → E →L[ℝ] F}
    {V : Set E} (hG : ContinuousOn G V) (hV : Convex ℝ V)
    (hleaf : ∀ z ∈ V, ∀ᶠ w in 𝓝 z, w - z ∈ (G z).ker → G w = G z)
    {x y : E} (hx : x ∈ V) (hy : y ∈ V) (hxy : y - x ∈ (G x).ker) :
    G y = G x := by
  let c : I → E := fun t => AffineMap.lineMap x y (t : ℝ)
  have hc : Continuous c := by
    simp only [c, AffineMap.lineMap_apply_module']
    fun_prop
  have hcV (t : I) : c t ∈ V := hV.lineMap_mem hx hy t.property
  have hcont : Continuous (fun t : I => G (c t)) := hG.comp_continuous hc hcV
  let S : Set I := {t | G (c t) = G x}
  have hclosed : IsClosed S := isClosed_eq hcont continuous_const
  have hopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hnear := hc.continuousAt.eventually (hleaf (c t) (hcV t))
    filter_upwards [hnear] with u hu
    change G (c u) = G x
    rw [hu, ht]
    rw [ht]
    have heq : c u - c t = ((u : ℝ) - (t : ℝ)) • (y - x) := by
      simp only [c, AffineMap.lineMap_apply_module', sub_smul]
      abel
    rw [heq]
    exact (G x).ker.smul_mem _ hxy
  have hnonempty : S.Nonempty := ⟨0, by simp [S, c]⟩
  have hall : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hnonempty
  have h1 : (1 : I) ∈ S := hall.symm ▸ mem_univ _
  simpa [S, c] using h1
