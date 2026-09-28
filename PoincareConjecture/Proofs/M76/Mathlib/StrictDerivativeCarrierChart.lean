import PoincareConjecture.Proofs.M76.Mathlib.BoundedInverseChart
import PoincareConjecture.Proofs.M76.Mathlib.ProjectionPerturbation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.OpenPartialHomeomorph.Composition










set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace HasStrictFDerivAt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]





theorem exists_carrier_openPartialHomeomorph {C : Set E} {a : C}
    {f : E → F} {Q : E →L[𝕜] F} (hf : HasStrictFDerivAt f Q (a : E))
    {S : Set C} (hS : S ∈ 𝓝 a) {K : ℝ≥0}
    (hbound : ∀ x ∈ S, ∀ y ∈ S, ‖(x : E) - (y : E)‖ ≤ K * ‖Q x - Q y‖)
    (himage : Q a ∈ interior ((fun x : C => Q x) '' S))
    {V : Set C} (hV : V ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph C F, a ∈ e.source ∧ e.source ⊆ S ∩ V ∧
      ∀ x ∈ e.source, e x = f x := by
  let : Nonempty C := ⟨a⟩
  let c : ℝ≥0 := (2 * (K + 1))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : c * K < 1 := by
    change (2 * (K + 1))⁻¹ * K < 1
    rw [inv_mul_eq_div, div_lt_one (by positivity)]
    calc
      K < K + 1 := lt_add_one K
      _ ≤ (K + 1) + (K + 1) := le_add_of_nonneg_right zero_le
      _ = 2 * (K + 1) := by ring
  obtain ⟨W, hW, happ⟩ := hf.approximates_deriv_on_nhds (Or.inr hc)
  have hWpre : (Subtype.val ⁻¹' W : Set C) ∈ 𝓝 a :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hW
  have hQcont : Continuous (fun x : C => Q x) := Q.continuous.comp continuous_subtype_val
  have hdist : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ K * dist (Q x) (Q y) := by
    intro x hx y hy
    simpa only [Subtype.dist_eq, dist_eq_norm] using hbound x hx y hy
  obtain ⟨e, he, ha, hesub⟩ := hQcont.exists_openPartialHomeomorph_of_inverse_bound
    hS hdist himage (inter_mem hV hWpre)
  let g : F → E := fun y => (e.symm y : E)
  have hgW : MapsTo g e.target W := fun y hy => (hesub (e.map_target hy)).2.2
  have hQg : ∀ y ∈ e.target, Q (g y) = y := by
    intro y hy
    simpa only [he] using e.right_inv hy
  have hgbound : ∀ x ∈ e.target, ∀ y ∈ e.target, ‖g x - g y‖ ≤ K * ‖x - y‖ := by
    intro x hx y hy
    have h := hbound (e.symm x) (hesub (e.map_target hx)).1
      (e.symm y) (hesub (e.map_target hy)).1
    change ‖g x - g y‖ ≤ K * ‖Q (g x) - Q (g y)‖ at h
    rwa [hQg x hx, hQg y hy] at h
  have happId := happ.comp_inverse_projection g hgW hQg hgbound
  let A := ContinuousLinearEquiv.refl 𝕜 F
  have hnorm : Subsingleton F ∨ c * K < ‖(A.symm : F →L[𝕜] F)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial F with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [A] using hsmall)
  let d := happId.toOpenPartialHomeomorph (f' := A) (f ∘ g) e.target hnorm e.open_target
  refine ⟨e.trans d, ⟨ha, e.map_source ha⟩, ?_, ?_⟩
  · intro x hx
    exact ⟨(hesub hx.1).1, (hesub hx.1).2.1⟩
  · intro x hx
    change f (e.symm (e x) : E) = f (x : E)
    rw [e.left_inv hx.1]

end HasStrictFDerivAt
