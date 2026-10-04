import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousOn
import Mathlib.Logic.Equiv.Basic

/-!+# Identity extension from a vanishing displacement bound

A self-homeomorphism of an open set extends by the identity if
its forward and inverse displacements are bounded by a continuous
function vanishing outside the set. This isolates the boundary
continuity argument in Hamilton 1976, pp. 65, 67--68. See M76
derivation 81.
-/

set_option autoImplicit false

open Set Topology

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] {U : Set E}

/-- A continuous displacement bound vanishing outside an open
set makes the identity extension continuous. See Hamilton
pp. 65, 67--68 and M76 derivation 81. -/
theorem continuous_extendDomain_of_vanishing_bound (e : U ≃ₜ U) (hU : IsOpen U)
    {b : E → ℝ} (hb : Continuous b) (hbzero : EqOn b (fun _ => 0) Uᶜ)
    (hbound : ∀ x : U, ‖(e x : E) - x‖ ≤ b x) :
    letI := Classical.propDecidable
    Continuous (Equiv.Perm.extendDomain e.toEquiv (Equiv.refl U) : E → E) := by
  classical
  let f : E → E := Equiv.Perm.extendDomain e.toEquiv (Equiv.refl U)
  have hfU : ContinuousOn f U := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_subtype_val.comp e.continuous using 1
    ext x
    exact Equiv.Perm.extendDomain_apply_subtype e.toEquiv (Equiv.refl U) x.property
  have hglobal (x : E) : ‖f x - x‖ ≤ b x := by
    by_cases hx : x ∈ U
    · rw [show f x = (e ⟨x, hx⟩ : E) from
        Equiv.Perm.extendDomain_apply_subtype e.toEquiv (Equiv.refl U) hx]
      exact hbound ⟨x, hx⟩
    · have hfix : f x = x :=
        Equiv.Perm.extendDomain_apply_not_subtype e.toEquiv (Equiv.refl U) hx
      simp only [hfix, sub_self, norm_zero, hbzero hx, le_refl]
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ U
  · exact hfU.continuousAt (hU.mem_nhds hx)
  · have hfix : f x = x :=
      Equiv.Perm.extendDomain_apply_not_subtype e.toEquiv (Equiv.refl U) hx
    have hb0 : Filter.Tendsto b (𝓝 x) (𝓝 0) := by
      simpa only [hbzero hx] using hb.continuousAt.tendsto (x := x)
    have hdelta : Filter.Tendsto (fun y => f y - y) (𝓝 x) (𝓝 0) :=
      squeeze_zero_norm hglobal hb0
    change Filter.Tendsto f (𝓝 x) (𝓝 (f x))
    rw [hfix]
    simpa only [id_eq, sub_add_cancel, zero_add] using hdelta.add continuous_id.continuousAt

/-- Extend an open-set homeomorphism by the identity when a
continuous bound for both displacements vanishes at its exterior.
See Hamilton pp. 65, 67--68 and M76 derivation 81. -/
noncomputable def extendByVanishingBound (e : U ≃ₜ U) (hU : IsOpen U)
    {b : E → ℝ} (hb : Continuous b) (hbzero : EqOn b (fun _ => 0) Uᶜ)
    (hbound : ∀ x : U, ‖(e x : E) - x‖ ≤ b x)
    (hinvbound : ∀ x : U, ‖(e.symm x : E) - x‖ ≤ b x) : E ≃ₜ E := by
  classical
  exact
    { toEquiv := Equiv.Perm.extendDomain e.toEquiv (Equiv.refl U)
      continuous_toFun := e.continuous_extendDomain_of_vanishing_bound hU hb hbzero hbound
      continuous_invFun :=
        e.symm.continuous_extendDomain_of_vanishing_bound hU hb hbzero hinvbound }

/-- The extension retains the original homeomorphism on its
open domain. See Hamilton p. 68 and M76 derivation 81. -/
theorem extendByVanishingBound_apply_mem (e : U ≃ₜ U) (hU : IsOpen U)
    {b : E → ℝ} (hb : Continuous b) (hbzero : EqOn b (fun _ => 0) Uᶜ)
    (hbound : ∀ x : U, ‖(e x : E) - x‖ ≤ b x)
    (hinvbound : ∀ x : U, ‖(e.symm x : E) - x‖ ≤ b x)
    {x : E} (hx : x ∈ U) :
    e.extendByVanishingBound hU hb hbzero hbound hinvbound x = (e ⟨x, hx⟩ : E) := by
  classical
  exact Equiv.Perm.extendDomain_apply_subtype e.toEquiv (Equiv.refl U) hx

/-- The extension fixes every point outside the open domain,
including its boundary. See Hamilton p. 68 and M76 derivation 81. -/
theorem extendByVanishingBound_apply_notMem (e : U ≃ₜ U) (hU : IsOpen U)
    {b : E → ℝ} (hb : Continuous b) (hbzero : EqOn b (fun _ => 0) Uᶜ)
    (hbound : ∀ x : U, ‖(e x : E) - x‖ ≤ b x)
    (hinvbound : ∀ x : U, ‖(e.symm x : E) - x‖ ≤ b x)
    {x : E} (hx : x ∉ U) :
    e.extendByVanishingBound hU hb hbzero hbound hinvbound x = x := by
  classical
  exact Equiv.Perm.extendDomain_apply_not_subtype e.toEquiv (Equiv.refl U) hx

end Homeomorph
