import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CompactFirstContact
import Mathlib.Topology.Algebra.Group.Quotient












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open scoped ContDiff

namespace PoincareConjecture




theorem m64Intrinsic_periodic_normal_map_on_cylinder
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u) {P : ℝ}
    (hperiod : ∀ t, Function.Periodic (fun a => u (a, t)) P) :
    ∃ U : AddCircle P × ℝ → AnnulusCoordinates, Continuous U ∧
      (∀ a t : ℝ, U ((a : AddCircle P), t) = u (a, t)) ∧
      ∀ a t : ℝ, Function.Injective (fderiv ℝ u (a, t)) →
        ∃ W ∈ 𝓝 ((a : AddCircle P), t), InjOn U W := by
  let Q : ℝ × ℝ → AddCircle P × ℝ := Prod.map (fun a => (a : AddCircle P)) id
  have hQ : IsOpenQuotientMap Q :=
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples P)).prodMap
      IsOpenQuotientMap.id
  let U : AddCircle P × ℝ → AnnulusCoordinates := fun z => (hperiod z.2).lift z.1
  have heq (z : ℝ × ℝ) : U (Q z) = u z := rfl
  have hU : Continuous U := hQ.continuous_comp_iff.mp (by
    simpa only [Function.comp_def, heq] using hu.continuous)
  refine ⟨U, hU, fun _ _ => rfl, ?_⟩
  intro a t hi
  have hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ AnnulusCoordinates := by simp
  let A := ((fderiv ℝ u (a, t)).toLinearMap.linearEquivOfInjective hi hdim).toContinuousLinearEquiv
  have hd : HasFDerivAt u A.toContinuousLinearMap (a, t) :=
    (hu.differentiable (by simp) (a, t)).hasFDerivAt
  let F := hu.contDiffAt.toOpenPartialHomeomorph u hd (by simp)
  have hsource : (a, t) ∈ F.source :=
    hu.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨Q '' F.source, (hQ.isOpenMap _ F.open_source).mem_nhds ⟨(a, t), hsource, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  apply congrArg Q
  apply F.injOn hx hy
  exact hxy

end PoincareConjecture
