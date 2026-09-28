import PoincareConjecture.Proofs.M76.Mathlib.KernelLeafConstancy
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ContinuousOn.exists_normalizedProjection_leaf_neighborhood
    {Q : E → E →L[ℝ] F} {U : Set E} (hQ : ContinuousOn Q U)
    (hU : IsOpen U) {a : E} (ha : a ∈ U) (J : F →L[ℝ] E)
    (hJ : ∀ y ∈ U, Function.RightInverse J (Q y))
    (hleaf : ∀ y ∈ U, ∀ᶠ z in 𝓝 y, z - y ∈ (Q y).ker → Q z = Q y) :
    ∃ W : Set E, IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, a + J (Q y (y - a)) ∈ U ∧
        Q (a + J (Q y (y - a))) = Q y ∧
        a + J (Q y (y - a)) - y ∈ (Q y).ker := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU a ha
  let f : E → F := fun y => Q y (y - a)
  let b : E → E := fun y => a + J (f y)
  have hf : ContinuousOn f (ball a r) :=
    (hQ.mono hball).clm_apply (continuous_id.sub continuous_const).continuousOn
  have hb : ContinuousOn b (ball a r) :=
    continuousOn_const.add (J.continuous.comp_continuousOn hf)
  let W := ball a r ∩ b ⁻¹' ball a r
  have hW : IsOpen W := hb.isOpen_inter_preimage isOpen_ball isOpen_ball
  have haW : a ∈ W := by
    simp [W, b, f, hr]
  refine ⟨W, hW, haW, fun y hy => hball hy.1, fun y hy => ?_⟩
  have hby : b y ∈ ball a r := hy.2
  have hker : b y - y ∈ (Q y).ker := by
    change Q y (a + J (Q y (y - a)) - y) = 0
    rw [map_sub, map_add, hJ y (hball hy.1), map_sub]
    abel
  refine ⟨hball hby, ?_, hker⟩
  exact (hQ.mono hball).eq_of_sub_mem_ker_of_convex (convex_ball a r)
    (fun z hz => hleaf z (hball hz)) hy.1 hby hker

namespace ContinuousLinearMap

variable [FiniteDimensional ℝ F]

theorem isInvertible_comp_of_ker_eq (Q R : E →L[ℝ] F) (J : F →L[ℝ] E)
    (hker : Q.ker = R.ker) (hJ : Function.RightInverse J R) :
    (Q.comp J).IsInvertible := by
  have hinj : Function.Injective (Q.comp J) := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro z hz
    have hJz : J z ∈ Q.ker := hz
    rw [hker] at hJz
    have hz0 : R (J z) = 0 := hJz
    simpa only [hJ z, Submodule.mem_bot] using hz0
  have hsurj : Function.Surjective (Q.comp J) :=
    LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective (Q.comp J) (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

end ContinuousLinearMap
