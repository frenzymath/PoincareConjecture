import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.EndpointPathLimit
import Mathlib.Topology.Order.ExtendFrom
import Mathlib.Topology.UnitInterval



set_option autoImplicit false
open Set Filter
open scoped Topology
namespace PoincareConjecture.M76.PrismBelt

theorem exists_path_of_endpoint_limit
    {X : Type*} [TopologicalSpace X] [T3Space X]
    {γ : ℝ → X} {ε : ℝ} {x : X} (hε : 0 < ε)
    (hγ : ContinuousOn γ (Ioo 0 ε)) (hlim : Tendsto γ (𝓝[>] 0) (𝓝 x)) :
    ∃ ξ : C(unitInterval,X), ξ 0 = x ∧
      ∀ t : unitInterval, 0 < (t : ℝ) → ξ t = γ (ε / 2 * t) := by
  let time (t : unitInterval) : ℝ := ε / 2 * t
  have ht (t : unitInterval) : time t ∈ Ico 0 ε := by
    change 0 ≤ ε / 2 * (t : ℝ) ∧ ε / 2 * (t : ℝ) < ε
    constructor
    · exact mul_nonneg (by linarith) t.property.1
    · nlinarith [t.property.2]
  have hc : Continuous (fun t => extendFrom (Ioo 0 ε) γ (time t)) :=
    (continuousOn_Ico_extendFrom_Ioo hγ hlim).comp_continuous
      (continuous_const.mul continuous_subtype_val) ht
  refine ⟨⟨fun t => extendFrom (Ioo 0 ε) γ (time t),hc⟩,?_,?_⟩
  · change extendFrom (Ioo 0 ε) γ (ε / 2 * 0) = x
    rw [mul_zero]
    exact eq_lim_at_left_extendFrom_Ioo hε hlim
  · intro t hpos
    exact extendFrom_extends hγ _ ⟨mul_pos (by linarith) hpos,(ht t).2⟩

end PoincareConjecture.M76.PrismBelt
