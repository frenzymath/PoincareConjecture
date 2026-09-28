import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open scoped Topology

namespace PoincareConjecture.Proofs.M09

theorem Icc_subset_of_uniform_open_intervals (D : Set ℝ) (hD : IsOpen D)
    (h0 : 0 ∈ D) (S : ℝ) (hS : 0 ≤ S) (r : ℝ) (hr : 0 < r)
    (hstep : ∀ t ∈ Set.Icc 0 S, t ∈ D → Set.Ioo (t - r) (t + r) ⊆ D) :
    Set.Icc 0 S ⊆ D := by
  let E := Set.Icc 0 S
  let : PreconnectedSpace E := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let A : Set E := {t | (t : ℝ) ∈ D}
  have hopen : IsOpen A := hD.preimage continuous_subtype_val
  have hcompl : IsOpen Aᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hN : Set.Ioo ((t : ℝ) - r) ((t : ℝ) + r) ∈ 𝓝 (t : ℝ) :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [continuousAt_subtype_val.preimage_mem_nhds hN] with z hz
    change (z : ℝ) ∉ D
    intro hzD
    apply ht
    exact hstep z z.property hzD ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hAll : A = Set.univ := IsClopen.eq_univ ⟨isOpen_compl_iff.mp hcompl, hopen⟩
    ⟨⟨0, le_rfl, hS⟩, h0⟩
  intro s hs
  have hm : (⟨s, hs⟩ : E) ∈ A := by rw [hAll]; trivial
  exact hm

end PoincareConjecture.Proofs.M09
