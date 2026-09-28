import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.AdaptedChart
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.Compact

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace Poincare.Geometry.Manifold

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem mfderiv_eq_zero_of_isLocalMin
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {x : M}
    (hmin : IsLocalMin f x) : mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x = 0 := by
  have hchart : IsLocalMin (f ∘ (extChartAt (𝓡 n) x).symm)
      (extChartAt (𝓡 n) x x) := by
    apply IsLocalMin.comp_continuous _ (continuousAt_extChartAt_symm (I := 𝓡 n) x)
    simpa only [(extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)] using hmin
  exact hchart.hasFDerivAt_eq_zero (RegularLevel.hasFDerivAt_comp_extChartAt_symm hf x)

theorem strict_minimum_on_compact_sublevel_component_of_unique_critical
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {O : Set M} (hO : IsOpen O) {p : M} {b : ℝ}
    (hp : p ∈ O) (hpb : f p < b)
    (hK : IsCompact (connectedComponentIn (O ∩ f ⁻¹' Iic b) p))
    (hunique : ∀ x ∈ connectedComponentIn (O ∩ f ⁻¹' Iic b) p,
      mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x = 0 → x = p) :
    ∀ x ∈ connectedComponentIn (O ∩ f ⁻¹' Iic b) p, x ≠ p → f p < f x := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (E n) M
  let K := connectedComponentIn (O ∩ f ⁻¹' Iic b) p
  have hpK : p ∈ K := mem_connectedComponentIn ⟨hp, hpb.le⟩
  have hnhds (x : M) (hx : x ∈ K) (hxb : f x < b) : K ∈ 𝓝 x := by
    have hxO := (connectedComponentIn_subset _ _ hx).1
    have ho : O ∩ f ⁻¹' Iic b ∈ 𝓝 x := mem_of_superset
      ((hO.inter (hf.continuous.isOpen_preimage _ isOpen_Iio)).mem_nhds ⟨hxO, hxb⟩)
      (inter_subset_inter_right O (preimage_mono Iio_subset_Iic_self))
    have hc := connectedComponentIn_mem_nhds ho
    rwa [← connectedComponentIn_eq hx] at hc
  obtain ⟨q, hqK, hqmin⟩ := hK.exists_isMinOn ⟨p, hpK⟩ hf.continuous.continuousOn
  have hqb : f q < b := (hqmin hpK).trans_lt hpb
  have hqp : q = p := hunique q hqK
    (mfderiv_eq_zero_of_isLocalMin hf (hqmin.isLocalMin (hnhds q hqK hqb)))
  subst q
  intro x hx hxp
  apply lt_of_le_of_ne (hqmin hx)
  intro heq
  have hxMin : IsMinOn f K x := by
    intro y hy
    rw [← heq]
    exact hqmin hy
  exact hxp (hunique x hx (mfderiv_eq_zero_of_isLocalMin hf
    (hxMin.isLocalMin (hnhds x hx (heq ▸ hpb)))))

end Poincare.Geometry.Manifold
