import PoincareConjecture.Proofs.M09.ScaledAdaptedField

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u v

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] {ι : Type v} [Fintype ι]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem field_sum_smooth (α : ℝ → M)
    (P : ι → ∀ t, TangentSpace (𝓡 n) (α t))
    (U : Set ℝ) (hU : IsOpen U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hP : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨α t, P i t⟩ : TangentBundle (𝓡 n) M)) U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨α t, ∑ i, P i t⟩ : TangentBundle (𝓡 n) M)) U := by
  intro s hs
  let p := α s
  let V := U ∩ α ⁻¹' (chartAt E p).source
  have hV : IsOpen V := hα.continuousOn.isOpen_inter_preimage hU (chartAt E p).open_source
  have hsV : s ∈ V := ⟨hs, mem_chart_source E p⟩
  let v : ι → ℝ → E := fun i t ↦ mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (α t) (P i t)
  have hv (i : ι) : ContDiffOn ℝ ∞ (v i) V :=
    field_chart_coordinates_smooth p α (P i) V ((hP i).mono Set.inter_subset_left)
      (fun _ ht ↦ ht.2)
  have hsum : ContDiffOn ℝ ∞ (fun t ↦ ∑ i, v i t) V :=
    ContDiffOn.sum (fun i _ ↦ hv i)
  have hlocal : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun t ↦ (⟨α t, chartVectorField p (∑ i, v i t) (α t)⟩ : TangentBundle (𝓡 n) M)) V :=
    (chartVectorField_param_smooth p (fun t ↦ ∑ i, v i t) V hsum).comp
      (contMDiffOn_id.prodMk (hα.mono Set.inter_subset_left)) (fun _ ht ↦ ⟨ht, ht.2⟩)
  apply ((hlocal.contMDiffAt (hV.mem_nhds hsV)).congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hV.mem_nhds hsV] with t ht
  have heq : chartVectorField p (∑ i, v i t) (α t) = ∑ i, P i t := by
    change (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (α t)).inverse (∑ i, v i t) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ ↦ chartVectorField_differential p (α t) (P i t) ht.2)
  rw [heq]

end PoincareConjecture.Proofs.M09
