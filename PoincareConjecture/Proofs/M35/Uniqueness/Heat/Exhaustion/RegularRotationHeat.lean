import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.CompactKilling
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.InitialJetCompatibility

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

local notation "V" => StandardCapSpace

theorem compactKillingHeat_of_regular_rotation {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T : ℝ} (hTlt : T < G.lifetime)
    (B : V →L[ℝ] V) (hskew : ∀ x, inner ℝ x (B x) = 0)
    (hkill : ∀ x u v : V,
      DeTurckNative.metricLieDerivative g₀.connection (fun y => B y) x u v = 0)
    {E : Set V} (X : ℝ → V → V) (hXs : ∀ t, ContDiff ℝ ∞ (X t))
    (hjoint : ContDiffOn ℝ ∞ (Function.uncurry X) (Ioo 0 G.lifetime ×ˢ univ))
    (hX : ContinuousOn (Function.uncurry X) (Icc 0 T ×ˢ univ))
    (hDX : ContinuousOn (fun p : ℝ × V => fderiv ℝ (X p.1) p.2) (Icc 0 T ×ˢ E))
    (hbound : ∀ t ∈ Icc 0 T, ∀ x ∈ E,
      (G.flow.metric t).inner x (X t x) (X t x) ≤ 4 * ‖B‖ ^ 2)
    (hinit : ∀ x ∈ E, X 0 =ᶠ[𝓝 x] fun y => B y)
    (hheat : ∀ t ∈ Ioc 0 T, ∀ x ∈ E, ∀ᶠ y in 𝓝 x,
      HasDerivWithinAt (fun s => X s y)
        (@Add.add V inferInstance
          (∑ i, fieldHessian (G.flow.connection t) (X t) y
            ((G.flow.metric t).orthonormalBasis y i) ((G.flow.metric t).orthonormalBasis y i))
          (RicciFlow.ricciSharp (G.flow.connection t) y (X t y))) (Ico 0 G.lifetime) t) :
    Nonempty (CompactKillingHeat G T (4 * ‖B‖ ^ 2) (9 * ‖B‖ ^ 2) (fun y => B y) E) := by
  have hI : Icc 0 T ⊆ Ico 0 G.lifetime := fun _ ht => ⟨ht.1, ht.2.trans_lt hTlt⟩
  have hXE := hX.mono (prod_mono Subset.rfl (subset_univ E))
  exact ⟨{
    field := X
    slice_smooth := hXs
    joint_smooth := hjoint
    value_continuous := hX
    energy_zero_continuous := raw_vectorHeatJetEnergy_zero_continuousOn G hI X hXE
    energy_one_continuous := raw_vectorHeatJetEnergy_one_continuousOn G hI X hXs hXE hDX
    defect_continuous := raw_killing_defect_normSq_continuousOn G.flow hI X hXs hXE hDX
    metric_bound := hbound
    initial_gradient := fun x hx => raw_initial_heat_gradient_bound G B hskew X (hXs 0) (hinit x hx)
    initial_killing := fun x hx => raw_initial_heat_killing G B hkill X (hXs 0) (hinit x hx)
    initial_value := fun x hx => (hinit x hx).eq_of_nhds
    heat := hheat }⟩

end PoincareConjecture.M35.Uniqueness.Heat
