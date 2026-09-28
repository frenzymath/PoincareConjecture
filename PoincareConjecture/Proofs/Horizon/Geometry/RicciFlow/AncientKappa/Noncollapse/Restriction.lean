import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow



theorem ancientKappaNoncollapsed_restrict_of_metricKappaNoncollapsed
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    {δ κ : ℝ} (F : RicciFlow n M (Iio δ)) (hδ : 0 < δ)
    (hκ : ∀ t ∈ Iio δ, MetricKappaNoncollapsed (F.metric t) (F.connection t) κ) :
    AncientKappaNoncollapsed
      (Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
        (show Iic (0 : ℝ) ⊆ Iio δ from fun _ ht => ht.trans_lt hδ)
        ordConnected_Iic (show (Iic (0 : ℝ)).Nontrivial from
          ⟨-1, by norm_num, 0, by simp, by norm_num⟩)) κ := by
  intro r₀ _ t ht x r hr _ hcurv
  apply (hκ t (ht.trans_lt hδ)).2 x r hr
  intro y hy
  exact hcurv t ⟨by nlinarith [sq_pos_of_pos hr], le_rfl⟩ y hy

end PoincareConjecture.RicciFlow
