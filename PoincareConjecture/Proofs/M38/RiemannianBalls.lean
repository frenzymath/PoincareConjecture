import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Topology.Connected.PathConnected

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem isPathConnected_ball (g : RiemannianMetric n M) (x : M)
    {r : ℝ} (hr : 0 < r) : IsPathConnected (g.ball x r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  refine ⟨x, ?_, ?_⟩
  · change Manifold.riemannianEDist (𝓡 n) x x < ENNReal.ofReal r
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  · intro y hy
    change Manifold.riemannianEDist (𝓡 n) x y < ENNReal.ofReal r at hy
    obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hy
    apply JoinedIn.ofLine hγ.continuousOn hγ0 hγ1
    rintro _ ⟨t, ht, rfl⟩
    change Manifold.riemannianEDist (𝓡 n) x (γ t) < ENNReal.ofReal r
    have hprefix := hγ.mono (Set.Icc_subset_Icc le_rfl ht.2)
    exact (Manifold.riemannianEDist_le_pathELength hprefix hγ0 rfl ht.1).trans_lt
      ((Manifold.pathELength_mono (I := 𝓡 n) le_rfl ht.2).trans_lt hlength)

end PoincareConjecture.M38
