import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Descent
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.Descent
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Descent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

theorem limitFinite_endpoint_flow_descent
    {n : ℕ} {ι : Type*} [Nonempty ι] {P : ι → Type*} {N : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace N]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ N]
    {J : Set ℝ} (F : ∀ i, RicciFlow n (P i) J) {t0 : ℝ} (ht0 : t0 ∈ J)
    (q : ∀ i, P i → N)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinv : ∀ t ∈ J, ∀ i j (x : P i) (y : P j), q i x = q j y →
      ∀ (a b : TangentSpace (𝓡 n) x) (c d : TangentSpace (𝓡 n) y),
        mfderiv (𝓡 n) (𝓡 n) (q i) x a = mfderiv (𝓡 n) (𝓡 n) (q j) y c →
        mfderiv (𝓡 n) (𝓡 n) (q i) x b = mfderiv (𝓡 n) (𝓡 n) (q j) y d →
        ((F i).metric t).inner x a b = ((F j).metric t).inner y c d) :
    ∃ G : RicciFlow n N J,
      ∀ t ∈ J, ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
        ((F i).metric t).inner x a b = (G.metric t).inner (q i x)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x b) := by
  classical
  have hex : ∀ t : J, ∃! g : RiemannianMetric n N,
      ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
        ((F i).metric t).inner x a b = g.inner (q i x)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x b) := by
    intro t
    exact exists_unique_metric_of_covering_local_diffeomorphisms
      (fun i => (F i).metric t) q hq hcover (hinv t t.property)
  choose gs hgs _huniq using hex
  let g : ℝ → RiemannianMetric n N :=
    fun t => if ht : t ∈ J then gs ⟨t, ht⟩ else gs ⟨t0, ht0⟩
  have hpres : ∀ t ∈ J, ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
      ((F i).metric t).inner x a b = (g t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b) := by
    intro t ht i x a b
    simpa only [g, dif_pos ht] using hgs ⟨t, ht⟩ i x a b
  have hg : RiemannianMetric.IsSmoothFamilyOn g J :=
    isSmoothFamilyOn_of_local_diffeomorphisms (fun i => (F i).metric) g
      (fun i => (F i).smooth) q hq hcover hpres
  let D0 : LeviCivitaData (g t0) := (g t0).leviCivitaDataOfCover
    (fun i => (F i).metric t0) (fun i => (F i).connection t0) q
    (fun i => (hq i).contMDiff)
    (fun i x => ⟨(hq i x).mfderivToContinuousLinearEquiv (by simp), rfl⟩)
    (hpres t0 ht0) hcover
  obtain ⟨G, hG⟩ := RicciFlow.exists_of_covering_local_diffeomorphisms F g hg
    t0 D0 q hq hcover hpres
  refine ⟨G, ?_⟩
  rw [hG]
  exact hpres

end PoincareConjecture.M47
