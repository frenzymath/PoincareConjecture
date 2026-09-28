import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Descent
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.Descent
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Descent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Poincare.Gluing
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

theorem terminalGerms_finite_flow_descent
    {n : ℕ} {ι : Type*} [Finite ι] [Nonempty ι]
    {P : ι → Type*} {N : Type*}
    [∀ i, TopologicalSpace (P i)] [TopologicalSpace N]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (P i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [∀ i, IsManifold (𝓡 n) ∞ (P i)] [IsManifold (𝓡 n) ∞ N]
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow n (P i) (Icc (-tau i) 0))
    (q : ∀ i, P i → N)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinv : ∀ i j t, t ∈ Icc (-tau i) 0 → t ∈ Icc (-tau j) 0 →
      ∀ (x : P i) (y : P j), q i x = q j y →
      ∀ (a b : TangentSpace (𝓡 n) x) (c d : TangentSpace (𝓡 n) y),
        mfderiv (𝓡 n) (𝓡 n) (q i) x a = mfderiv (𝓡 n) (𝓡 n) (q j) y c →
        mfderiv (𝓡 n) (𝓡 n) (q i) x b = mfderiv (𝓡 n) (𝓡 n) (q j) y d →
        ((F i).metric t).inner x a b = ((F j).metric t).inner y c d)
    (g0 : RiemannianMetric n N)
    (hterminal : ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
      ((F i).metric 0).inner x a b = g0.inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b)) :
    ∃ delta : ℝ, 0 < delta ∧ (∀ i, delta < tau i) ∧
      ∃ G : RicciFlow n N (Icc (-delta) 0), G.metric 0 = g0 ∧
        ∀ t ∈ Icc (-delta) 0, ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
          ((F i).metric t).inner x a b = (G.metric t).inner (q i x)
            (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
            (mfderiv (𝓡 n) (𝓡 n) (q i) x b) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let m : ℝ := Finset.univ.inf' Finset.univ_nonempty tau
  have hm : 0 < m := (Finset.lt_inf'_iff _).mpr (fun i _ => htau i)
  have hmi (i : ι) : m ≤ tau i := Finset.inf'_le tau (Finset.mem_univ i)
  let delta : ℝ := m / 2
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdt (i : ι) : delta < tau i := by dsimp [delta]; linarith [hmi i]
  let J : Set ℝ := Icc (-delta) 0
  have hJ (i : ι) : J ⊆ Icc (-tau i) 0 := by
    intro t ht
    exact ⟨(neg_le_neg (hdt i).le).trans ht.1, ht.2⟩
  have hzero : 0 ∈ J := ⟨neg_nonpos.mpr hd.le, le_rfl⟩
  let Fsmall : ∀ i, RicciFlow n (P i) J := fun i => {
    metric := (F i).metric
    connection := (F i).connection
    interval := ordConnected_Icc
    nontrivial := ⟨-delta, ⟨le_rfl, neg_nonpos.mpr hd.le⟩,
      0, hzero, (neg_lt_zero.mpr hd).ne⟩
    smooth := (F i).smooth.mono (prod_mono (hJ i) subset_rfl)
    equation := fun t ht x a b => ((F i).equation t (hJ i ht) x a b).mono (hJ i) }
  have hex : ∀ t : J, ∃! gN : RiemannianMetric n N,
      ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
        ((F i).metric t).inner x a b = gN.inner (q i x)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x b) := by
    intro t
    exact exists_unique_metric_of_covering_local_diffeomorphisms
      (fun i => (F i).metric t) q hq hcover
      (fun i j => hinv i j t (hJ i t.property) (hJ j t.property))
  choose gs hgs huniq using hex
  let gN : ℝ → RiemannianMetric n N :=
    fun t => if ht : t ∈ J then gs ⟨t, ht⟩ else g0
  have hpres : ∀ t ∈ J, ∀ i (x : P i) (a b : TangentSpace (𝓡 n) x),
      ((F i).metric t).inner x a b = (gN t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b) := by
    intro t ht i x a b
    simp only [gN, dif_pos ht]
    exact hgs ⟨t, ht⟩ i x a b
  have hgN : RiemannianMetric.IsSmoothFamilyOn gN J :=
    isSmoothFamilyOn_of_local_diffeomorphisms (fun i => (Fsmall i).metric) gN
      (fun i => (Fsmall i).smooth) q hq hcover hpres
  have hgzero : gN 0 = g0 := by
    simp only [gN, dif_pos hzero]
    exact (huniq ⟨0, hzero⟩ g0 hterminal).symm
  let D0 : LeviCivitaData g0 := g0.leviCivitaDataOfCover
    (fun i => (F i).metric 0) (fun i => (F i).connection 0) q
    (fun i => (hq i).contMDiff)
    (fun i x => ⟨(hq i x).mfderivToContinuousLinearEquiv (by simp), rfl⟩)
    hterminal hcover
  obtain ⟨G, hG⟩ := RicciFlow.exists_of_covering_local_diffeomorphisms Fsmall gN hgN
    0 (D0.withMetric (gN 0)) q hq hcover hpres
  refine ⟨delta, hd, hdt, G, ?_, ?_⟩
  · rw [hG]
    exact hgzero
  · rw [hG]
    exact hpres

end PoincareConjecture.M47
