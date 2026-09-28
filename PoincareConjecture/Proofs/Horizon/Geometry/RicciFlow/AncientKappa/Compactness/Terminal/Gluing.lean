import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gluing.Descent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.Descent
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Limit.Descent











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow



theorem exists_terminal_extension_of_covering_chart_flows
    {n : ℕ} {ι : Type*} [Nonempty ι] {U : ι → Type*} {M : Type*}
    [∀ i, TopologicalSpace (U i)] [TopologicalSpace M]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (U i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [∀ i, IsManifold (𝓡 n) ∞ (U i)] [IsManifold (𝓡 n) ∞ M]
    (F : RicciFlow n M (Iio 0)) (Fchart : ∀ i, RicciFlow n (U i) (Iic 0))
    (q : ∀ i, U i → M)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinterior : ∀ t : ℝ, t < 0 → ∀ i (x : U i) (a b : TangentSpace (𝓡 n) x),
      ((Fchart i).metric t).inner x a b = (F.metric t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x b)) :
    ∃ G : RicciFlow n M (Iic 0),
      (∀ t : ℝ, t < 0 → G.metric t = F.metric t) ∧
      ∀ t : ℝ, t ≤ 0 → ∀ i (x : U i) (a b : TangentSpace (𝓡 n) x),
        ((Fchart i).metric t).inner x a b = (G.metric t).inner (q i x)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x a)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x b) := by
  classical
  have hinv (t : ℝ) (ht : t ≤ 0) (i j : ι) (x : U i) (y : U j)
      (hxy : q i x = q j y)
      (a b : TangentSpace (𝓡 n) x) (c d : TangentSpace (𝓡 n) y)
      (ha : mfderiv (𝓡 n) (𝓡 n) (q i) x a = mfderiv (𝓡 n) (𝓡 n) (q j) y c)
      (hb : mfderiv (𝓡 n) (𝓡 n) (q i) x b = mfderiv (𝓡 n) (𝓡 n) (q j) y d) :
      ((Fchart i).metric t).inner x a b = ((Fchart j).metric t).inner y c d := by
    have hpast : EqOn (fun s => ((Fchart i).metric s).inner x a b)
        (fun s => ((Fchart j).metric s).inner y c d) (Iio 0) := by
      intro s hs
      dsimp only
      rw [hinterior s hs, hinterior s hs]
      have hform : ((F.metric s).inner (q i x) : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) = (F.metric s).inner (q j y) :=
        congrArg (fun z : M => show EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from (F.metric s).inner z) hxy
      have hv : ((mfderiv (𝓡 n) (𝓡 n) (q i) x a,
          mfderiv (𝓡 n) (𝓡 n) (q i) x b) :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =
          (mfderiv (𝓡 n) (𝓡 n) (q j) y c, mfderiv (𝓡 n) (𝓡 n) (q j) y d) :=
        Prod.ext ha hb
      exact congrArg₂ (fun (B : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) => B v.1 v.2) hform hv
    exact hpast.of_subset_closure
      (fun s hs => ((Fchart i).equation s hs x a b).continuousWithinAt)
      (fun s hs => ((Fchart j).equation s hs y c d).continuousWithinAt)
      Iio_subset_Iic_self (by rw [closure_Iio]) ht
  have hex (t : ℝ) := Poincare.Gluing.exists_unique_metric_of_covering_local_diffeomorphisms
    (fun i => (Fchart i).metric (min t 0)) q hq hcover
      (hinv (min t 0) (min_le_right _ _))
  let g (t : ℝ) := Classical.choose (hex t)
  have hpres (t : ℝ) (ht : t ≤ 0) (i : ι) (x : U i)
      (a b : TangentSpace (𝓡 n) x) :
      ((Fchart i).metric t).inner x a b = (g t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x a) (mfderiv (𝓡 n) (𝓡 n) (q i) x b) := by
    have h := (Classical.choose_spec (hex t)).1 i x a b
    change ((Fchart i).metric (min t 0)).inner x a b = (g t).inner (q i x)
      (mfderiv (𝓡 n) (𝓡 n) (q i) x a) (mfderiv (𝓡 n) (𝓡 n) (q i) x b) at h
    rwa [min_eq_left ht] at h
  have heq (t : ℝ) (ht : t < 0) : g t = F.metric t := by
    symm
    apply (Classical.choose_spec (hex t)).2 (F.metric t)
    intro i x a b
    simpa only [min_eq_left ht.le] using hinterior t ht i x a b
  have hsmooth : RiemannianMetric.IsSmoothFamilyOn g (Iic 0) :=
    Poincare.Gluing.isSmoothFamilyOn_of_local_diffeomorphisms
      (fun i => (Fchart i).metric) g (fun i => (Fchart i).smooth) q hq hcover hpres
  obtain ⟨G, hG⟩ := exists_of_covering_local_diffeomorphisms Fchart g hsmooth
    0 (g 0).leviCivitaData q hq hcover hpres
  refine ⟨G, ?_, ?_⟩
  · simpa only [hG] using heq
  · simpa only [hG] using hpres

end PoincareConjecture.RicciFlow
