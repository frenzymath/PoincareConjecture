import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Gluing.Descent
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Descent
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.Descent











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe uI uU uM

namespace PoincareConjecture.M30




theorem exists_finite_extension_of_covering_chart_flows
    {n : ℕ} {ι : Type uI} [Nonempty ι]
    {U : ι → Type uU} {M : Type uM}
    [∀ i, TopologicalSpace (U i)] [TopologicalSpace M]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (U i)]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [∀ i, IsManifold (𝓡 n) ∞ (U i)] [IsManifold (𝓡 n) ∞ M]
    {a b : ℝ} (hab : a < b)
    (F : RicciFlow n M (Ioo a b))
    (Fchart : ∀ i, RicciFlow n (U i) (Icc a b))
    (q : ∀ i, U i → M)
    (hq : ∀ i, IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (q i))
    (hcover : ∀ y, ∃ i x, q i x = y)
    (hinterior : ∀ t ∈ Ioo a b, ∀ i (x : U i)
      (v w : TangentSpace (𝓡 n) x),
      ((Fchart i).metric t).inner x v w = (F.metric t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x v)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x w)) :
    ∃ G : RicciFlow n M (Icc a b),
      (∀ t ∈ Ioo a b, G.metric t = F.metric t) ∧
      ∀ t ∈ Icc a b, ∀ i (x : U i)
        (v w : TangentSpace (𝓡 n) x),
        ((Fchart i).metric t).inner x v w = (G.metric t).inner (q i x)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x v)
          (mfderiv (𝓡 n) (𝓡 n) (q i) x w) := by
  classical
  have hinv (t : ℝ) (ht : t ∈ Icc a b) (i j : ι) (x : U i) (y : U j)
      (hxy : q i x = q j y)
      (v w : TangentSpace (𝓡 n) x) (v' w' : TangentSpace (𝓡 n) y)
      (hv : mfderiv (𝓡 n) (𝓡 n) (q i) x v = mfderiv (𝓡 n) (𝓡 n) (q j) y v')
      (hw : mfderiv (𝓡 n) (𝓡 n) (q i) x w = mfderiv (𝓡 n) (𝓡 n) (q j) y w') :
      ((Fchart i).metric t).inner x v w = ((Fchart j).metric t).inner y v' w' := by
    have hpast : EqOn (fun s => ((Fchart i).metric s).inner x v w)
        (fun s => ((Fchart j).metric s).inner y v' w') (Ioo a b) := by
      intro s hs
      dsimp only
      rw [hinterior s hs, hinterior s hs]
      have hform : ((F.metric s).inner (q i x) : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) = (F.metric s).inner (q j y) :=
        congrArg (fun z : M => show EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ from (F.metric s).inner z) hxy
      have hvec : ((mfderiv (𝓡 n) (𝓡 n) (q i) x v,
          mfderiv (𝓡 n) (𝓡 n) (q i) x w) :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =
          (mfderiv (𝓡 n) (𝓡 n) (q j) y v', mfderiv (𝓡 n) (𝓡 n) (q j) y w') :=
        Prod.ext hv hw
      exact congrArg₂ (fun (B : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) => B z.1 z.2)
          hform hvec
    exact hpast.of_subset_closure
      (fun s hs => ((Fchart i).equation s hs x v w).continuousWithinAt)
      (fun s hs => ((Fchart j).equation s hs y v' w').continuousWithinAt)
      Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne]) ht
  let clamp (t : ℝ) := max a (min t b)
  have hclamp (t : ℝ) : clamp t ∈ Icc a b :=
    ⟨le_max_left _ _, max_le hab.le (min_le_right _ _)⟩
  have hclamp_eq (t : ℝ) (ht : t ∈ Icc a b) : clamp t = t := by
    dsimp only [clamp]
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have hex (t : ℝ) := Poincare.Gluing.exists_unique_metric_of_covering_local_diffeomorphisms
    (fun i => (Fchart i).metric (clamp t)) q hq hcover (hinv (clamp t) (hclamp t))
  let g (t : ℝ) := Classical.choose (hex t)
  have hpres (t : ℝ) (ht : t ∈ Icc a b) (i : ι) (x : U i)
      (v w : TangentSpace (𝓡 n) x) :
      ((Fchart i).metric t).inner x v w = (g t).inner (q i x)
        (mfderiv (𝓡 n) (𝓡 n) (q i) x v) (mfderiv (𝓡 n) (𝓡 n) (q i) x w) := by
    have h := (Classical.choose_spec (hex t)).1 i x v w
    change ((Fchart i).metric (clamp t)).inner x v w = (g t).inner (q i x)
      (mfderiv (𝓡 n) (𝓡 n) (q i) x v) (mfderiv (𝓡 n) (𝓡 n) (q i) x w) at h
    rwa [hclamp_eq t ht] at h
  have heq (t : ℝ) (ht : t ∈ Ioo a b) : g t = F.metric t := by
    symm
    apply (Classical.choose_spec (hex t)).2 (F.metric t)
    intro i x v w
    simpa only [hclamp_eq t (Ioo_subset_Icc_self ht)] using hinterior t ht i x v w
  have hsmooth : RiemannianMetric.IsSmoothFamilyOn g (Icc a b) :=
    Poincare.Gluing.isSmoothFamilyOn_of_local_diffeomorphisms
      (fun i => (Fchart i).metric) g (fun i => (Fchart i).smooth) q hq hcover hpres
  obtain ⟨G, hG⟩ := RicciFlow.exists_of_covering_local_diffeomorphisms
    Fchart g hsmooth a (g a).leviCivitaData q hq hcover hpres
  refine ⟨G, ?_, ?_⟩
  · simpa only [hG] using heq
  · simpa only [hG] using hpres

end PoincareConjecture.M30
