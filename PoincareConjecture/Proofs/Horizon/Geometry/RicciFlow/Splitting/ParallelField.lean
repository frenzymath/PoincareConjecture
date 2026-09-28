import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.LocalRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Calculus
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow.Splitting

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

structure ParallelFieldData (F : RicciFlow n M (Icc a b)) (f : M → ℝ) where
  field : ∀ x : M, TangentSpace (𝓡 n) x
  terminal : ∀ x, field x = (F.connection b).gradient f x
  parallel : ∀ t ∈ Ico a b, ∀ x : M, ∀ u : TangentSpace (𝓡 n) x,
    (F.connection t).connection field x u = 0
  ricci_null : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
    (F.connection t).ricci x (field x) v = 0

theorem curvature_eq_zero_of_parallel_field
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus)
    (X : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X))
    (hparallel : ∀ x : M, D.connection X x = 0)
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    D.curvature x u v (X x) = 0 := by
  obtain ⟨U, hU, hx, hExt⟩ := exists_open_contMDiffOn_extend (n := n) x
  let E := EuclideanSpace ℝ (Fin n)
  let A : (y : M) → TangentSpace (𝓡 n) y := FiberBundle.extend E u
  let B : (y : M) → TangentSpace (𝓡 n) y := FiberBundle.extend E v
  have hA : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% A) U := hExt u
  have hB : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% B) U := hExt v
  have hcurv := hD.2.2.2.2 U hU A B X hA hB hX.contMDiffOn x hx
  have hA0 : (fun y => D.connection X y (A y)) = 0 := by
    funext y
    rw [hparallel y]
    simp
  have hB0 : (fun y => D.connection X y (B y)) = 0 := by
    funext y
    rw [hparallel y]
    simp
  have hzero : D.curvatureOnFields A B X x = 0 := by
    unfold LeviCivitaData.curvatureOnFields
    rw [hA0, hB0, hparallel x]
    simp
  have hpoint : D.curvature x u v (X x) = 0 := by
    have := hcurv.symm ▸ hzero
    simpa [A, B] using this
  exact hpoint

theorem ricci_eq_zero_of_parallel_field
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus)
    (X : (x : M) → TangentSpace (𝓡 n) x)
    (hX : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X))
    (hparallel : ∀ x : M, D.connection X x = 0)
    (x : M) (v : TangentSpace (𝓡 n) x) :
    D.ricci x (X x) v = 0 := by
  let basis := g.orthonormalBasis x
  rw [LeviCivitaData.ricci]
  apply Finset.sum_eq_zero
  intro i hi
  have hpair := hD.2.2.2.1 x (X x) (basis i) v (basis i)
  have hlast := hD.2.2.2.1 x v (basis i) (X x) (basis i)
  rw [hpair.2.1, hlast.1]
  have hcurv := curvature_eq_zero_of_parallel_field D hD X hX hparallel x v (basis i)
  simp [LeviCivitaData.curvatureTensor, hcurv]

def ParallelFieldData.of_parallel_field
    (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M (Icc a b)) (f : M → ℝ)
    (field : ∀ x : M, TangentSpace (𝓡 n) x)
    (terminal : ∀ x, field x = (F.connection b).gradient f x)
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hzero : RiemannianMetric.HasZeroHessian (F.connection b) f)
    (hfield : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (T% field))
    (hparallel : ∀ t ∈ Ico a b, ∀ x : M,
      ∀ u : TangentSpace (𝓡 n) x, (F.connection t).connection field x u = 0) :
    ParallelFieldData F f := by
  have hterminal : field = (F.connection b).gradient f := funext terminal
  have hparallel_closed : ∀ t ∈ Icc a b, ∀ x : M,
      ∀ u : TangentSpace (𝓡 n) x, (F.connection t).connection field x u = 0 := by
    intro t ht x u
    by_cases htb : t = b
    · subst t
      rw [hterminal]
      exact RiemannianMetric.connection_gradient_eq_zero_of_hasZeroHessian hf hzero x u
    · exact hparallel t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩ x u
  refine
    { field := field
      terminal := terminal
      parallel := ?_
      ricci_null := ?_ }
  · intro t ht x u
    exact hparallel t ht x u
  · intro t ht x v
    have hD := hC.tensor_calculus n M (F.metric t) (F.connection t)
    have hpar : ∀ y : M, (F.connection t).connection field y = 0 := by
      intro y
      ext u
      exact hparallel_closed t ht y u
    exact ricci_eq_zero_of_parallel_field (F.connection t) hD field hfield hpar x v

namespace ParallelFieldData

theorem metric_dual_eq
    {F : RicciFlow n M (Icc a b)} {f : M → ℝ}
    (h : ParallelFieldData F f) (hab : a < b) {t : ℝ}
    (ht : t ∈ Icc a b) (x : M) (v : TangentSpace (𝓡 n) x) :
    (F.metric t).inner x (h.field x) v =
      (F.metric b).inner x (h.field x) v := by
  let q : ℝ → ℝ := fun s => (F.metric s).inner x (h.field x) v
  have hderiv : ∀ s ∈ Icc a b, HasDerivWithinAt q 0 (Icc a b) s := by
    intro s hs
    have hflow := F.equation s hs x (h.field x) v
    simpa only [q, h.ricci_null s hs x v, mul_zero] using hflow
  have hdiff : DifferentiableOn ℝ q (Icc a b) := by
    intro s hs
    exact (hderiv s hs).differentiableWithinAt
  have hzero : ∀ s ∈ Ico a b, derivWithin q (Icc a b) s = 0 := by
    intro s hs
    exact (hderiv s ⟨hs.1, hs.2.le⟩).derivWithin
      (uniqueDiffOn_Icc hab s ⟨hs.1, hs.2.le⟩)
  exact (constant_of_derivWithin_zero hdiff hzero t ht).trans
    (constant_of_derivWithin_zero hdiff hzero b ⟨hab.le, le_rfl⟩).symm

end ParallelFieldData

theorem backward_persistence_of_parallel_field_data
    [T3Space M]
    (hab : a < b) (F : RicciFlow n M (Icc a b))
    (_hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (_hcurv : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (_hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ K)
    (f : M → ℝ) (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hunit : RiemannianMetric.HasUnitGradient (F.connection b) f)
    (hzero : RiemannianMetric.HasZeroHessian (F.connection b) f)
    (hfield : ParallelFieldData F f) :
    ∀ t ∈ Icc a b,
      (F.connection t).gradient f = (F.connection b).gradient f ∧
        RiemannianMetric.HasUnitGradient (F.connection t) f ∧
          RiemannianMetric.HasZeroHessian (F.connection t) f := by
  intro t ht
  have hdual (s : ℝ) (hs : s ∈ Icc a b) (x : M)
      (v : TangentSpace (𝓡 n) x) :
      (F.metric s).inner x (hfield.field x) v =
        mvfderiv (𝓡 n) f x v := by
    calc
      (F.metric s).inner x (hfield.field x) v =
          (F.metric b).inner x (hfield.field x) v :=
        ParallelFieldData.metric_dual_eq hfield hab hs x v
      _ = (F.metric b).inner x ((F.connection b).gradient f x) v := by
        rw [hfield.terminal]
      _ = mvfderiv (𝓡 n) f x v := (F.metric b).inner_gradient f x v
  have hgrad (s : ℝ) (hs : s ∈ Icc a b) :
      (F.connection s).gradient f = hfield.field := by
    funext x
    apply (F.metric s).inner_isInvertible x |>.injective
    ext v
    rw [(F.connection s).gradient_eq_metric_gradient]
    exact ((F.metric s).inner_gradient f x v).trans (hdual s hs x v).symm
  have hgrad_eq : (F.connection t).gradient f = (F.connection b).gradient f := by
    exact (hgrad t ht).trans (hgrad b ⟨hab.le, le_rfl⟩).symm
  refine ⟨hgrad_eq, ?_, ?_⟩
  · intro x
    calc
      (F.metric t).inner x ((F.connection t).gradient f x)
          ((F.connection t).gradient f x) =
          (F.metric t).inner x (hfield.field x) (hfield.field x) := by
            rw [hgrad t ht]
      _ = (F.metric b).inner x (hfield.field x) (hfield.field x) :=
        ParallelFieldData.metric_dual_eq hfield hab ht x (hfield.field x)
      _ = (F.metric b).inner x ((F.connection b).gradient f x)
          ((F.connection b).gradient f x) := by
            rw [hfield.terminal]
      _ = 1 := hunit x
  · by_cases htb : t = b
    · subst t
      exact hzero
    · have htlt : t ∈ Ico a b := ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
      intro x u v
      rw [(F.connection t).hessian_eq_inner_connection_gradient (hf x), hgrad t ht,
        hfield.parallel t htlt x u]
      simp

end PoincareConjecture.RicciFlow.Splitting
