import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteHarnackDomain
import PoincareConjecture.Proofs.M04.CompactSlabParabolic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.Regularity










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47



theorem limitNoncollapse_compact_scalar_lower_preserved
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (h04 : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow 3 M J)
    (hcompact : IsCompact (univ : Set M)) {a b c : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J) (hinit : ∀ x, c ≤ (F.connection a).scalarCurvature x) :
    ∀ t ∈ Icc a b, ∀ x, c ≤ (F.connection t).scalarCurvature x := by
  let f := fun t x => (F.connection t).scalarCurvature x - c
  let v := fun t x => (F.connection t).laplacian (F.connection t).scalarCurvature x +
    2 * (F.connection t).ricciNormSq x
  have hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ (univ : Set M)) :=
    ((h04.scalar_regular 3 M J F).continuousOn.mono
      (prod_mono hJ Subset.rfl)).sub continuousOn_const
  have hderiv : ∀ t ∈ Icc a b, ∀ x ∈ (univ : Set M),
      HasDerivWithinAt (fun s => f s x) (v t x) (Icc a b) t := by
    intro t ht x _hx
    exact ((h04.scalar_evolution 3 M J F t (hJ ht) x).mono hJ).sub_const c
  have hmin : ∀ t ∈ Ioc a b, ∀ x ∈ (univ : Set M),
      (∀ y ∈ (univ : Set M), f t x ≤ f t y) → f t x < 0 →
        -(0 : ℝ) * f t x ≤ v t x := by
    intro t _ht x _hx hmin _hneg
    have hlocal : IsLocalMin (F.connection t).scalarCurvature x :=
      Eventually.of_forall (fun y => (sub_le_sub_iff_right c).mp (hmin y (mem_univ y)))
    have hlap := (F.connection t).laplacian_nonneg_of_isLocalMin
      (h04.tensor_calculus 3 M (F.metric t) (F.connection t)).contMDiff_scalarCurvature.contMDiffAt
      hlocal
    have hric : 0 ≤ (F.connection t).ricciNormSq x :=
      Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    dsimp only [v]
    nlinarith
  have hresult := M04.compact_subset_min_velocity_nonnegative_Icc hcompact hab f v hf
    hderiv hmin (fun x _hx => sub_nonneg.mpr (hinit x))
  intro t ht x
  exact sub_nonneg.mp (hresult t ht x (mem_univ x))

private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    T2Space L.carrier.carrier := L.carrier.t2Space



theorem limitNoncollapse_compact_exists_low_point
    (h04 : RicciFlowCurvatureTheory.{u}) {H : ℝ≥0∞}
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H))
    (hcompact : IsCompact (univ : Set L.carrier.carrier))
    (t : ℝ) (ht : t ∈ blowupBackwardInterval H) :
    ∃ y : L.carrier.carrier, (L.flow.connection t).scalarCurvature y ≤ 1 := by
  by_cases ht0 : t = 0
  · subst t
    exact ⟨L.base, L.scalar_normalized.le⟩
  have htneg : t < 0 := lt_of_le_of_ne ht.1 ht0
  have hcont := (h04.tensor_calculus 3 L.carrier.carrier
    (L.flow.metric t) (L.flow.connection t)).contMDiff_scalarCurvature.continuous
  obtain ⟨y, _hy, hmin⟩ := hcompact.exists_isMinOn ⟨L.base, mem_univ _⟩ hcont.continuousOn
  have hJ : Icc t 0 ⊆ blowupBackwardInterval H := L.flow.interval.out ht L.zero_mem
  have hbound := limitNoncollapse_compact_scalar_lower_preserved h04 L.flow hcompact
    htneg hJ (fun x => hmin (mem_univ x)) 0 ⟨ht.1, le_rfl⟩ L.base
  exact ⟨y, hbound.trans_eq L.scalar_normalized⟩

end PoincareConjecture.M47
