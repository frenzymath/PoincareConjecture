import PoincareConjecture.Proofs.M35.Uniqueness.VectorHeatEnergy
import PoincareConjecture.Proofs.M35.Uniqueness.CompleteScalarMaximum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

theorem bounded_vector_heat_normSq_le
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B C : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ t ∈ Ioc 0 T, ContDiff ℝ ∞ (X t))
    (hcont : ContinuousOn (fun z : ℝ × StandardCapSpace =>
      (G.flow.metric z.1).inner z.2 (X z.1 z.2) (X z.1 z.2)) (Icc 0 T ×ˢ univ))
    (hinit : ∀ x, (G.flow.metric 0).inner x (X 0 x) (X 0 x) ≤ C)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x,
      (G.flow.metric t).inner x (X t x) (X t x) ≤ B)
    (hheat : ∀ t ∈ Ioc 0 T, ∀ x,
      HasDerivWithinAt (fun s => X s x)
        (@Add.add StandardCapSpace inferInstance
          (∑ i, fieldHessian (G.flow.connection t) (X t) x
            ((G.flow.metric t).orthonormalBasis x i)
            ((G.flow.metric t).orthonormalBasis x i))
          (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ∀ x, (G.flow.metric t).inner x (X t x) (X t x) ≤ C := by
  let Q : ℝ → StandardCapSpace → ℝ := fun t x =>
    (G.flow.metric t).inner x (X t x) (X t x)
  have hQs (t : ℝ) (ht : t ∈ Ioc 0 T) :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (Q t) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨(G.flow.metric t).toRiemannianMetric⟩
    exact (euclidean_field_contMDiff (hX t ht)).inner_bundle
      (euclidean_field_contMDiff (hX t ht))
  have hnonneg := raw_scalar_nonnegative P G hT hTlt hB (le_refl 0)
    (fun t x => C - Q t x) (continuousOn_const.sub hcont)
    (fun t ht x => contMDiffAt_const.sub (hQs t ht x))
    (fun x => sub_nonneg.mpr (hinit x))
    (fun t ht x => by dsimp [Q]; linarith [hbound t ht x])
    (fun t ht x => ?_)
  · intro t ht x
    exact sub_nonneg.mp (hnonneg t ht x)
  · let a := 2 * (G.flow.metric t).inner x
      (∑ i, fieldHessian (G.flow.connection t) (X t) x
        ((G.flow.metric t).orthonormalBasis x i)
        ((G.flow.metric t).orthonormalBasis x i)) (X t x)
    have hd : HasDerivWithinAt (fun s => Q s x) a (Icc 0 T) t :=
      vector_heat_normSq_hasDerivWithinAt G hT hTlt ⟨ht.1.le, ht.2⟩ X x (hheat t ht x)
    refine ⟨-a, hd.const_sub C, ?_⟩
    have hL := field_normSq_trace_le_laplacian (G.flow.connection t) (X t) (hX t ht) x
    have heq : (fun y => C - Q t y) = fun y => C + (-1 : ℝ) * Q t y := by
      funext y
      ring
    have hscale : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y => (-1 : ℝ) * Q t y) x :=
      contMDiffAt_const.mul (hQs t ht x)
    rw [heq, laplacian_const_add_at _ hscale,
      LeviCivitaData.laplacian_const_mul]
    change -1 * (G.flow.connection t).laplacian (Q t) x + 0 * (C - Q t x) ≤ -a
    change a ≤ (G.flow.connection t).laplacian (Q t) x at hL
    linarith

theorem bounded_vector_heat_zero
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T B : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hB : 0 ≤ B)
    (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ∀ t ∈ Ioc 0 T, ContDiff ℝ ∞ (X t))
    (hcont : ContinuousOn (fun z : ℝ × StandardCapSpace =>
      (G.flow.metric z.1).inner z.2 (X z.1 z.2) (X z.1 z.2)) (Icc 0 T ×ˢ univ))
    (hinit : ∀ x, X 0 x = 0)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x,
      (G.flow.metric t).inner x (X t x) (X t x) ≤ B)
    (hheat : ∀ t ∈ Ioc 0 T, ∀ x,
      HasDerivWithinAt (fun s => X s x)
        (@Add.add StandardCapSpace inferInstance
          (∑ i, fieldHessian (G.flow.connection t) (X t) x
            ((G.flow.metric t).orthonormalBasis x i)
            ((G.flow.metric t).orthonormalBasis x i))
          (RicciFlow.ricciSharp (G.flow.connection t) x (X t x))) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ∀ x, X t x = 0 := by
  have hbound' := bounded_vector_heat_normSq_le P G hT hTlt hB (le_refl 0)
    X hX hcont (fun x => by simp [hinit x]) hbound hheat
  intro t ht x
  by_contra hn
  exact (not_lt_of_ge (hbound' t ht x)) ((G.flow.metric t).pos x _ hn)

end PoincareConjecture.M35.Uniqueness
