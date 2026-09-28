import PoincareConjecture.Proofs.M34.Standard.SectionalTests










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

open M04

variable {n : ℕ}

set_option maxHeartbeats 800000 in



theorem sectional_lower_of_model_pairs
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) (m : ℝ)
    (hmin : ∀ p ∈ modelOrthonormalPairs n,
      m ≤ D.curvatureTensor x p.1 p.2 p.1 p.2 / metricGram g x p.1 p.2)
    (u v : TangentSpace (𝓡 n) x) :
    m * metricGram g x u v ≤ D.curvatureTensor x u v u v := by
  let f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] TangentSpace (𝓡 n) x :=
    { toFun := fun v => v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine sectional_lower_of_surjective_linearMap D x f Function.surjective_id m ?_ u v
  intro p q hp hq hpq
  have hmem : (p, q) ∈ modelOrthonormalPairs n := ⟨hp, hq, hpq⟩
  exact (le_div_iff₀ (metricGram_pos_of_linearIndependent g x p q
    (modelOrthonormalPairs_linearIndependent hmem))).mp (hmin (p, q) hmem)

set_option maxHeartbeats 800000 in



theorem continuousOn_flow_sectionalRayleigh_model {J : Set ℝ}
    (F : RicciFlow n (EuclideanSpace ℝ (Fin n)) J) :
    ContinuousOn (fun z : ℝ × (EuclideanSpace ℝ (Fin n) ×
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) =>
      (F.connection z.1).curvatureTensor z.2.1 z.2.2.1 z.2.2.2 z.2.2.1 z.2.2.2 /
        metricGram (F.metric z.1) z.2.1 z.2.2.1 z.2.2.2)
      (J ×ˢ (univ ×ˢ modelOrthonormalPairs n)) := by
  have hsymm (x v : EuclideanSpace ℝ (Fin n)) :
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) 0).symmL ℝ x v =
        v := by
    rw [TangentBundle.symmL_model_space]
    rfl
  have h : ContinuousOn (fun z : (ℝ × EuclideanSpace ℝ (Fin n)) ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
    (F.connection z.1.1).curvatureTensor z.1.2 z.2.1 z.2.2 z.2.1 z.2.2 /
      metricGram (F.metric z.1.1) z.1.2 z.2.1 z.2.2)
      ((J ×ˢ univ) ×ˢ modelOrthonormalPairs n) := by
    simpa only [hsymm, TangentBundle.trivializationAt_baseSet, chartAt_self_eq,
      OpenPartialHomeomorph.refl_source] using
      continuousOn_flow_sectionalRayleigh_trivialization F (0 : EuclideanSpace ℝ (Fin n))
  exact h.comp ((continuous_fst.prodMk continuous_snd.fst).prodMk
    continuous_snd.snd).continuousOn (fun z hz => ⟨⟨hz.1, mem_univ _⟩, hz.2.2⟩)

end PoincareConjecture.M34
