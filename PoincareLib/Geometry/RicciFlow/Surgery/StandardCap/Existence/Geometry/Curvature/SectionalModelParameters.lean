import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.SectionalTests

/-!
# Fixed model parameters for the cap's planes

On Euclidean space the tangent trivializations are identities. Compact
Euclidean orthonormal pairs therefore parametrize all sectional lower
tests, and their actual metric quotients vary continuously along a flow.
These are the parameter-space facts for Lemma 12.6, pp. 297-298.
-/

set_option autoImplicit false
-- Identify the model tangent fibers without unfolding their normed structures.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M34

open M04

variable {n : ℕ}

set_option maxHeartbeats 800000 in
-- Kernel checking unfolds the canonical model/tangent module instances.
/-- A lower quotient bound on compact Euclidean pairs controls every
tangent pair for an arbitrary metric (Lemma 12.6, pp. 297-298). -/
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
-- Kernel checking identifies the two canonical tangent/model topologies.
/-- Joint continuity of the actual sectional quotient with fixed model
orthonormal plane parameters (Lemma 12.6, pp. 297-298). -/
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

end PoincareMT.M34
