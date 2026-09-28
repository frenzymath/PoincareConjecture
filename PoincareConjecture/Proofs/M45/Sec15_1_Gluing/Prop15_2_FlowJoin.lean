import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_TimeJoin
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_ClosedTimeJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M45




theorem ordinaryFlows_timeJoin
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    {a T b : ℝ} (haT : a < T) (hTb : T < b)
    (F : RicciFlow n M (Ioc a T)) (G : RicciFlow n N (Icc T b))
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} {f : EuclideanSpace ℝ (Fin n) → N}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hei : ∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible)
    (hfi : ∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) f x).IsInvertible)
    (hjoin : ∀ x ∈ U, (F.metric T).pullbackCoefficients e x =
      (G.metric T).pullbackCoefficients f x) :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      if p.1 < T then (F.metric p.1).pullbackCoefficients e p.2
      else (G.metric p.1).pullbackCoefficients f p.2) (Ioc a b ×ˢ U) := by
  have hleft := M44.contDiffOn_pullbackCoefficients_within F hU he
  have hright := M44.contDiffOn_pullbackCoefficients_within G hU hf
  apply timeJoin_smooth_finalEndpoint hTb hU _ hright
  apply ricciCoefficients_timeJoin hTb hU hleft hright hjoin
  · intro p hp
    exact (F.metric p.1).isInvertible_pullbackCoefficients (hei p.2 hp.2).injective
  · intro p hp
    exact (G.metric p.1).isInvertible_pullbackCoefficients (hfi p.2 hp.2).injective
  · let F' := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
      Ioo_subset_Ioc_self ordConnected_Ioo (Ioo_infinite haT).nontrivial
    intro t ht x hx
    exact M44.hasDerivAt_pullbackCoefficients_ricci F' isOpen_Ioo hU he hei ht hx
  · let G' := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G
      Ioo_subset_Icc_self ordConnected_Ioo (Ioo_infinite hTb).nontrivial
    intro t ht x hx
    exact M44.hasDerivAt_pullbackCoefficients_ricci G' isOpen_Ioo hU hf hfi ht hx

end PoincareConjecture.M45
