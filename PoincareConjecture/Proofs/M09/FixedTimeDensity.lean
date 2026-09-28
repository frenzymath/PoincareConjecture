import PoincareConjecture.Proofs.M09.BackwardNesting
import PoincareConjecture.Proofs.M09.BoundedMinimizingVectors
import PoincareConjecture.Proofs.M09.MinimizingInitialVectors
import Mathlib.Topology.Order.DenselyOrdered








set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_dense_regular_endpoints {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p)
    (t : ℝ) (ht : 0 < t) (hmax : t < τmax) :
    Dense {q : M | ∃ Z : TangentSpace (𝓡 n) p,
      (Z, t) ∈ A.regularDomain ∧ A.gamma Z t = q} := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) p
  letI : FiniteDimensional ℝ E :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  apply dense_iff_inter_open.mpr
  intro O hO hOne
  obtain ⟨q, hq⟩ := hOne
  obtain ⟨b, htb, hbmax⟩ := exists_between hmax
  let Q := ({q} : Set M) ×ˢ Set.Icc t b
  have hQ : IsCompact Q := isCompact_singleton.prod isCompact_Icc
  have hQt : Q ⊆ Set.univ ×ˢ Set.Ioo 0 τmax := fun z hz ↦
    ⟨Set.mem_univ _, ht.trans_le hz.2.1, hz.2.2.trans_lt hbmax⟩
  obtain ⟨R, _, hR⟩ := lExponentialFamily_minimizing_initial_bounded F hM04 T τmax hτmax
    hwindow hcurvature hL p A Q hQ hQt
  let K := Metric.closedBall (0 : E) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hnear : ∀ᶠ s in 𝓝 t, ∀ Z ∈ K, A.gamma Z t ∈ O ∨ A.gamma Z s ≠ q := by
    apply hK.eventually_forall_of_forall_eventually
    intro Z _
    have hγ : ContinuousAt (fun z : E × ℝ ↦ A.gamma z.1 z.2) (Z, t) :=
      (A.gamma_smooth.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
        ⟨Set.mem_univ _, ht, hmax⟩)).continuousAt
    have hfixed : ContinuousAt (fun z : ℝ × E ↦ A.gamma z.2 t) (t, Z) :=
      ContinuousAt.comp (x := (t, Z)) (f := fun z : ℝ × E ↦ (z.2, t)) hγ
        ((continuous_snd.prodMk continuous_const).continuousAt)
    have hvary : ContinuousAt (fun z : ℝ × E ↦ A.gamma z.2 z.1) (t, Z) :=
      ContinuousAt.comp (x := (t, Z)) (f := fun z : ℝ × E ↦ (z.2, z.1)) hγ
        ((continuous_snd.prodMk continuous_fst).continuousAt)
    by_cases hmem : A.gamma Z t ∈ O
    · filter_upwards [hfixed.preimage_mem_nhds (hO.mem_nhds hmem)] with z hz
      exact Or.inl hz
    · have hne : A.gamma Z t ≠ q := by
        intro heq
        exact hmem (heq.symm ▸ hq)
      filter_upwards [hvary.eventually_ne hne] with z hz
      exact Or.inr hz
  obtain ⟨s, ⟨hsnear, hsb⟩, hts⟩ := nonempty_nhds_inter_Ioi
    (hnear.and (isOpen_Iio.mem_nhds htb)) (not_isMax t)
  have hs : 0 < s := ht.trans hts
  have hsmax : s < τmax := hsb.trans hbmax
  obtain ⟨Z, hend, hmin⟩ := lExponentialFamily_exists_minimizing_initialVector
    hM04 hL hτmax hwindow A s hs hsmax q
  have hendpoint : (A.gamma Z s, s) ∈ Q := by
    exact ⟨Set.mem_singleton_iff.mpr hend, hts.le, hsb.le⟩
  have hnorm : ‖Z‖ ≤ R := by
    rw [norm_eq_sqrt_real_inner]
    exact hR Z s hs hsmax hendpoint hmin
  have hZ : Z ∈ K := by
    simpa only [K, Metric.mem_closedBall, dist_zero_right] using hnorm
  have hOZ : A.gamma Z t ∈ O := (hsnear Z hZ).resolve_right (not_not_intro hend)
  exact ⟨A.gamma Z t, hOZ, Z,
    lExponentialFamily_regularDomain_strict_prefix hM04 hL hτmax hwindow A Z t s ht hts hsmax hmin,
    rfl⟩

end PoincareConjecture.Proofs.M09
