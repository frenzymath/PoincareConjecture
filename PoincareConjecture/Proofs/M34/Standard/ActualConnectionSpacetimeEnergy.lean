import PoincareConjecture.Proofs.M34.Standard.ActualConnectionEnergy
import PoincareConjecture.Proofs.M34.Standard.CanonicalFlowRegularity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M34

open DifferenceEnergy



theorem exists_uniform_actual_connection_spacetime_energy_bound
    {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (V n)) (hU : IsOpen U) (hNE : Nonempty U),
      letI := hNE
      letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ {J J' : Set ℝ} (F : RicciFlow n U J) (F' : RicciFlow n U J')
        (R R' : ℝ → U → FS n),
        (∀ t x u v w, R t x u v w = (F.connection t).curvature x u v w) →
        (∀ t x u v w, R' t x u v w = (F'.connection t).curvature x u v w) →
        ∀ p : U,
          let r := (extChartAt (𝓡 n) p).symm
          let H : ℝ × V n → FH n := fun z =>
            (F.metric z.1).inner (r z.2) - (F'.metric z.1).inner (r z.2)
          let A : ℝ × V n → FA n := fun z => CovariantDerivative.difference
            (F.connection z.1).connection (F'.connection z.1).connection (r z.2)
          let S := fun z : ℝ × V n => R z.1 (r z.2) - R' z.1 (r z.2)
          ∀ t ∈ interior (J ∩ J'), ∀ x ∈ U,
            let B0 := (F.metric t).pullbackCoefficients r
            let B1 := (F'.metric t).pullbackCoefficients r
            (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B0 x‖ ≤ M) →
            (∀ j ≤ 3, ‖iteratedFDeriv ℝ j B1 x‖ ≤ M) →
            (∀ v, a * ‖v‖ ^ 2 ≤ B0 x v v) →
            (∀ v, a * ‖v‖ ^ 2 ≤ B1 x v v) →
            ∀ ε : ℝ, 0 < ε →
              (∑ alpha : Fin dA, 2 * qA (A (t, x)) alpha *
                fderiv ℝ (fun z => qA (A z) alpha) (t, x) (1, 0)) ≤
                ε * (∑ beta : Fin dS × Fin n,
                  (fderiv ℝ (fun y => qS (S (t, y)) beta.1) x
                    (EuclideanSpace.single beta.2 1)) ^ 2) +
                  (C / ε + C) * ((∑ j, qH (H (t, x)) j ^ 2) +
                    (∑ j, qA (A (t, x)) j ^ 2) + (∑ j, qS (S (t, x)) j ^ 2)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_actual_connection_energy_bound qH qA qS ha M
  refine ⟨C, hC, ?_⟩
  intro U hU hNE
  let := hNE
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro J J' F F' R R' hR hR' p r H A S t ht x hx B0 B1 hj0 hj1 he0 he1 ε hε
  have ht0 : t ∈ interior J := interior_mono inter_subset_left ht
  have ht1 : t ∈ interior J' := interior_mono inter_subset_right ht
  have hr : r x = (⟨x, hx⟩ : U) := canonicalOpen_chart_symm_apply hU p ⟨x, hx⟩
  have hmetric : B0 x - B1 x = H (t, x) := by
    dsimp only [H, B0, B1, r]
    rw [canonicalDomain_inner_eq_pullbackCoefficients U hU (F.metric t) p x hx,
      canonicalDomain_inner_eq_pullbackCoefficients U hU (F'.metric t) p x hx]
  have hAc : ContDiffOn (F := FA n) ℝ ∞ A ((J ∩ J') ×ˢ U) :=
    canonicalDomain_contDiffOn_connection_difference U hU qA F F' p
  have hderiv (alpha : Fin dA) :
      deriv (fun s => qA (A (s, x)) alpha) t =
        fderiv ℝ (fun z => qA (A z) alpha) (t, x) (1, 0) := by
    have hc : ContDiffOn ℝ ∞ (fun z => qA (A z) alpha)
        ((interior (J ∩ J')) ×ˢ U) :=
      ((EuclideanSpace.proj alpha : EuclideanSpace ℝ (Fin dA) →L[ℝ] ℝ).contDiff.comp_contDiffOn
        (qA.contDiff.comp_contDiffOn hAc)).mono (Set.prod_mono interior_subset subset_rfl)
    have hd := (hc.differentiableOn (by simp) (t, x) ⟨ht, hx⟩).differentiableAt
      ((isOpen_interior.prod hU).mem_nhds ⟨ht, hx⟩)
    have hs : HasDerivAt (fun s => qA (A (s, x)) alpha)
        (fderiv ℝ (fun z => qA (A z) alpha) (t, x) (1, 0)) t := by
      simpa using! (hd.hasFDerivAt.comp t
        ((hasDerivAt_id t).hasFDerivAt.prodMk (hasDerivAt_const t x).hasFDerivAt)).hasDerivAt
    exact hs.deriv
  have hb := hbound U hU hNE F F' R R' hR hR' t ht0 ht1 p ⟨x, hx⟩
    hj0 hj1 he0 he1 ε hε
  have hApoint (s : ℝ) : CovariantDerivative.difference
      (F.connection s).connection (F'.connection s).connection (⟨x, hx⟩ : U) = A (s, x) := by
    dsimp only [A]
    rw [hr]
  simpa only [hApoint, ← hmetric, hderiv] using hb

end PoincareConjecture.M34
