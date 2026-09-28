import PoincareConjecture.Proofs.M51.InitialUnion
import PoincareConjecture.Proofs.M51.LiteralTranslation
import PoincareConjecture.Proofs.M51.OrdinaryGluing

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Ordinary

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def onEqualDomain {J K : Set ℝ} (F : RicciFlow n M J)
    (hJK : J = K) : RicciFlow n M K := hJK ▸ F

@[simp] theorem onEqualDomain_metric {J K : Set ℝ} (F : RicciFlow n M J)
    (hJK : J = K) (t : ℝ) : (onEqualDomain F hJK).metric t = F.metric t := by
  subst K
  rfl

@[simp] theorem onEqualDomain_curvatureTensorNorm {J K : Set ℝ}
    (F : RicciFlow n M J) (hJK : J = K) (t : ℝ) (x : M) :
    ((onEqualDomain F hJK).connection t).curvatureTensorNorm x =
      (F.connection t).curvatureTensorNorm x := by
  subst K
  rfl

theorem initialDomain_eq_Ici (g0 : RiemannianMetric n M)
    (hA : ¬ BddAbove (initialLifetimes g0)) : initialDomain g0 = Ici 0 := by
  ext t
  constructor
  · exact fun ht => ht.1
  · intro ht
    obtain ⟨T, hT, htT⟩ := not_bddAbove_iff.mp hA t
    exact ⟨ht, T, hT, htT⟩

theorem initialLifetime_sup_pos (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (hA : BddAbove (initialLifetimes g0)) :
    0 < sSup (initialLifetimes g0) := by
  obtain ⟨T, hT⟩ := initialLifetimes_nonempty h03 g0
  exact hT.1.trans_le (le_csSup hA hT)

theorem initialDomain_eq_Ico (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (hA : BddAbove (initialLifetimes g0)) :
    initialDomain g0 = Ico 0 (sSup (initialLifetimes g0)) := by
  ext t
  constructor
  · rintro ⟨ht, T, hT, htT⟩
    exact ⟨ht, htT.trans_le (le_csSup hA hT)⟩
  · intro ht
    obtain ⟨T, hT, htT⟩ :=
      exists_lt_of_lt_csSup (initialLifetimes_nonempty h03 g0) ht.2
    exact ⟨ht.1, T, hT, htT⟩

theorem initialUnion_terminal_curvature (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) (hA : BddAbove (initialLifetimes g0)) :
    ∀ L s : ℝ, s < sSup (initialLifetimes g0) →
      ∃ t ∈ Ioo (max 0 s) (sSup (initialLifetimes g0)), ∃ x : M,
        L < ((initialUnion h03 g0).connection t).curvatureTensorNorm x := by
  intro L s hs
  by_contra h
  push Not at h
  let T := sSup (initialLifetimes g0)
  have hT : 0 < T := initialLifetime_sup_pos h03 g0 hA
  obtain ⟨a, ha, haT⟩ := exists_between (max_lt hT hs)
  have ha0 : 0 < a := (le_max_left 0 s).trans_lt ha
  let F := onEqualDomain (initialUnion h03 g0) (initialDomain_eq_Ico h03 g0 hA)
  have hbound : ∀ t ∈ Ico a T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ L := by
    intro t ht x
    simpa only [F, onEqualDomain_curvatureTensorNorm] using
      h t ⟨ha.trans_le ht.1, ht.2⟩ x
  obtain ⟨δ, hδT, R, hR⟩ := h03.2.2 (T - a) (sub_pos.mpr haT)
    (tail F ha0.le haT) ⟨L, tail_curvature_bound F ha0.le haT hbound⟩
  have hδ : 0 < δ := (sub_pos.mpr haT).trans hδT
  have hTB : T < a + δ := by linarith
  let G := restart R hδ a
  have hmetric : EqOn F.metric G.metric (Ico a T) := by
    intro t ht
    have htime : t - a ∈ Ico 0 (T - a) := ⟨sub_nonneg.mpr ht.1, sub_lt_sub_right ht.2 a⟩
    have hclock : a + (t - a) = t := by linarith
    simpa only [tail_metric, G, restart_metric, hclock] using hR htime
  obtain ⟨c, hac, hcT⟩ := exists_between haT
  let extended := glueOverlap F G c ha0 ⟨hac, hcT⟩ hTB hmetric
  have hinitial : extended.metric 0 = g0 := by
    rw [show extended.metric 0 = F.metric 0 from
      glueOverlap_initial_metric F G c ha0 ⟨hac, hcT⟩ hTB hmetric]
    exact (onEqualDomain_metric _ _ 0).trans (initialUnion_initial_metric h03 g0)
  have hlifetime : a + δ ∈ initialLifetimes g0 :=
    ⟨hT.trans hTB, extended, hinitial⟩
  exact (not_le_of_gt hTB) (le_csSup hA hlifetime)

theorem exists_maximal_initial_flow (h03 : RicciFlowLocalTheory n M)
    (g0 : RiemannianMetric n M) :
    ∃ (J : Set ℝ) (F : RicciFlow n M J),
      IsLeast J 0 ∧ F.metric 0 = g0 ∧
        (J = Ici 0 ∨ ∃ T : ℝ, 0 < T ∧ J = Ico 0 T ∧
          ∀ L s : ℝ, s < T → ∃ t ∈ Ioo (max 0 s) T, ∃ x : M,
            L < (F.connection t).curvatureTensorNorm x) := by
  refine ⟨initialDomain g0, initialUnion h03 g0,
    initialDomain_isLeast h03 g0, initialUnion_initial_metric h03 g0, ?_⟩
  by_cases hA : BddAbove (initialLifetimes g0)
  · exact Or.inr ⟨sSup (initialLifetimes g0), initialLifetime_sup_pos h03 g0 hA,
      initialDomain_eq_Ico h03 g0 hA, initialUnion_terminal_curvature h03 g0 hA⟩
  · exact Or.inl (initialDomain_eq_Ici g0 hA)

end PoincareConjecture.M51Ordinary
