import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_CompactPhaseContinuation










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}



theorem exponential_survival_of_confined_open_phase
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z : G.Horizontal x)
    {b : ℝ} (hb : 0 < b) (hbtime : T - b ^ 2 ∈ I.domain)
    {K : Set G.Point} (hK : IsCompact K) (C : ℝ)
    (hbound : ∀ s ∈ Ioo 0 b, (Z, s) ∈ E.domain →
      (exponentialPhase E Z s).proj ∈ K ∧
        G.spacetime.horizontalMetric.inner (exponentialPhase E Z s).proj
          (exponentialPhase E Z s).2 (exponentialPhase E Z s).2 ≤ C) :
    (Z, b) ∈ E.domain := by
  let S : Set (Icc (0 : ℝ) b) := {s | (Z, s.val) ∈ E.domain}
  have hT : T ∈ I.domain := by
    rw [← G.spacetime.time_range]
    exact ⟨x, E.base_time⟩
  have htime := M14.squareClock_admissible_prefix hT hb.le hbtime
  have hopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨U, hU, hsU, hsub⟩ := E.domain_relative_open (Z, s.val) hs
    have hnear : {t : Icc (0 : ℝ) b | (Z, t.val) ∈ U} ∈ 𝓝 s :=
      (hU.preimage (continuous_const.prodMk continuous_subtype_val)).mem_nhds hsU
    apply mem_of_superset hnear
    intro t ht
    exact hsub ⟨ht, t.property.1, htime t.val t.property⟩
  have hclosed : IsClosed S := by
    apply IsSeqClosed.isClosed
    intro u s hu hlimit
    by_cases hs0 : s.val = 0
    · change (Z, s.val) ∈ E.domain
      rw [hs0]
      exact E.domain_zero Z
    have hs : 0 < s.val := lt_of_le_of_ne s.property.1 (Ne.symm hs0)
    by_cases hlater : ∃ k, s.val ≤ (u k).val
    · obtain ⟨k, hk⟩ := hlater
      exact (E.maximal_lifetime Z).out (E.domain_zero Z) (hu k) ⟨s.property.1, hk⟩
    have hbefore (k : ℕ) : (u k).val < s.val :=
      lt_of_not_ge (fun hk => hlater ⟨k, hk⟩)
    have hsk : Tendsto (fun k => (u k).val) atTop (𝓝 s.val) :=
      continuous_subtype_val.continuousAt.tendsto.comp hlimit
    have hbelow : ∀ᶠ k in atTop, 0 < (u k).val ∧ (u k).val < s.val :=
      (hsk.eventually (Ioi_mem_nhds hs)).and (Eventually.of_forall hbefore)
    have hphase : ∀ᶠ k in atTop,
        (exponentialPhase E Z (u k).val).proj ∈ K ∧
          G.spacetime.horizontalMetric.inner (exponentialPhase E Z (u k).val).proj
            (exponentialPhase E Z (u k).val).2 (exponentialPhase E Z (u k).val).2 ≤ C := by
      filter_upwards [hbelow] with k hk
      exact hbound (u k).val ⟨hk.1, hk.2.trans_le s.property.2⟩ (hu k)
    obtain ⟨z, _, hcluster⟩ := (isCompact_horizontalDisk G hK C).exists_mapClusterPt
      (tendsto_principal.mpr hphase)
    obtain ⟨r, hsr, _, hsurv⟩ := exponential_survival_of_phase_cluster hM04 hM12 E Z
      hs hsk (fun k => hu k) hbelow z hcluster
    exact (E.maximal_lifetime Z).out (E.domain_zero Z) hsurv ⟨s.property.1, hsr⟩
  let : PreconnectedSpace (Icc (0 : ℝ) b) := Subtype.preconnectedSpace isPreconnected_Icc
  have hSuniv : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ
    ⟨⟨0, le_rfl, hb.le⟩, E.domain_zero Z⟩
  exact (Set.ext_iff.mp hSuniv ⟨b, hb.le, le_rfl⟩).mpr (mem_univ _)




theorem exponential_survival_of_varying_phase_limit
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {b : ℝ} (hb : 0 < b)
    (hbtime : T - b ^ 2 ∈ I.domain)
    {Zk : ℕ → G.Horizontal x} {Z : G.Horizontal x} (hZk : Tendsto Zk atTop (𝓝 Z))
    {bk : ℕ → ℝ} (hbk : Tendsto bk atTop (𝓝 b)) (hbkpos : ∀ k, 0 < bk k)
    (hsurv : ∀ k, (Zk k, bk k) ∈ E.domain)
    {K : Set G.Point} (hK : IsCompact K) (C : ℝ)
    (hcurve : ∀ k s, s ∈ Icc 0 (bk k) → E.gamma (Zk k) s ∈ K)
    (hspeed : ∀ k s, s ∈ Icc 0 (bk k) →
      G.spacetime.horizontalMetric.inner
        ((E.square_path (Zk k) (bk k) (hsurv k) (hbkpos k)).curve s)
        ((E.square_path (Zk k) (bk k) (hsurv k) (hbkpos k)).horizontal_velocity s)
        ((E.square_path (Zk k) (bk k) (hsurv k) (hbkpos k)).horizontal_velocity s) ≤ C) :
    (Z, b) ∈ E.domain := by
  apply exponential_survival_of_confined_open_phase hM04 hM12 E Z hb hbtime hK C
  intro s hs hZ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hbk.eventually (Ioi_mem_nhds hs.2))
  have hsb (k : ℕ) : s ≤ bk (k + N) := (hN (k + N) (Nat.le_add_left N k)).le
  have hprefix (k : ℕ) : (Zk (k + N), s) ∈ E.domain :=
    (E.maximal_lifetime (Zk (k + N))).out (E.domain_zero (Zk (k + N)))
      (hsurv (k + N)) ⟨hs.1.le, hsb k⟩
  apply exponentialPhase_mem_compactDisk_of_tendsto E hK C
    (hZk.comp (tendsto_add_atTop_nat N)) hs.1 hZ hprefix
  intro k
  let disk : Set (TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal) :=
    {z | z.proj ∈ K ∧ G.spacetime.horizontalMetric.inner z.proj z.2 z.2 ≤ C}
  change exponentialPhase E (Zk (k + N)) s ∈ disk
  rw [exponentialPhase_eq_squarePath_of_le E (hsurv (k + N)) (hbkpos (k + N)) hs.1 (hsb k)]
  refine ⟨?_, hspeed (k + N) s ⟨hs.1.le, hsb k⟩⟩
  change (E.square_path (Zk (k + N)) (bk (k + N)) (hsurv (k + N)) (hbkpos (k + N))).curve s ∈ K
  rw [M14.exponential_square_curve_eq E (Zk (k + N)) (hsurv (k + N)) (hbkpos (k + N))
    (by simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq (hbkpos (k + N)).le]
      using (show s ∈ Icc 0 (bk (k + N)) from ⟨hs.1.le, hsb k⟩))]
  exact hcurve (k + N) s ⟨hs.1.le, hsb k⟩

end PoincareConjecture.Proofs.M46
