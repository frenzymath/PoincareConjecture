import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveSectionalLowerBound

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.M04

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in

theorem exists_initial_sectional_lower [CompactSpace M]
    (F : RicciFlow 3 M J) {a : ℝ} (ha : a ∈ J)
    {S : Set M} (hS : IsClosed S)
    (hpos : ∀ y ∈ S, ∀ u v : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (F.metric a) y u v →
        0 < (F.connection a).sectionalCurvature y u v) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ S, ∀ u v : TangentSpace (𝓡 3) y,
      c * metricGram (F.metric a) y u v ≤ (F.connection a).curvatureTensor y u v u v := by
  classical
  obtain ⟨P⟩ := compactSectionalParameters F
  let C := P.point ⁻¹' S
  let : CompactSpace C :=
    isCompact_iff_compactSpace.mp (hS.preimage P.point_continuous).isCompact
  let q : C → ℝ := fun z =>
    (F.connection a).curvatureTensor (P.point z.1) (P.left z.1) (P.right z.1)
      (P.left z.1) (P.right z.1) /
      metricGram (F.metric a) (P.point z.1) (P.left z.1) (P.right z.1)
  have hG (z : C) :
      0 < metricGram (F.metric a) (P.point z.1) (P.left z.1) (P.right z.1) :=
    metricGram_pos_of_linearIndependent (F.metric a) _ _ _ (P.independent z.1)
  have hqc : Continuous q := P.continuous_quotient.comp_continuous
    (continuous_const.prodMk continuous_subtype_val) (fun z => ⟨ha, mem_univ z.1⟩)
  have hqpos (z : C) : 0 < q z := div_pos
    (curvature_pair_positive_of_orthonormal (F.connection a) (P.point z.1)
      (hpos _ z.2) _ _ (P.independent z.1)) (hG z)
  by_cases hC : Nonempty C
  · let : Nonempty C := hC
    obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set C).Nonempty)
      hqc.continuousOn
    refine ⟨q z, hqpos z, P.complete_on S a (q z) ?_⟩
    intro w hw
    exact (le_div_iff₀ (hG ⟨w, hw⟩)).mp (hz (mem_univ ⟨w, hw⟩))
  · have : IsEmpty C := not_nonempty_iff.mp hC
    refine ⟨1, zero_lt_one, P.complete_on S a 1 ?_⟩
    intro z hz
    exact isEmptyElim (⟨z, hz⟩ : C)

def zeroBasedOrdinaryRestriction (F : RicciFlow 3 M J)
    {a b : ℝ} (hab : a < b) (hI : Icc a b ⊆ J) : RicciFlow 3 M (Icc 0 (b - a)) where
  metric s := F.metric (a + s)
  connection s := F.connection (a + s)
  interval := ordConnected_Icc
  nontrivial := ⟨0, ⟨le_rfl, (sub_pos.mpr hab).le⟩,
    b - a, ⟨(sub_pos.mpr hab).le, le_rfl⟩, (sub_pos.mpr hab).ne⟩
  smooth := by
    have hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
        (fun p : ℝ × M => (a + p.1, p.2)) :=
      (contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd
    exact F.smooth.comp hs.contMDiffOn (fun p hp =>
      ⟨hI ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, mem_univ _⟩)
  equation s hs x u v := by
    have htime : a + s ∈ J := hI ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hshift : HasDerivWithinAt (fun t : ℝ => a + t) 1 (Icc 0 (b - a)) s := by
      simpa only [id_eq] using ((hasDerivAt_id s).const_add a).hasDerivWithinAt
    have h := (F.equation (a + s) htime x u v).comp s hshift
      (fun t ht => hI ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    convert! h using 1
    simp only [mul_one]

theorem sectional_lower_on_closed_interval
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (F : RicciFlow 3 M J) {a b c : ℝ} (hab : a < b) (hc : 0 ≤ c)
    (hI : Icc a b ⊆ J) {S : Set M} (hSopen : IsOpen S) (hSclosed : IsClosed S)
    (hinit : ∀ y ∈ S, ∀ u v : TangentSpace (𝓡 3) y,
      c * metricGram (F.metric a) y u v ≤ (F.connection a).curvatureTensor y u v u v) :
    ∀ t ∈ Icc a b, ∀ y ∈ S, ∀ u v : TangentSpace (𝓡 3) y,
      c * metricGram (F.metric t) y u v ≤ (F.connection t).curvatureTensor y u v u v := by
  let F0 := zeroBasedOrdinaryRestriction F hab hI
  have hi : ∀ y ∈ S, ∀ u v : TangentSpace (𝓡 3) y,
      c * metricGram (F0.metric 0) y u v ≤ (F0.connection 0).curvatureTensor y u v u v := by
    change ∀ y ∈ S, ∀ u v : TangentSpace (𝓡 3) y,
      c * metricGram (F.metric (a + 0)) y u v ≤
        (F.connection (a + 0)).curvatureTensor y u v u v
    exact (congrArg (fun t => ∀ y ∈ S, ∀ u v : TangentSpace (𝓡 3) y,
      c * metricGram (F.metric t) y u v ≤ (F.connection t).curvatureTensor y u v u v)
      (add_zero a)).mpr hinit
  intro t ht y hy u v
  have h := clopen_sectional_lower_preserved (sub_pos.mpr hab) hc F0 hSopen hSclosed
    hi (t - a) ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 a⟩ y hy u v
  have heq : a + (t - a) = t := by ring
  change c * metricGram (F.metric (a + (t - a))) y u v ≤
    (F.connection (a + (t - a))).curvatureTensor y u v u v at h
  rwa [heq] at h

theorem positive_sectional_uniform_on_component
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (F : RicciFlow 3 M J) {a : ℝ} (ha : a ∈ J) (x : M)
    (hpos : ∀ y ∈ connectedComponent x, ∀ u v : TangentSpace (𝓡 3) y,
      LeviCivitaData.IsOrthonormalPair (F.metric a) y u v →
        0 < (F.connection a).sectionalCurvature y u v) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ J, a ≤ t → ∀ y ∈ connectedComponent x,
      ∀ u v : TangentSpace (𝓡 3) y,
        c * metricGram (F.metric t) y u v ≤ (F.connection t).curvatureTensor y u v u v := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 3)) M
  have hC := isClopen_connectedComponent (x := x)
  obtain ⟨c, hc, hinit⟩ := exists_initial_sectional_lower F ha hC.isClosed hpos
  refine ⟨c, hc, ?_⟩
  intro t ht hat
  rcases lt_or_eq_of_le hat with hlt | rfl
  · exact sectional_lower_on_closed_interval F hlt hc.le
      (F.interval.out ha ht) hC.isOpen hC.isClosed hinit t ⟨hat, le_rfl⟩
  · exact hinit

end PoincareConjecture.Proofs.M46
