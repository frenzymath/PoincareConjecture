import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveSectionalContinuation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47Positive

open PoincareConjecture.M04 Proofs.M46

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] {J : Set ℝ}



theorem sectional_positive_eventually (F : RicciFlow 3 M J)
    {t : ℝ} (ht : t ∈ J)
    (hpos : ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric t) x u v →
        0 < (F.connection t).sectionalCurvature x u v) :
    ∀ᶠ s in 𝓝[J] t, ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric s) x u v →
        0 < (F.connection s).sectionalCurvature x u v := by
  obtain ⟨c, hc, hmin⟩ := exists_initial_sectional_lower F ht isClosed_univ
    (fun x _ => hpos x)
  obtain ⟨P⟩ := compactSectionalParameters F
  let q : ℝ × P.carrier → ℝ := fun p =>
    (F.connection p.1).curvatureTensor (P.point p.2) (P.left p.2) (P.right p.2)
      (P.left p.2) (P.right p.2) /
      metricGram (F.metric p.1) (P.point p.2) (P.left p.2) (P.right p.2)
  have hgram (s : ℝ) (z : P.carrier) :
      0 < metricGram (F.metric s) (P.point z) (P.left z) (P.right z) :=
    metricGram_pos_of_linearIndependent (F.metric s) _ _ _ (P.independent z)
  have hq (z : P.carrier) : c ≤ q (t, z) :=
    (le_div_iff₀ (hgram t z)).mpr (hmin _ (mem_univ _) _ _)
  have hprod : ∀ᶠ p : ℝ × P.carrier in (𝓝[J] t) ×ˢ 𝓝ˢ (univ : Set P.carrier),
      c / 2 < q p := by
    apply isCompact_univ.mem_prod_nhdsSet_of_forall
    intro z _
    have hnear := (P.continuous_quotient (t, z) ⟨ht, mem_univ z⟩).eventually
      (Ioi_mem_nhds ((half_lt_self hc).trans_le (hq z)))
    simp only [nhdsWithin_prod_eq, nhdsWithin_univ] at hnear
    convert! hnear using 1
  have hnear : ∀ᶠ s in 𝓝[J] t, ∀ z : P.carrier, c / 2 < q (s, z) :=
    hprod.curry.mono (fun _ hs z => hs.self_of_nhdsSet z (mem_univ z))
  filter_upwards [hnear] with s hs x u v huv
  have h := P.complete s (c / 2) (fun z =>
    (le_div_iff₀ (hgram s z)).mp (hs z).le) x u v
  have hcuv : c / 2 ≤ (F.connection s).curvatureTensor x u v u v := by
    simpa [metricGram, huv.1, huv.2.1, huv.2.2] using h
  have hcurv := (half_pos hc).trans_le hcuv
  simpa [LeviCivitaData.sectionalCurvature, huv.1, huv.2.1, huv.2.2] using hcurv



theorem sectional_positive_at_later_time [T2Space M] [SecondCountableTopology M]
    (F : RicciFlow 3 M J) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t)
    (hpos : ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric s) x u v →
        0 < (F.connection s).sectionalCurvature x u v) :
    ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric t) x u v →
        0 < (F.connection t).sectionalCurvature x u v := by
  rcases lt_or_eq_of_le hst with hst | rfl
  · obtain ⟨c, hc, hmin⟩ := exists_initial_sectional_lower F hs isClosed_univ
      (fun x _ => hpos x)
    have hbound := sectional_lower_on_closed_interval F hst hc.le
      (F.interval.out hs ht) isOpen_univ isClosed_univ hmin t ⟨hst.le, le_rfl⟩
    intro x u v huv
    have hcuv : c ≤ (F.connection t).curvatureTensor x u v u v := by
      simpa [metricGram, huv.1, huv.2.1, huv.2.2] using hbound x (mem_univ x) u v
    have hcurv := hc.trans_le hcuv
    simpa [LeviCivitaData.sectionalCurvature, huv.1, huv.2.1, huv.2.2] using hcurv
  · exact hpos



theorem exists_earlier_positive_time {a b t : ℝ}
    (F : RicciFlow 3 M (Icc a b)) (hat : a < t) (htb : t ≤ b)
    (hpos : ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric t) x u v →
        0 < (F.connection t).sectionalCurvature x u v) :
    ∃ s ∈ Ioo a t, ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric s) x u v →
        0 < (F.connection s).sectionalCurvature x u v := by
  have hnear := sectional_positive_eventually F ⟨hat.le, htb⟩ hpos
  have hdom : Icc a b ∈ 𝓝[<] t := by
    filter_upwards [Ioo_mem_nhdsLT hat] with s hs
    exact ⟨hs.1.le, hs.2.le.trans htb⟩
  have hnear' := hnear.filter_mono (nhdsWithin_le_of_mem hdom)
  obtain ⟨s, hs, hsp⟩ := (Filter.Eventually.and (Ioo_mem_nhdsLT hat) hnear').exists
  exact ⟨s, hs, hsp⟩

end PoincareConjecture.M47Positive
