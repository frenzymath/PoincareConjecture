import PoincareConjecture.Proofs.M47.PositiveHistoryOpenness









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47Positive

open PoincareConjecture.M04 Proofs.M46

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [T2Space M] [SecondCountableTopology M]




theorem exists_positive_history_onset {b T : ℝ} (hbT : b < T)
    (F : RicciFlow 3 M (Icc b T))
    (hpos : ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric T) x u v →
        0 < (F.connection T).sectionalCurvature x u v) :
    ∃ a ∈ Ico b T,
      (∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
        0 ≤ (F.connection a).curvatureTensor x u v u v) ∧
      (∀ t ∈ Ioc a T, ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (F.metric t) x u v →
          0 < (F.connection t).sectionalCurvature x u v) ∧
      (∀ t ∈ Ico b a, ¬ (∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (F.metric t) x u v →
          0 < (F.connection t).sectionalCurvature x u v)) ∧
      (a = b ∨ ¬ (∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
        LeviCivitaData.IsOrthonormalPair (F.metric a) x u v →
          0 < (F.connection a).sectionalCurvature x u v)) := by
  classical
  let Pos (t : ℝ) : Prop := ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair (F.metric t) x u v →
      0 < (F.connection t).sectionalCurvature x u v
  let A : Set ℝ := {t | t ∈ Icc b T ∧ Pos t}
  have hTA : T ∈ A := ⟨⟨hbT.le, le_rfl⟩, hpos⟩
  have hne : A.Nonempty := ⟨T, hTA⟩
  have hbelow : BddBelow A := ⟨b, fun _ ht => ht.1.1⟩
  let a := sInf A
  have hba : b ≤ a := le_csInf hne (fun _ ht => ht.1.1)
  obtain ⟨s, hs, hsp⟩ := exists_earlier_positive_time F hbT le_rfl hpos
  have hsa : s ∈ A := ⟨⟨hs.1.le, hs.2.le⟩, hsp⟩
  have haT : a < T := (csInf_le hbelow hsa).trans_lt hs.2
  have hafter : ∀ t ∈ Ioc a T, Pos t := by
    intro t ht
    obtain ⟨r, hr, hrt⟩ := exists_lt_of_csInf_lt hne ht.1
    exact sectional_positive_at_later_time F hr.1
      ⟨hba.trans ht.1.le, ht.2⟩ hrt.le hr.2
  have hbefore : ∀ t ∈ Ico b a, ¬ Pos t := by
    intro t ht htp
    have htA : t ∈ A := ⟨⟨ht.1, ht.2.le.trans haT.le⟩, htp⟩
    exact (not_le_of_gt ht.2) (csInf_le hbelow htA)
  have honset : a = b ∨ ¬ Pos a := by
    by_cases hab : a = b
    · exact Or.inl hab
    · right
      intro hap
      have hba' : b < a := lt_of_le_of_ne hba (Ne.symm hab)
      obtain ⟨r, hr, hrp⟩ := exists_earlier_positive_time F hba' haT.le hap
      exact hbefore r ⟨hr.1.le, hr.2⟩ hrp
  refine ⟨a, ⟨hba, haT⟩, ?_, hafter, hbefore, honset⟩
  obtain ⟨P⟩ := compactSectionalParameters F
  let q : ℝ × P.carrier → ℝ := fun p =>
    (F.connection p.1).curvatureTensor (P.point p.2) (P.left p.2) (P.right p.2)
      (P.left p.2) (P.right p.2) /
      metricGram (F.metric p.1) (P.point p.2) (P.left p.2) (P.right p.2)
  have hgram (t : ℝ) (z : P.carrier) :
      0 < metricGram (F.metric t) (P.point z) (P.left z) (P.right z) :=
    metricGram_pos_of_linearIndependent (F.metric t) _ _ _ (P.independent z)
  have hqpos (t : ℝ) (ht : t ∈ Ioc a T) (z : P.carrier) : 0 < q (t, z) :=
    div_pos (curvature_pair_positive_of_orthonormal (F.connection t) (P.point z)
      (hafter t ht (P.point z)) _ _ (P.independent z)) (hgram t z)
  have hlimit (z : P.carrier) : 0 ≤ q (a, z) := by
    have hqc : ContinuousOn (fun t => q (t, z)) (Icc a T) :=
      P.continuous_quotient.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht => ⟨⟨hba.trans ht.1, ht.2⟩, mem_univ z⟩)
    have hlim : Tendsto (fun t => q (t, z)) (𝓝[>] a) (𝓝 (q (a, z))) :=
      ((hqc a ⟨le_rfl, haT.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE haT)).mono Ioi_subset_Ici_self
    apply ge_of_tendsto hlim
    filter_upwards [Ioc_mem_nhdsGT haT] with t ht
    exact (hqpos t ht z).le
  have hbound := P.complete a 0 (fun z =>
    (le_div_iff₀ (hgram a z)).mp (hlimit z))
  simpa only [zero_mul] using hbound

end PoincareConjecture.M47Positive
