import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2Locality
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.SliceCongruence












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}





theorem c2_exists_closed_of_uniform_curvature (hlocal : M63LocalCurveTheory F)
    (gamma : ℝ → M) (hper : Function.Periodic gamma curvePeriod)
    (hreg : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 gamma)
    (himm : ∀ x, curveVelocity (n := n) gamma x ≠ 0) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ T, a < T → T ≤ b → ∀ c : ℝ → ℝ → M,
      M63C2ShrinkingCurveOn F c (Icc a T) → (∀ x, c x a = gamma x) →
        ∀ t ∈ Icc a T, ∀ x, m62Curvature F c t x ≤ K) :
    ∃ c : ℝ → ℝ → M, M63C2ShrinkingCurveOn F c (Icc a b) ∧
      (∀ x, c x a = gamma x) ∧ M63IntrinsicRegularityOn F c (Icc a b) := by
  classical
  let E : Set ℝ := {s | a < s ∧ s ≤ b ∧ ∃ c : ℝ → ℝ → M,
    M63C2ShrinkingCurveOn F c (Icc a s) ∧ ∀ x, c x a = gamma x}
  obtain ⟨T0, hT0, hT0b, c0, hc0, hinit0, _⟩ :=
    hlocal.local_existence gamma hper hreg himm
  have hE0 : T0 ∈ E := ⟨hT0, hT0b, c0, hc0, hinit0⟩
  have hne : E.Nonempty := ⟨T0, hE0⟩
  have hbd : BddAbove E := ⟨b, fun s hs => hs.2.1⟩
  let T := sSup E
  have haT : a < T := hT0.trans_le (le_csSup hbd hE0)
  have hTb : T ≤ b := csSup_le hne (fun s hs => hs.2.1)
  choose C hC hinit using (fun s : E => s.property.2.2)
  have hagree (s r : E) (t : ℝ) (ht : t ∈ Icc a (min (s : ℝ) (r : ℝ))) :
      ∀ x, C s x t = C r x t :=
    hlocal.unique_closed (min (s : ℝ) (r : ℝ)) (lt_min s.property.1 r.property.1)
      ((min_le_left _ _).trans s.property.2.1) (C s) (C r)
      (c2_restrict (hC s) (Icc_subset_Icc le_rfl (min_le_left _ _)))
      (c2_restrict (hC r) (Icc_subset_Icc le_rfl (min_le_right _ _)))
      (fun x => (hinit s x).trans (hinit r x).symm) t ht
  have habove (t : ℝ) (ht : t ∈ Ico a T) : ∃ s : E, t < (s : ℝ) := by
    obtain ⟨s, hs, hts⟩ := (lt_csSup_iff hbd hne).mp ht.2
    exact ⟨⟨s, hs⟩, hts⟩
  choose endpoint hendpoint using habove
  let c (x t : ℝ) : M := if ht : t ∈ Ico a T then C (endpoint t ht) x t else gamma x
  have hcompare (s : E) (t : ℝ) (ht : t ∈ Ico a T) (hts : t ≤ (s : ℝ)) :
      ∀ x, c x t = C s x t := by
    intro x
    dsimp only [c]
    rw [dif_pos ht]
    exact hagree (endpoint t ht) s t ⟨ht.1, le_min (hendpoint t ht).le hts⟩ x
  have hcinit (x : ℝ) : c x a = gamma x :=
    (hcompare ⟨T0, hE0⟩ a ⟨le_rfl, haT⟩ hT0.le x).trans (hinit ⟨T0, hE0⟩ x)
  have hc : M63C2ShrinkingCurveOn F c (Ico a T) := by
    apply c2_of_closed_prefixes
    intro t ht
    let s := endpoint t ht
    obtain ⟨r, htr, hrs⟩ := exists_between (hendpoint t ht)
    have hsT : (s : ℝ) ≤ T := le_csSup hbd s.property
    have hrT : r < T := hrs.trans_le hsT
    refine ⟨r, htr, hrT, ?_⟩
    apply c2_congr (c2_restrict (hC s) (Icc_subset_Icc le_rfl hrs.le))
    exact fun y hy => hcompare s y ⟨hy.1, hy.2.trans_lt hrT⟩ (hy.2.trans hrs.le)
  have hcurvature (t : ℝ) (ht : t ∈ Ico a T) (x : ℝ) :
      m62Curvature F c t x ≤ K := by
    let s := endpoint t ht
    rw [curvature_congr_slice F (hcompare s t ht (hendpoint t ht).le)]
    exact hbound s s.property.1 s.property.2.1 (C s) (hC s) (hinit s)
      t ⟨ht.1, (hendpoint t ht).le⟩ x
  obtain ⟨T', hTT', hT'b, hstrict, d, hd, hdc⟩ :=
    hlocal.continuation T haT hTb c hc K hK hcurvature
  have hdinit (x : ℝ) : d x a = gamma x :=
    (hdc a ⟨le_rfl, haT⟩ x).trans (hcinit x)
  have hT'E : T' ∈ E := ⟨haT.trans_le hTT', hT'b, d, hd, hdinit⟩
  have hT'T : T' ≤ T := le_csSup hbd hT'E
  have hTeq : T = b := by
    apply le_antisymm hTb
    by_contra! h
    exact (not_lt_of_ge hT'T) (hstrict h)
  have hT'eq : T' = b := le_antisymm hT'b (hTeq ▸ hTT')
  have hdfull : M63C2ShrinkingCurveOn F d (Icc a b) := hT'eq ▸ hd
  exact ⟨d, hdfull, hdinit,
    hlocal.intrinsic_regularity b (haT.trans_le hTb) le_rfl
      (Icc a b) (Or.inl rfl) d hdfull⟩

end PoincareConjecture.M63
