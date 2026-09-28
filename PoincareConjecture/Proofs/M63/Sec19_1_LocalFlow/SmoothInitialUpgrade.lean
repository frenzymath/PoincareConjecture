import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothUpgradeFixedLabels
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothLocalExistence
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessFields
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.FixedRelabelingAssembly

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem c2ShrinkingCurve_smooth_of_smooth_initial [T2Space M]
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {T : ℝ} (haT : a < T) (_hTb : T ≤ b) {J : Set ℝ}
    (hJ : J = Icc a T ∨ J = Ico a T) {c : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c J)
    (hi : M63IntrinsicRegularityOn F c J)
    (hinitial : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c x a)) :
    M63SmoothShrinkingCurveOn F c J := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  let : Nonempty M := ⟨c 0 a⟩
  have haJ : a ∈ J := by
    rcases hJ with rfl | rfl
    · exact ⟨le_rfl, haT.le⟩
    · exact ⟨le_rfl, haT⟩
  have hint : interior J = Ioo a T := by
    rcases hJ with rfl | rfl
    · exact interior_Icc
    · exact interior_Ico
  have hsub {r s : ℝ} (har : a ≤ r) (hsT : s < T) : Icc r s ⊆ J := by
    rcases hJ with rfl | rfl
    · intro t ht
      exact ⟨har.trans ht.1, ht.2.trans hsT.le⟩
    · intro t ht
      exact ⟨har.trans ht.1, ht.2.trans_lt hsT⟩
  obtain ⟨T0, haT0, _hT0b, c0, hc0, hinit0, _hi0, _hjoint0⟩ :=
    exists_smooth_local_curve F (fun x => c x a) (hc.periodic a haJ)
      hinitial (hc.immersed a haJ)
  let L : ℝ := (a + min T T0) / 2
  have ham : a < min T T0 := lt_min haT haT0
  have haL : a < L := by dsimp only [L]; linarith
  have hLm : L < min T T0 := by dsimp only [L]; linarith
  have hLT : L < T := hLm.trans_le (min_le_left _ _)
  have hLT0 : L < T0 := hLm.trans_le (min_le_right _ _)
  have hsame : ∀ t ∈ Icc a L, ∀ x, c x t = c0 x t :=
    c2ShrinkingCurve_unique_closed F hcompact (c2_restrict hc (hsub le_rfl hLT))
      (c2_restrict hc0.1 (fun t ht => ⟨ht.1, ht.2.trans hLT0.le⟩))
      (fun x => (hinit0 x).symm)
  have hslice (tau : ℝ) (htau : tau ∈ Ioo a L) :
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c x tau) := by
    have hs0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c0 x tau) :=
      hc0.2.comp_contMDiff (contDiff_id.prodMk contDiff_const).contMDiff
        (fun x => ⟨mem_univ x, by
          rw [interior_Icc]
          exact ⟨htau.1, htau.2.trans hLT0⟩⟩)
    exact hs0.congr (fun x => hsame tau ⟨htau.1.le, htau.2.le⟩ x)
  obtain ⟨N, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := 𝓡 n) (M := M)
  obtain ⟨U, ρ, hU, heU, hρ, hρe, _hmin, _huniq⟩ :=
    exists_smooth_compact_embedded_retraction e hemb he hinj
  refine ⟨hc, ?_⟩
  intro z hz
  have ht : z.2 ∈ Ioo a T := by simpa only [hint] using hz.2
  let tau : ℝ := (a + min L z.2) / 2
  let s : ℝ := (z.2 + T) / 2
  have hamt : a < min L z.2 := lt_min haL ht.1
  have hat : a < tau := by dsimp only [tau]; linarith
  have htm : tau < min L z.2 := by dsimp only [tau]; linarith
  have htL : tau < L := htm.trans_le (min_le_left _ _)
  have htt : tau < z.2 := htm.trans_le (min_le_right _ _)
  have hts : z.2 < s := by dsimp only [s]; linarith [ht.2]
  have hsT : s < T := by dsimp only [s]; linarith [ht.2]
  have htaus : tau < s := htt.trans hts
  have hslab : Icc tau s ⊆ J := hsub hat.le hsT
  obtain ⟨phi, d, hphi, _hbij, _hpos, _hshift, hd, hdslices, hrel⟩ :=
    exists_fixed_smooth_relabeling F hcompact hc hi hat htaus hslab
  have hanchor : tau ∈ Icc tau s := ⟨le_rfl, htaus.le⟩
  obtain ⟨_hphis, hsmooth⟩ := smoothShrinkingCurve_of_fixed_relabeling_and_smooth_slice
    F he hU heU hρ hρe hanchor (c2_restrict hc hslab) hd
    (hslice tau ⟨hat, htL⟩) (hdslices tau hanchor) hphi.continuous hrel
  have hlocal : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => c z.1 z.2) (univ ×ˢ Ioo tau s) := by
    simpa only [interior_Icc] using hsmooth.2
  exact (hlocal.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    ⟨mem_univ _, htt, hts⟩)).contMDiffWithinAt

end PoincareConjecture.M63
