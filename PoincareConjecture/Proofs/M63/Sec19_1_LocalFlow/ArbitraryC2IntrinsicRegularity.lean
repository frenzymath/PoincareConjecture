import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.IntrinsicClosedPrefix
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.IntrinsicRestartPrefix
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.IntrinsicC2LocalExistence
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessFields
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem c2ShrinkingCurve_intrinsic_regularity
    [T2Space M] (F : RicciFlow n M (Icc a b))
    (hcompact : IsCompact (univ : Set M))
    {T : ℝ} (haT : a < T) (hTb : T ≤ b)
    {J : Set ℝ} (hJ : J = Icc a T ∨ J = Ico a T)
    {c : ℝ → ℝ → M} (hc : M63C2ShrinkingCurveOn F c J) :
    M63IntrinsicRegularityOn F c J := by
  classical
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  have restrict {d : ℝ → ℝ → M} {K L : Set ℝ}
      (hi : M63IntrinsicRegularityOn F d K) (hsub : L ⊆ K) :
      M63IntrinsicRegularityOn F d L :=
    { interior_jets := fun i =>
        (hi.interior_jets i).mono (prod_mono Subset.rfl (interior_mono hsub))
      closed_positive_jets := fun r s har hrs hrsL i =>
        hi.closed_positive_jets r s har hrs (hrsL.trans hsub) i }
  have freeze (d : ℝ → ℝ → M) (i : ℕ) (t : ℝ) :
      (fun x => m63CurvatureJet F d i t x) =
        (fun x => m63CurvatureJet F (fun y _ => d y t) i t x) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      funext x
      change m62SpatialDerivative F d t (fun y => m63CurvatureJet F d i t y) x =
        m62SpatialDerivative F (fun y _ => d y t) t
          (fun y => m63CurvatureJet F (fun z _ => d z t) i t y) x
      rw [ih]
      rfl
  have bundleFreeze (d : ℝ → ℝ → M) (i : ℕ) (t x : ℝ) :
      (⟨d x t, m63CurvatureJet F d i t x⟩ : TangentBundle (𝓡 n) M) =
        (⟨d x t, m63CurvatureJet F (fun y _ => d y t) i t x⟩ :
          TangentBundle (𝓡 n) M) := by rw [congrFun (freeze d i t) x]
  have congrCurve {d : ℝ → ℝ → M} {K : Set ℝ}
      (hi : M63IntrinsicRegularityOn F d K) (heq : ∀ t ∈ K, ∀ x, c x t = d x t) :
      M63IntrinsicRegularityOn F c K := by
    have hb (i : ℕ) (t : ℝ) (ht : t ∈ K) (x : ℝ) :
        (⟨c x t, m63CurvatureJet F c i t x⟩ : TangentBundle (𝓡 n) M) =
          (⟨d x t, m63CurvatureJet F d i t x⟩ : TangentBundle (𝓡 n) M) :=
      (bundleFreeze c i t x).trans
        ((congrArg (fun gamma : ℝ → M =>
          (⟨gamma x, m63CurvatureJet F (fun y _ => gamma y) i t x⟩ :
            TangentBundle (𝓡 n) M)) (funext (heq t ht))).trans
              (bundleFreeze d i t x).symm)
    exact
      { interior_jets := fun i => (hi.interior_jets i).congr
          (fun z hz => hb i z.2 (interior_subset hz.2) z.1)
        closed_positive_jets := fun r s har hrs hsub i =>
          (hi.closed_positive_jets r s har hrs hsub i).congr
            (fun z hz => hb i z.2 (hsub hz.2) z.1) }
  have fromPrefixes {S : ℝ}
      (hprefix : ∀ t ∈ Ico a S, ∃ r, t < r ∧
        M63IntrinsicRegularityOn F c (Icc a r)) :
      M63IntrinsicRegularityOn F c (Ico a S) := by
    refine ⟨?_, ?_⟩
    · intro i
      rw [interior_Ico]
      apply contMDiffOn_of_locally_contMDiffOn
      intro z hz
      obtain ⟨r, htr, hi⟩ := hprefix z.2 (Ioo_subset_Ico_self hz.2)
      refine ⟨univ ×ˢ Iio r, isOpen_univ.prod isOpen_Iio, ⟨mem_univ _, htr⟩, ?_⟩
      apply (hi.interior_jets i).mono
      rw [interior_Icc]
      exact fun y hy => ⟨mem_univ _, hy.1.2.1, hy.2.2⟩
    · intro r s har hrs hsub i
      obtain ⟨v, hsv, hi⟩ := hprefix s (hsub ⟨hrs, le_rfl⟩)
      exact hi.closed_positive_jets r s har hrs
        (fun u hu => ⟨har.le.trans hu.1, hu.2.trans hsv.le⟩) i
  have closed {T0 : ℝ} (haT0 : a < T0) (hT0b : T0 ≤ b)
      (hc0 : M63C2ShrinkingCurveOn F c (Icc a T0)) :
      M63IntrinsicRegularityOn F c (Icc a T0) := by
    let E : Set ℝ := {r | a < r ∧ r ≤ T0 ∧ M63IntrinsicRegularityOn F c (Icc a r)}
    have hE : E.Nonempty := by
      have ha : a ∈ Icc a T0 := ⟨le_rfl, haT0.le⟩
      obtain ⟨R, haR, _hRb, d, hd, hinit, hi⟩ :=
        exists_intrinsic_c2_local_curve F (fun x => c x a)
          (hc0.periodic a ha) (hc0.spatial_regular a ha) (hc0.immersed a ha)
      let r := min T0 R
      have har : a < r := lt_min haT0 haR
      have hrc : Icc a r ⊆ Icc a T0 := Icc_subset_Icc_right (min_le_left _ _)
      have hrd : Icc a r ⊆ Icc a R := Icc_subset_Icc_right (min_le_right _ _)
      have heq := c2ShrinkingCurve_unique_closed F hcompact
        (c2_restrict hc0 hrc) (c2_restrict hd hrd) (fun x => (hinit x).symm)
      exact ⟨r, har, min_le_left _ _, congrCurve (restrict hi hrd) heq⟩
    have hbounded : BddAbove E := ⟨T0, fun r hr => hr.2.1⟩
    let S := sSup E
    have haS : a < S := by
      obtain ⟨r, hr⟩ := hE
      exact hr.1.trans_le (le_csSup hbounded hr)
    have hST : S ≤ T0 := csSup_le hE (fun r hr => hr.2.1)
    have hiOpen : M63IntrinsicRegularityOn F c (Ico a S) := by
      apply fromPrefixes
      intro t ht
      obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup hE ht.2
      exact ⟨r, htr, hr.2.2⟩
    have hcS : M63C2ShrinkingCurveOn F c (Icc a S) :=
      c2_restrict hc0 (Icc_subset_Icc_right hST)
    have hiS := (intrinsic_closed_prefix_of_half_open F hcompact haS
      (hST.trans hT0b) hcS hiOpen).1
    have hTS : T0 ≤ S := by
      by_contra! hlt
      obtain ⟨S', hSS', hS'T, hiS'⟩ :=
        exists_larger_intrinsic_closed_prefix F hcompact haS hlt hT0b hc0 hiS
      have hmem : S' ∈ E := ⟨haS.trans hSS', hS'T, hiS'⟩
      exact (not_lt_of_ge (le_csSup hbounded hmem)) hSS'
    have hSTeq : S = T0 := le_antisymm hST hTS
    simpa only [hSTeq] using hiS
  rcases hJ with rfl | rfl
  · exact closed haT hTb hc
  · apply fromPrefixes
    intro t ht
    let r := (t + T) / 2
    have htr : t < r := by dsimp only [r]; linarith [ht.2]
    have hrT : r < T := by dsimp only [r]; linarith [ht.2]
    have har : a < r := ht.1.trans_lt htr
    have hsub : Icc a r ⊆ Ico a T := fun u hu => ⟨hu.1, hu.2.trans_lt hrT⟩
    exact ⟨r, htr, closed har (hrT.le.trans hTb) (c2_restrict hc hsub)⟩

end PoincareConjecture.M63
