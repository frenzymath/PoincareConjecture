import PoincareConjecture.Proofs.M35.Uniqueness.LocalQuadraticBound
import PoincareConjecture.Proofs.M35.Uniqueness.RawCommonCarrier
import PoincareConjecture.Proofs.M09.TimeTranslatedFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_raw_local_positive_quadratic_heat_bound
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {T c d : ℝ}
    (hT : 0 < T) (hTlt : T < G.lifetime) (hc : 0 < c) (hd : 0 ≤ d)
    {C₀ : Set StandardCapSpace} (hC₀ : IsCompact C₀) :
    ∃ E : Set StandardCapSpace, IsCompact E ∧ C₀ ⊆ interior E ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ → StandardCapSpace → ℝ,
        ContinuousOn (Function.uncurry Q) (Ioc 0 T ×ˢ E) →
        (∀ t ∈ Ioc 0 T, ∀ x ∈ E, 0 ≤ Q t x) →
        (∀ t ∈ Ioc 0 T, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (Q t)) →
        (∀ t ∈ Ioc 0 T, ∀ x ∈ E, ∃ a : ℝ,
          HasDerivWithinAt (fun s => Q s x) a (Icc 0 t) t ∧
            a - (G.flow.connection t).laplacian (Q t) x ≤ -c * Q t x ^ 2 + d) →
        ∀ t ∈ Ioc 0 T, ∀ p ∈ C₀, t * Q t p ≤ C := by
  obtain ⟨K₀, hK₀, hbound⟩ := G.curvature_locally_bounded T hT.le hTlt
  let K := K₀ + 1
  have hK : 0 < K := by dsimp only [K]; linarith
  have hRm (t : ℝ) (ht : t ∈ Icc 0 T) (x : StandardCapSpace) :
      (G.flow.connection t).curvatureTensorNorm x ≤ K := by
    have hh := (le_abs_self _).trans (hbound t ht x)
    dsimp only [K]
    linarith
  obtain ⟨L, H, hL, hH, hcutoff⟩ :=
    M04.exists_shi_geometric_cutoff 3 K (K * T) 1 hK (by norm_num)
  let R := M04.shiRetainedFlowRadius 3 (K * T) 1
  have hR : 0 < R := M04.shiRetainedFlowRadius_pos (by norm_num)
  obtain ⟨E, hE, hCE, hballs⟩ := exists_raw_common_ball_carrier P G hT hTlt hR hC₀
  let C := max 0 (M04.shiCutoffThreshold c d L H T)
  have hC : 0 ≤ C := le_max_left _ _
  refine ⟨E, hE, hCE, 2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro Q hcont hQ hspace hheat t ht p hp
  let a := t / 2
  have ha : 0 < a := div_pos ht.1 (by norm_num)
  have haT : a ≤ T := by dsimp only [a]; linarith only [ht.1, ht.2]
  have hshift (s : ℝ) (hs : s ∈ Icc 0 a) : a + s ∈ Ioc 0 T := by
    constructor <;> dsimp only [a] at * <;> linarith only [ha, hs.1, hs.2, ht.2]
  let F := PoincareConjecture.Proofs.M09.timeTranslatedFlow G.flow a a ha
    (fun s hs => ⟨(hshift s hs).1.le, (hshift s hs).2.trans_lt hTlt⟩)
  have htime : a ≤ K * T / K := by
    rw [mul_div_cancel_left₀ T hK.ne']
    exact haT
  obtain ⟨_, η, hη, hη0, hη1, hboundary, hηp, hsupport⟩ :=
    hcutoff StandardCapSpace a ha.le htime F p E hE
      (fun s hs => hballs (a + s) ⟨(hshift s hs).1.le, (hshift s hs).2⟩ p hp)
      (fun s hs y _ => hRm (a + s) ⟨(hshift s hs).1.le, (hshift s hs).2⟩ y)
  let q := fun s y => Q (a + s) y
  have hqc : ContinuousOn (Function.uncurry q) (Icc 0 a ×ˢ E) :=
    hcont.comp (((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn)
      (fun z hz => ⟨hshift z.1 hz.1, hz.2⟩)
  have hqd (s : ℝ) (hs : s ∈ Ioc 0 a) (y : StandardCapSpace)
      (hy : y ∈ interior E) : ∃ z : ℝ,
        HasDerivWithinAt (fun r => q r y) z (Icc 0 s) s ∧
          z - (F.connection s).laplacian (q s) y ≤ -c * q s y ^ 2 + d := by
    have hsa := hshift s ⟨hs.1.le, hs.2⟩
    obtain ⟨z, hz, hze⟩ := hheat (a + s) hsa y (interior_subset hy)
    have hmap : MapsTo (fun r : ℝ => a + r) (Icc 0 s) (Icc 0 (a + s)) := by
      intro r hr
      constructor <;> linarith only [ha, hr.1, hr.2]
    have hchain := hz.comp s ((hasDerivAt_id s).const_add a).hasDerivWithinAt hmap
    refine ⟨z, ?_, hze⟩
    simpa only [Function.comp_def, mul_one, q] using hchain
  have hestimate := M04.shi_cutoff_bound F.metric F.connection hE
    (S := a) (κ := 1) (c := c) (d := d) (L := L) (G := H) (Θ := T) (a := 0) (I := 0)
    ha (by norm_num) hc hd hL hH (by norm_num) (by norm_num) (by simpa using haT)
    q η hqc hη (fun s hs y hy => hQ (a + s) (hshift s hs) y hy)
    hη0 hη1 hboundary (fun _ _ => by simp)
    (fun s hs => hspace (a + s) (hshift s ⟨hs.1.le, hs.2⟩))
    (fun s hs y hy => by simpa only [one_mul] using! hqd s hs y hy)
    (by simpa only [M04.shiPhysicalCutoffSupports, one_mul] using hsupport)
  have hh : a * Q t p ≤ C := by
    simpa only [zero_add, hηp a ⟨ha.le, le_rfl⟩, mul_one,
      q, show a + a = t by dsimp only [a]; ring, C] using
      hestimate a ⟨ha.le, le_rfl⟩ p (interior_subset (hCE hp))
  dsimp only [a] at hh
  linarith only [hh]

end PoincareConjecture.M35.Uniqueness
