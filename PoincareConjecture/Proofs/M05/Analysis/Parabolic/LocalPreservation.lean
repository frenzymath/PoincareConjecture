import PoincareConjecture.Proofs.M05.Analysis.Parabolic.SupportTransport
import PoincareConjecture.Proofs.M05.Analysis.Parabolic.CompactMaximum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped InnerProductSpace Topology NNReal BigOperators Classical

namespace Poincare.Parabolic

variable {B : Type*} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  {V : B → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [∀ x, FiniteDimensional ℝ (V x)]

theorem local_mem_of_inward_of_contact
    {K : ∀ x, Set (V x)} (hne : ∀ x, (K x).Nonempty)
    (hclosed : ∀ x, IsClosed (K x)) (hconv : ∀ x, Convex ℝ (K x))
    (O : B → Set B) (hO : ∀ p, IsOpen (O p)) (hpO : ∀ p, p ∈ O p)
    (e : ∀ p x, x ∈ O p → V p ≃ₗᵢ[ℝ] V x)
    (heK : ∀ p x hx, e p x hx '' K p = K x)
    {U L : ∀ x, ℝ → V x} {ψ : ∀ x, ℝ → V x → V x} {a b : ℝ}
    (hU : ∀ p, ContinuousOn (fun z : B × ℝ =>
      if hx : z.1 ∈ O p then (e p z.1 hx).symm (U z.1 z.2) else 0)
      (O p ×ˢ Icc a b))
    (hevol : ∀ x t, t ∈ Ioc a b →
      HasDerivWithinAt (U x) (L x t + ψ x t (U x t)) (Icc a b) t)
    (hlip : ∀ R : ℝ, ∃ D : ℝ≥0, ∀ x t, t ∈ Ioc a b →
      LipschitzOnWith D (ψ x t) (Metric.closedBall 0 R))
    (hinward : ∀ x t, t ∈ Ioc a b → ∀ q ∈ unitSupportSet (K x),
      ⟪q.2, ψ x t q.1⟫_ℝ ≤ 0)
    (hcontact : ∀ x t, t ∈ Ioc a b → ∀ q ∈ unitSupportSet (K x),
      0 < Metric.infDist (U x t) (K x) →
      ⟪q.2, U x t - q.1⟫_ℝ = Metric.infDist (U x t) (K x) →
      (∀ y, Metric.infDist (U y t) (K y) ≤ Metric.infDist (U x t) (K x)) →
      ⟪q.2, L x t⟫_ℝ ≤ 0)
    (hinit : ∀ x, U x a ∈ K x) :
    ∀ x t, t ∈ Icc a b → U x t ∈ K x := by
  classical
  let UP (p : B) (z : B × ℝ) : V p :=
    if hx : z.1 ∈ O p then (e p z.1 hx).symm (U z.1 z.2) else 0
  have hUP (p x : B) (hx : x ∈ O p) (t : ℝ) :
      UP p (x, t) = (e p x hx).symm (U x t) := dif_pos hx
  choose C hCmem hCsub hCcompact using fun p =>
    local_compact_nhds ((hO p).mem_nhds (hpO p))
  obtain ⟨s, -, hs⟩ := isCompact_univ.elim_nhds_subcover C (fun p _ => hCmem p)
  have hcover (x : B) : ∃ p : s, x ∈ C p.1 := by
    obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact ⟨⟨p, hp⟩, hx⟩
  have hbound (p : s) : ∃ N : ℝ, ∀ z ∈ C p.1 ×ˢ Icc a b, ‖UP p.1 z‖ ≤ N :=
    ((hCcompact p.1).prod isCompact_Icc).exists_bound_of_continuousOn
      ((hU p.1).mono (fun _ hz => ⟨hCsub p.1 hz.1, hz.2⟩))
  choose Np hNp using hbound
  let N : ℝ := ∑ p : s, |Np p|
  have hN (x : B) (t : ℝ) (ht : t ∈ Icc a b) : ‖U x t‖ ≤ N := by
    obtain ⟨p, hx⟩ := hcover x
    have hn := hNp p (x, t) ⟨hx, ht⟩
    rw [hUP p.1 x (hCsub p.1 hx) t, (e p.1 x (hCsub p.1 hx)).symm.norm_map] at hn
    exact hn.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun q : s => |Np q|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ p)))
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice hne
  let A : ℝ := ∑ p : s, ‖w p.1‖
  have hanchor (x : B) : ∃ z ∈ K x, ‖z‖ ≤ A := by
    obtain ⟨p, hx⟩ := hcover x
    refine ⟨e p.1 x (hCsub p.1 hx) (w p.1), ?_, ?_⟩
    · rw [← heK p.1 x (hCsub p.1 hx)]
      exact mem_image_of_mem _ (hw p.1)
    · rw [(e p.1 x (hCsub p.1 hx)).norm_map]
      exact Finset.single_le_sum (f := fun q : s => ‖w q.1‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p)
  choose z hz hzbound using hanchor
  let R : ℝ := 2 * N + A
  let P (p : s) := C p.1 × boundedUnitSupportSet (K p.1) R
  let (p : s) : CompactSpace (C p.1) := isCompact_iff_compactSpace.mp (hCcompact p.1)
  let (p : s) : CompactSpace (boundedUnitSupportSet (K p.1) R) :=
    isCompact_iff_compactSpace.mp (isCompact_boundedUnitSupportSet _ R (hclosed p.1))
  let S := Σ p : s, P p
  let base (q : S) : B := q.2.1.1
  let iso (q : S) : V q.1.1 ≃ₗᵢ[ℝ] V (base q) :=
    e q.1.1 (base q) (hCsub q.1.1 q.2.1.2)
  let pair (q : S) : V (base q) × V (base q) :=
    (iso q q.2.2.1.1, iso q q.2.2.1.2)
  have hpair (q : S) : pair q ∈ unitSupportSet (K (base q)) := by
    rw [← heK q.1.1 (base q) (hCsub q.1.1 q.2.1.2)]
    exact unitSupport_map (iso q) q.2.2.2.1
  let f (q : S) (t : ℝ) : ℝ := ⟪(pair q).2, U (base q) t - (pair q).1⟫_ℝ
  let f' (q : S) (t : ℝ) : ℝ :=
    ⟪(pair q).2, L (base q) t + ψ (base q) t (U (base q) t)⟫_ℝ
  have hf_model (q : S) (t : ℝ) : f q t =
      ⟪q.2.2.1.2, UP q.1.1 (base q, t) - q.2.2.1.1⟫_ℝ := by
    rw [hUP q.1.1 (base q) (hCsub q.1.1 q.2.1.2)]
    exact support_eval_pullback (iso q) _ _ _
  have hf_cont : Continuous (fun q : S × Icc a b => f q.1 q.2) := by
    have hp : Continuous (fun q : Σ p : s, P p × Icc a b => f ⟨q.1, q.2.1⟩ q.2.2) := by
      apply continuous_sigma
      intro p
      have hc : Continuous (fun q : P p × Icc a b => UP p.1 (q.1.1.1, q.2)) :=
        (hU p.1).comp_continuous
          ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
            (continuous_subtype_val.comp continuous_snd))
          (fun q => ⟨hCsub p.1 q.1.1.2, q.2.2⟩)
      have hn : Continuous (fun q : P p × Icc a b => q.1.2.1.2) :=
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).snd
      have hv : Continuous (fun q : P p × Icc a b => q.1.2.1.1) :=
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).fst
      convert hn.inner (hc.sub hv) using 1
      ext q
      exact hf_model ⟨p, q.1⟩ q.2
    exact hp.comp Homeomorph.sigmaProdDistrib.continuous
  have hf : ContinuousOn (Function.uncurry f) (univ ×ˢ Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hf_cont.comp
      ((continuous_subtype_val.fst).prodMk
        (continuous_subtype_val.snd.subtype_mk (fun q => q.2.2)))
  have hderiv (q : S) (t : ℝ) (ht : t ∈ Ioc a b) :
      HasDerivWithinAt (f q) (f' q t) (Icc a b) t := by
    simpa [f, f'] using (hasDerivWithinAt_const t (Icc a b) (pair q).2).inner ℝ
      ((hevol (base q) t ht).sub_const (pair q).1)
  have hrealize (x : B) (r : V x × V x) (hr : r ∈ boundedUnitSupportSet (K x) R) :
      ∃ q : S, ∀ t, f q t = ⟪r.2, U x t - r.1⟫_ℝ := by
    obtain ⟨p, hx⟩ := hcover x
    let ex := e p.1 x (hCsub p.1 hx)
    have hmap : ex.symm '' K x = K p.1 := by
      rw [← heK p.1 x (hCsub p.1 hx)]
      exact Set.ext fun v => by simp [ex]
    have hr' : (ex.symm r.1, ex.symm r.2) ∈ boundedUnitSupportSet (K p.1) R := by
      rw [← hmap]
      exact (boundedUnitSupport_map_iff ex.symm).mpr hr
    refine ⟨⟨p, ⟨x, hx⟩, ⟨(ex.symm r.1, ex.symm r.2), hr'⟩⟩, ?_⟩
    intro t
    simp only [f, pair, iso, base, ex, LinearIsometryEquiv.apply_symm_apply]
  have hactive (q : S) (t : ℝ) (ht : t ∈ Icc a b) (hpos : 0 < f q t)
      (hmax : ∀ p, f p t ≤ f q t) :
      f q t = Metric.infDist (U (base q) t) (K (base q)) ∧
        ∀ y, Metric.infDist (U y t) (K y) ≤
          Metric.infDist (U (base q) t) (K (base q)) := by
    have hle := unitSupport_eval_le_infDist (hne (base q)) (hclosed (base q))
      (hconv (base q)) (hpair q) (U (base q) t)
    have hdist (y : B) : Metric.infDist (U y t) (K y) ≤ f q t := by
      by_cases hy : U y t ∈ K y
      · simpa only [Metric.infDist_zero_of_mem hy] using hpos.le
      · obtain ⟨r, hr, heq⟩ := exists_boundedUnitSupport_active (hne y) (hclosed y)
          (hconv y) (hz y) (hN y t ht) hy
        have hr' : r ∈ boundedUnitSupportSet (K y) R :=
          ⟨hr.1, hr.2.trans (add_le_add (le_refl (2 * N)) (hzbound y))⟩
        obtain ⟨p, hp⟩ := hrealize y r hr'
        rw [← heq, ← hp t]
        exact hmax p
    exact ⟨le_antisymm hle (hdist (base q)), fun y => (hdist y).trans hle⟩
  obtain ⟨D, hD⟩ := hlip (max N R)
  have hmax (q : S) (t : ℝ) (ht : t ∈ Ioc a b) (hpos : 0 < f q t)
      (hmax : ∀ p, f p t ≤ f q t) : f' q t ≤ D * f q t := by
    have ht' : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    obtain ⟨ha, hs⟩ := hactive q t ht' hpos hmax
    have hd := hcontact (base q) t ht (pair q) (hpair q) (ha ▸ hpos) ha hs
    have hr := reaction_inner_le_mul_infDist (hne (base q)) (hclosed (base q))
      (hconv (base q)) (hpair q) ha (hD (base q) t ht)
      (show U (base q) t ∈ Metric.closedBall 0 (max N R) by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          (hN (base q) t ht').trans (le_max_left _ _))
      (show nearestPoint (K (base q)) (hne (base q)) (hclosed (base q)) (hconv (base q))
          (U (base q) t) ∈ Metric.closedBall 0 (max N R) by
        have hp := norm_nearestPoint_le (hne (base q)) (hclosed (base q)) (hconv (base q))
          (hz (base q)) (hN (base q) t ht')
        have hp' : _ ≤ R := hp.trans (add_le_add (le_refl (2 * N)) (hzbound (base q)))
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          hp'.trans (le_max_right _ _))
      (hinward (base q) t ht)
    dsimp only [f']
    rw [inner_add_right, ha]
    linarith
  have hnonpos := nonpos_of_deriv_le_mul_at_max hf hderiv hmax
    (fun q => (hpair q).2.2 (U (base q) a) (hinit (base q)))
  intro x t ht
  by_contra hnot
  obtain ⟨r, hr, heq⟩ := exists_boundedUnitSupport_active (hne x) (hclosed x) (hconv x)
    (hz x) (hN x t ht) hnot
  have hr' : r ∈ boundedUnitSupportSet (K x) R :=
    ⟨hr.1, hr.2.trans (add_le_add (le_refl (2 * N)) (hzbound x))⟩
  obtain ⟨q, hq⟩ := hrealize x r hr'
  have h := hnonpos q t ht
  rw [hq t, heq] at h
  exact (not_lt_of_ge h) (((hclosed x).notMem_iff_infDist_pos (hne x)).mp hnot)

end Poincare.Parabolic
