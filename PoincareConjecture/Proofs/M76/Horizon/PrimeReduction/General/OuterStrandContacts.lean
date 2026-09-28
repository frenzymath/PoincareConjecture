import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.FiniteContactBuffer
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.OuterTubeStrand
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedGraph








set_option autoImplicit false
open Set Geometry
open scoped Topology

namespace PoincareConjecture.M76

local notation "V" => (ℝ × ℝ)
local notation "Z" => (Prod.snd : V → ℝ) ⁻¹' ({0} : Set ℝ)
local notation "I" => Icc (0 : ℝ) 1



theorem exists_planar_endpoint_contact_buffer {S : Set V}
    (hfinite : (S ∩ Z).Finite) {a b : ℝ → V}
    (ha : ContinuousAt a 0) (hb : ContinuousAt b 0)
    (ha0 : (a 0).2 = 0) (hb0 : (b 0).2 = 0)
    (hab : (a 0).1 ≤ (b 0).1)
    (hcontact : segment ℝ (a 0) (b 0) ∩ S = {a 0, b 0}) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < ε →
      (a c).2 = 0 → (b c).2 = 0 →
      (a c).1 ≤ (a 0).1 → (b 0).1 ≤ (b c).1 →
      segment ℝ (a c) (b c) ∩ S = {a 0, b 0} := by
  let C : Set ℝ := Prod.fst '' (S ∩ Z)
  have hC : C.Finite := hfinite.image Prod.fst
  have hmem (x : ℝ) : x ∈ C ↔ (x, 0) ∈ S := by
    constructor
    · rintro ⟨y, ⟨hyS, hy0⟩, hyx⟩
      have hy : y = (x, 0) := Prod.ext hyx hy0
      exact hy ▸ hyS
    · intro hx
      exact ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
  have hreal : Icc (a 0).1 (b 0).1 ∩ C = {(a 0).1, (b 0).1} := by
    ext x
    constructor
    · rintro ⟨hx, hxC⟩
      have hp : (x, 0) ∈ segment ℝ (a 0) (b 0) ∩ S := by
        rw [Polygon.returning_axis_segment ha0 hb0 hab]
        exact ⟨⟨hx, rfl⟩, (hmem x).mp hxC⟩
      rcases hcontact.subset hp with h | h
      · exact Or.inl (congrArg Prod.fst h)
      · exact Or.inr (congrArg Prod.fst h)
    · rintro (rfl | rfl)
      · have hp := hcontact.symm.subset (show a 0 ∈ ({a 0, b 0} : Set V) by simp)
        refine ⟨⟨le_rfl, hab⟩, (hmem _).mpr ?_⟩
        exact (Prod.ext rfl ha0 : a 0 = ((a 0).1, 0)) ▸ hp.2
      · have hp := hcontact.symm.subset (show b 0 ∈ ({a 0, b 0} : Set V) by simp)
        refine ⟨⟨hab, le_rfl⟩, (hmem _).mpr ?_⟩
        exact (Prod.ext rfl hb0 : b 0 = ((b 0).1, 0)) ▸ hp.2
  obtain ⟨ε, hε, hbuffer⟩ :=
    exists_continuous_endpoint_contact_buffer hC ha.fst hb.fst hreal
  refine ⟨ε, hε, ?_⟩
  intro c hc hac hbc hleft hright
  have heq := hbuffer c hc hleft hright
  rw [Polygon.returning_axis_segment hac hbc (hleft.trans (hab.trans hright))]
  ext z
  constructor
  · rintro ⟨⟨hz, hz0⟩, hzS⟩
    have hzC : z.1 ∈ C := ⟨z, ⟨hzS, hz0⟩, rfl⟩
    rcases heq.subset ⟨hz, hzC⟩ with h | h
    · exact Or.inl (Prod.ext h (hz0.trans ha0.symm))
    · exact Or.inr (Prod.ext h (hz0.trans hb0.symm))
  · rintro (rfl | rfl)
    · have h := heq.symm.subset (show (a 0).1 ∈ ({(a 0).1, (b 0).1} : Set ℝ) by simp)
      exact ⟨⟨h.1, ha0⟩, (hcontact.symm.subset (by simp)).2⟩
    · have h := heq.symm.subset (show (b 0).1 ∈ ({(a 0).1, (b 0).1} : Set ℝ) by simp)
      exact ⟨⟨h.1, hb0⟩, (hcontact.symm.subset (by simp)).2⟩





theorem exists_outer_ribbon_replacement_axis
    {r : ℝ} (hr : 0 < r) (f : V → V)
    (hf : FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ I))
    (hi : InjOn f (Icc (-r) r ×ˢ I))
    (hup : ∀ z ∈ Icc (-r) r ×ˢ I, 0 ≤ (f z).2)
    (hends : ∀ c ∈ Icc (-r) r, (f (c, 0)).2 = 0 ∧ (f (c, 1)).2 = 0)
    {S : Set V} (hS : ∀ z ∈ Icc (-r) r ×ˢ I, f z ∈ S ↔ z.1 = 0)
    (hfinite : (S ∩ Z).Finite)
    (hcontact : segment ℝ (f (0, 0)) (f (0, 1)) ∩ S = {f (0, 0), f (0, 1)})
    {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hPu : ∀ i, 0 ≤ (P i).2)
    (hboundary : P.boundary ℝ = ((fun t : ℝ => f (0, t)) '' I) ∪
      segment ℝ (f (0, 0)) (f (0, 1)))
    (horder : (f (0, 0)).1 < (f (0, 1)).1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, c ∈ Ioo (-r) r ∧ |c| < ε ∧ c ≠ 0 ∧
      (f (c, 0)).1 < (f (0, 0)).1 ∧ (f (0, 1)).1 < (f (c, 1)).1 ∧
      let w := segment ℝ (f (c, 0)) (f (c, 1))
      let W := (fun t : ℝ => f (c, t)) '' I
      IsFinitePLBallPair ℝ w {f (c, 0), f (c, 1)} ∧
      IsFinitePLBallPair ℝ W {f (c, 0), f (c, 1)} ∧
      w ∩ S = {f (0, 0), f (0, 1)} ∧
      W ∩ Z = {f (c, 0), f (c, 1)} ∧ Disjoint W S ∧
      ∃ axis : w ≃ₜ W, axis.IsFinitePL ∧
        ∀ x : w, (x : V) ∈ ({f (c, 0), f (c, 1)} : Set V) → (axis x : V) = x := by
  have hzero : (0 : ℝ) ∈ Icc (-r) r := ⟨(neg_lt_zero.mpr hr).le, hr.le⟩
  have htrace (t : ℝ) (ht : t ∈ I) : ContinuousAt (fun c => f (c, t)) 0 := by
    apply ContinuousOn.continuousAt
      (hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun c hc => ⟨hc, ht⟩))
    exact Icc_mem_nhds (neg_lt_zero.mpr hr) hr
  obtain ⟨δ, hδ, hbuffer⟩ := exists_planar_endpoint_contact_buffer hfinite
    (htrace 0 (by simp)) (htrace 1 (by simp))
    (hends 0 hzero).1 (hends 0 hzero).2 horder.le hcontact
  obtain ⟨c, hc, hcsmall, hc0, hleft, _, hright, _, _, hW, hWaxis, havoid⟩ :=
    exists_outer_strand_of_planar_signed_ribbon hr f hf hi hup hends hS
      P hP hPi hPu hboundary horder (lt_min hε hδ)
  have hcc : c ∈ Icc (-r) r := Ioo_subset_Icc_self hc
  have hab : f (c, 0) ≠ f (c, 1) := by
    intro heq
    have h := congrArg Prod.fst heq
    linarith
  let L : ℝ →ᴬ[ℝ] V := ContinuousAffineMap.lineMap (f (c, 0)) (f (c, 1))
  have hw : IsFinitePLBallPair ℝ (segment ℝ (f (c, 0)) (f (c, 1)))
      {f (c, 0), f (c, 1)} := by
    have h := isFinitePLBallPair_affine_interval zero_lt_one L
      (AffineMap.lineMap_injective ℝ hab).injOn
    change IsFinitePLBallPair ℝ
      (AffineMap.lineMap (f (c, 0)) (f (c, 1)) '' I)
      {AffineMap.lineMap (f (c, 0)) (f (c, 1)) 0,
        AffineMap.lineMap (f (c, 0)) (f (c, 1)) 1} at h
    simpa only [← segment_eq_image_lineMap, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one] using h
  obtain ⟨axis, haxis, ha, hb⟩ := hw.exists_marked_interval_homeomorph hW hab hab
  refine ⟨c, hc, hcsmall.trans_le (min_le_left _ _), hc0, hleft, hright, hw, hW,
    hbuffer c (hcsmall.trans_le (min_le_right _ _)) (hends c hcc).1 (hends c hcc).2
      hleft.le hright.le, hWaxis, havoid, axis, haxis, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact ((ha x).mpr hx).trans hx.symm
  · exact ((hb x).mpr hx).trans hx.symm

end PoincareConjecture.M76
