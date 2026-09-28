import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.PlanarLift



set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

open TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem exists_partial_planar_coordinates
    {a b w : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hw : 0 < w) (hwsmall : w ≤ 1 / 2) (side : Bool)
    {q : P2 → E} (hq : FinitePiecewiseAffineOn q (Icc (-w) w ×ˢ Icc a b))
    (hqi : InjOn q (Icc (-w) w ×ˢ Icc a b))
    (hqmap : MapsTo q (Icc (-w) w ×ˢ Icc a b) (Rim ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hcenter : ∀ s ∈ Icc a b, q (0, s) = (armPoint side s, 0))
    (hzero : ∀ p ∈ Icc (-w) w ×ˢ Icc a b, (q p).2 = 0 ↔ p.1 = 0) :
    ∃ (v : ℝ) (g : P2 → P2), 0 < v ∧ v ≤ w ∧ v ≤ 1 / 2 ∧
      FinitePiecewiseAffineOn g (Icc (-v) v ×ˢ Icc a b) ∧
      InjOn g (Icc (-v) v ×ˢ Icc a b) ∧
      MapsTo g (Icc (-v) v ×ˢ Icc a b)
        (Ioo (-(1 / 2 : ℝ)) (3 / 2) ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)) ∧
      (∀ s ∈ Icc a b, g (0, s) = (s, 0)) ∧
      (∀ p ∈ Icc (-v) v ×ˢ Icc a b, (armPoint side (g p).1, (g p).2) = q p) ∧
      ∀ p ∈ Icc (-v) v ×ˢ Icc a b, (g p).2 = 0 ↔ p.1 = 0 := by
  have hbase (s : ℝ) (hs : s ∈ Icc a b) : s ∈ Icc (0 : ℝ) 1 :=
    ⟨ha.trans hs.1, hs.2.trans hb⟩
  let f : Icc a b × I → E := fun z => q (w * (z.2 : ℝ), (z.1 : ℝ))
  have hf : Continuous f := hq.continuousOn.comp_continuous
    ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp continuous_fst)) (by
        intro z
        exact ⟨⟨by nlinarith [z.2.property.1], by nlinarith [z.2.property.2]⟩, z.1.property⟩)
  let O : Set E := {z | 0 < sign side * z.1 0}
  have hO : IsOpen O := isOpen_lt continuous_const
    (continuous_const.mul ((continuous_apply 0).comp continuous_fst))
  have hbaseO (s : Icc a b) : f (s, ⟨0, by norm_num⟩) ∈ O := by
    change 0 < sign side * (q (w * 0, (s : ℝ))).1 0
    rw [mul_zero, hcenter s s.property, armPoint_eq_rimArm side (hbase s s.property)]
    cases side <;> norm_num [rimArm, sign]
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨δ, hδ, hδsmall, hthin⟩ := hf.exists_closed_strip_subset hO hbaseO
  let v := w * δ
  have hv : 0 < v := mul_pos hw hδ
  have hvw : v ≤ w := by dsimp [v]; nlinarith
  have hsub : Icc (-v) v ×ˢ Icc a b ⊆ Icc (-w) w ×ˢ Icc a b := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hp.2⟩
  have hchart (p : P2) (hp : p ∈ Icc (-v) v ×ˢ Icc a b) : 0 < sign side * (q p).1 0 := by
    have hpa : p.1 / w ∈ Icc (-δ) δ :=
      ⟨(le_div_iff₀ hw).mpr (by dsimp [v] at hp; nlinarith [hp.1.1]),
        (div_le_iff₀ hw).mpr (by dsimp [v] at hp; nlinarith [hp.1.2])⟩
    have hpI : p.1 / w ∈ I := ⟨by linarith [hpa.1], by linarith [hpa.2]⟩
    have h := hthin ⟨p.2, hp.2⟩ ⟨p.1 / w, hpI⟩ (abs_le.mpr hpa)
    change 0 < sign side * (q (w * (p.1 / w), p.2)).1 0 at h
    simpa [mul_div_cancel₀ _ hw.ne'] using h
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    (isFinitePLBallPair_Icc (by linarith : -v < v)).prod (isFinitePLBallPair_Icc hab)
  have hq' : FinitePiecewiseAffineOn q (Icc (-v) v ×ˢ Icc a b) :=
    hKs ▸ hq.restrict K hK (hKs.subset.trans hsub)
  let g : P2 → P2 := fun p => (armPhase side (q p).1, (q p).2)
  have hg : FinitePiecewiseAffineOn g (Icc (-v) v ×ˢ Icc a b) :=
    (finitePL_armPhase (hq'.postcomp (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap) side).prod_mk
      (hq'.postcomp (ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)
  have hback (p : P2) (hp : p ∈ Icc (-v) v ×ˢ Icc a b) :
      (armPoint side (g p).1, (g p).2) = q p :=
    Prod.ext (armPoint_armPhase side (hqmap (hsub hp)).1 (hchart p hp)) rfl
  refine ⟨v, g, hv, hvw, hvw.trans hwsmall, hg, ?_, ?_, ?_, hback, ?_⟩
  · intro p hp z hz heq
    exact hqi (hsub hp) (hsub hz) ((hback p hp).symm.trans
      ((congrArg (fun u : P2 => (armPoint side u.1, u.2)) heq).trans (hback z hz)))
  · intro p hp
    exact ⟨armPhase_mem side (hqmap (hsub hp)).1 (hchart p hp), (hqmap (hsub hp)).2⟩
  · intro s hs
    dsimp [g]
    rw [hcenter s hs, armPoint_eq_rimArm side (hbase s hs), armPhase_rimArm side (hbase s hs)]
  · intro p hp
    exact hzero p (hsub hp)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
