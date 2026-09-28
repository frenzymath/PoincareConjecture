import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Disks.OriginalCompressionScalar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.OriginalRelativeDefiningFunction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.OriginalScalarHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance period_positive : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩

private theorem upper_asymmetric_scalar_phase_eq {rMinus rPlus u : ℝ}
    (hm : 0 < rMinus) (hp : 0 < rPlus) (hsum : rMinus + rPlus < 64)
    (hu : -rMinus ≤ u ∧ u ≤ rPlus) (theta : ℝ) :
    (theta : C0) - (u : C0) = theta ↔ u = 0 := by
  have huI : u ∈ Ico (-rMinus) (-rMinus + 4 * 16) := by
    exact ⟨hu.1, by linarith [hu.2]⟩
  have hzI : (0 : ℝ) ∈ Ico (-rMinus) (-rMinus + 4 * 16) := by
    constructor <;> linarith
  constructor
  · intro h
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico huI hzI).mp
    have hu0 : (u : C0) = 0 := sub_eq_self.mp h
    simpa using hu0
  · rintro rfl
    simp

private theorem upper_asymmetric_scalar_phase_mem_arc {rMinus rPlus u theta alpha : ℝ}
    (hm : 0 < rMinus) (hu : -rMinus ≤ u ∧ u ≤ rPlus)
    (hplus : rPlus < theta - alpha) (hminus : rMinus < 64 - (theta - alpha)) :
    (theta : C0) - (u : C0) ∈ AddCircle.closedIntervalArc (4 * 16) alpha theta ↔ 0 ≤ u := by
  have huI : theta - u ∈ Ico alpha (alpha + 4 * (16 : ℝ)) := by
    constructor <;> linarith [hu.1, hu.2]
  constructor
  · rintro ⟨t, ht, htu⟩
    have htI : t ∈ Ico alpha (alpha + 4 * (16 : ℝ)) := by
      exact ⟨ht.1, by linarith [ht.2]⟩
    rw [← AddCircle.coe_sub] at htu
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI huI).mp htu
    linarith [ht.2]
  · intro h
    exact ⟨theta - u, ⟨by linarith [hu.2], by linarith⟩, AddCircle.coe_sub _ _ _⟩

theorem OriginalDiskProduct.exists_hamiltonZero_upper_asymmetric_compression_map {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} {j : V2 → X0} (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X0) ⁻¹' P.openStrip))
    {U : Set X0} (hU : IsOpen U) (hSU : P.closedStrip ⊆ U)
    (theta : ℝ) {f : X0 → ℝ} (hf : ContinuousOn f U)
    (hfPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U))
    (hphase : ∀ x ∈ U, hamiltonZeroCircleMap phi x = (theta : C0) - (f x : C0))
    (hpos : ∀ x ∈ U, x ∈ interior R ↔ 0 < f x)
    (hzero : ∀ x ∈ U, x ∈ frontier R ↔ f x = 0)
    {rMinus rPlus : ℝ} (hm : 0 < rMinus) (hp : 0 < rPlus)
    (hsum : rMinus + rPlus < 64)
    (hbound : ∀ x ∈ U, -rMinus ≤ f x ∧ f x ≤ rPlus) :
    ∃ (G : C(unitInterval × X0, X0)) (N : Set X0),
      IsCompact N ∧ PLDomain e N ∧ P.closedStrip ⊆ interior N ∧ N ⊆ U ∧
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ interior N → G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (fun x => (Q0 (G (1, x))).2) ⁻¹' {(theta : C0)} =
        (hamiltonZeroCircleMap phi ⁻¹' {(theta : C0)} \ P.openStrip) ∪ P.endDisks ∧
      (∀ c : C0, c ∉ AddCircle.closedIntervalArc (4 * 16) (theta - rPlus) (theta + rMinus) →
        ∀ t : unitInterval, (fun x => (Q0 (G (t, x))).2) ⁻¹' {c} =
          hamiltonZeroCircleMap phi ⁻¹' {c}) ∧
      (∀ alpha : ℝ, rPlus < theta - alpha → rMinus < 64 - (theta - alpha) →
        R = hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc (4 * 16) alpha theta →
        (fun x => (Q0 (G (1, x))).2) ⁻¹' AddCircle.closedIntervalArc (4 * 16) alpha theta =
          P.cutCarrier) ∧
      let g : C(X0, X0) := ⟨fun x => G (1, x),
        G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      ChartwisePLMap e d
        (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (hamiltonZeroHandleMap g)) ∧
        Nonempty (phi.HomotopyRel (hamiltonZeroHandleMap g) B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel (hamiltonZeroHandleMap g) B0) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  obtain ⟨A, hA, hSA, hAU, hhalf⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e he.compatible he.cover
      (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)) hU hSU
  have heA : PLDomain e A := ⟨he.cover, he.compatible, hA.isClosed, hhalf⟩
  let r := max rMinus rPlus
  have hr : 0 < r := lt_of_lt_of_le hm (le_max_left _ _)
  have hfbound (x : X0) (hx : x ∈ U) : |f x| ≤ r := by
    apply abs_le.mpr
    constructor
    · exact (neg_le_neg (le_max_left _ _)).trans (hbound x hx).1
    · exact (hbound x hx).2.trans (le_max_right _ _)
  obtain ⟨a0, ha0c, ha0, ha0f, ha0bound, ha0sign⟩ :=
    he.exists_relative_signed_defining_function hR heA hA hU hAU hf hfPL
      (fun x hx => hpos x (hAU hx)) (fun x hx => hzero x (hAU hx))
      hr (fun x hx => hfbound x (hAU hx))
  obtain ⟨b0, N, hN, heN, hSN, hNA, hb0c, hb0, hb0a, _, _, hb0neg, hb0zero⟩ :=
    P.exists_compression_scalar hR he hopen isOpen_interior hSA ha0c ha0
      (fun x => (ha0sign x).2.1) (fun x => (ha0sign x).1) hr ha0bound
  let clip : ℝ → ℝ := fun u => min rPlus (max (-rMinus) u)
  have clip_eq (u : ℝ) (hu : -rMinus ≤ u ∧ u ≤ rPlus) : clip u = u := by
    simp only [clip, max_eq_right hu.1, min_eq_right hu.2]
  have clip_bound (u : ℝ) : -rMinus ≤ clip u ∧ clip u ≤ rPlus := by
    exact ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩
  have clip_pos (u : ℝ) : 0 < clip u ↔ 0 < u := by
    simp only [clip, lt_min_iff, lt_max_iff, hp, true_and,
      not_lt.mpr (neg_nonpos.mpr hm.le), false_or]
  have clip_neg (u : ℝ) : clip u < 0 ↔ u < 0 := by
    simp only [clip, min_lt_iff, max_lt_iff, not_lt.mpr hp.le, false_or,
      neg_lt_zero.mpr hm, true_and]
  have clip_zero (u : ℝ) : clip u = 0 ↔ u = 0 := by
    constructor
    · intro h
      have hnp : ¬ 0 < u := fun hu => (clip_pos u).mpr hu |>.ne' h
      have hnn : ¬ u < 0 := fun hu => (clip_neg u).mpr hu |>.ne h
      linarith
    · rintro rfl
      exact clip_eq 0 ⟨by linarith, hp.le⟩
  let a : X0 → ℝ := clip ∘ a0
  let b : X0 → ℝ := clip ∘ b0
  have hac : Continuous a := continuous_const.min (continuous_const.max ha0c)
  have hbc : Continuous b := continuous_const.min (continuous_const.max hb0c)
  have ha (i : ι) : LocallyPiecewiseAffineOn (a ∘ (e i).symm) (e i).target :=
    (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 rPlus) (e i).open_target).min
      ((locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (-rMinus))
        (e i).open_target).max (ha0 i))
  have hb (i : ι) : LocallyPiecewiseAffineOn (b ∘ (e i).symm) (e i).target :=
    (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 rPlus) (e i).open_target).min
      ((locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (-rMinus))
        (e i).open_target).max (hb0 i))
  have haf : EqOn a f A := by
    intro x hx
    change clip (a0 x) = f x
    rw [ha0f hx]
    exact clip_eq _ (hbound x (hAU hx))
  have habound (x : X0) : -rMinus ≤ a x ∧ a x ≤ rPlus := clip_bound (a0 x)
  have hbbound (x : X0) : -rMinus ≤ b x ∧ b x ≤ rPlus := clip_bound (b0 x)
  have hba : EqOn b a (interior N)ᶜ := fun _ hx => congrArg clip (hb0a hx)
  have hbneg (x : X0) : x ∉ P.cutCarrier ↔ b x < 0 :=
    (hb0neg x).trans (clip_neg (b0 x)).symm
  have hbzero : b ⁻¹' {0} = (frontier R \ P.openStrip) ∪ P.endDisks := by
    ext x
    exact (clip_zero (b0 x)).trans (Set.ext_iff.mp hb0zero x)
  let w : C(X0, ℝ) := ⟨fun x => a x - b x, hac.sub hbc⟩
  have hw (i : ι) : LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target :=
    ((ha i).add (hb i).neg).congr (fun _ _ => (sub_eq_add_neg _ _).symm)
  have hwzero (x : X0) (hx : x ∉ interior N) : w x = 0 := sub_eq_zero.mpr (hba hx).symm
  obtain ⟨G, hGformula, hGzero, hGfixed, hGphase, hGtail⟩ :=
    hphi.exists_hamiltonZero_scalar_homotopy hd F w hw hwzero
  have hNU : N ⊆ U := hNA.trans (interior_subset.trans hAU)
  have hnormal (x : X0) (hx : x ∈ interior N) : (Q0 (G (1, x))).2 = (theta : C0) - (b x : C0) := by
    have hxA : x ∈ A := interior_subset (hNA (interior_subset hx))
    rw [hGphase, hphase x (hAU hxA)]
    change (theta : C0) - (f x : C0) + ((a x - b x : ℝ) : C0) = _
    rw [← haf hxA, AddCircle.coe_sub]
    abel
  have htime (t : unitInterval) (x : X0) (hx : x ∈ interior N) :
      (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc (4 * 16) (theta - rPlus) (theta + rMinus) := by
    let u := (1 - (t : ℝ)) * a x + (t : ℝ) * b x
    have ht0 : 0 ≤ (t : ℝ) := t.property.1
    have ht1 : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
    have haabs := habound x
    have hbabs := hbbound x
    have hu : -rMinus ≤ u ∧ u ≤ rPlus := by
      dsimp only [u]
      constructor
      · nlinarith [mul_nonneg ht1 (show 0 ≤ a x + rMinus by linarith),
          mul_nonneg ht0 (show 0 ≤ b x + rMinus by linarith)]
      · nlinarith [mul_nonneg ht1 (sub_nonneg.mpr haabs.2),
          mul_nonneg ht0 (sub_nonneg.mpr hbabs.2)]
    refine ⟨theta - u, ⟨by linarith [hu.2], by linarith [hu.1]⟩, ?_⟩
    rw [hGformula, hamiltonZeroTargetTranslation_coordinates]
    change ((theta - u : ℝ) : C0) = hamiltonZeroCircleMap phi x + (((t : ℝ) * (a x - b x) : ℝ) : C0)
    have hxA : x ∈ A := interior_subset (hNA (interior_subset hx))
    rw [hphase x (hAU hxA), ← haf hxA, ← AddCircle.coe_sub, ← AddCircle.coe_add]
    congr 1
    dsimp only [u]
    ring
  have hUC : P.openStrip ⊆ P.closedStrip :=
    image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hEC : P.endDisks ⊆ P.closedStrip :=
    P.closedStrip_sdiff_openStrip.symm.subset.trans sdiff_subset
  refine ⟨G, N, hN, heN, hSN, hNU, hGzero, hGfixed, ?_, ?_, ?_, hGtail⟩
  · ext x
    change (Q0 (G (1, x))).2 = (theta : C0) ↔
      (hamiltonZeroCircleMap phi x = (theta : C0) ∧ x ∉ P.openStrip) ∨ x ∈ P.endDisks
    by_cases hx : x ∈ interior N
    · rw [hnormal x hx, upper_asymmetric_scalar_phase_eq hm hp hsum (hbbound x)]
      have hxU := hNU (interior_subset hx)
      have hqfront : x ∈ frontier R ↔ hamiltonZeroCircleMap phi x = (theta : C0) := by
        rw [hphase x hxU, upper_asymmetric_scalar_phase_eq hm hp hsum (hbound x hxU)]
        exact hzero x hxU
      have hz : b x = 0 ↔ (x ∈ frontier R ∧ x ∉ P.openStrip) ∨ x ∈ P.endDisks :=
        Set.ext_iff.mp hbzero x
      exact hz.trans (or_congr (and_congr hqfront Iff.rfl) Iff.rfl)
    · rw [hGfixed 1 x hx]
      have hxopen : x ∉ P.openStrip := fun h => hx (hSN (hUC h))
      have hxend : x ∉ P.endDisks := fun h => hx (hSN (hEC h))
      change hamiltonZeroCircleMap phi x = (theta : C0) ↔ _
      simp only [hxopen, hxend, not_false_eq_true, and_true, or_false]
  · intro c hc t
    ext x
    change (Q0 (G (t, x))).2 = c ↔ hamiltonZeroCircleMap phi x = c
    by_cases hx : x ∈ interior N
    · have hnew := htime t x hx
      have hold := htime 0 x hx
      rw [hGzero] at hold
      exact iff_of_false (fun h => hc (h ▸ hnew)) (fun h => hc (h ▸ hold))
    · rw [hGfixed t x hx]
      rfl
  · intro alpha hgap hrgap hRarc
    ext x
    change (Q0 (G (1, x))).2 ∈ AddCircle.closedIntervalArc (4 * 16) alpha theta ↔ x ∈ P.cutCarrier
    by_cases hx : x ∈ interior N
    · rw [hnormal x hx, upper_asymmetric_scalar_phase_mem_arc hm (hbbound x) hgap hrgap]
      constructor
      · intro h
        by_contra hn
        exact (not_lt_of_ge h) ((hbneg x).mp hn)
      · exact fun h => le_of_not_gt (fun hn => (hbneg x).mpr hn h)
    · rw [hGfixed 1 x hx]
      change hamiltonZeroCircleMap phi x ∈ AddCircle.closedIntervalArc (4 * 16) alpha theta ↔
        x ∈ R \ P.openStrip
      exact (Set.ext_iff.mp hRarc x).symm.trans
        (and_iff_left (fun h => hx (hSN (hUC h)))).symm

end PoincareConjecture.M76
