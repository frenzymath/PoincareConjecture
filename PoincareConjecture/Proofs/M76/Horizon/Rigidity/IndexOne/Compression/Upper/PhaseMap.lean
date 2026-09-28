import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.SupportedScalar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.RelativeScalarHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc











set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩



theorem exists_upper_asymmetric_relative_compression_map
    {α β : Type*} {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    {phi : C(H, H)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {a b : ℝ}
    {j : (Fin 2 → ℝ) → X} (P : OriginalDiskProduct e (sourceSlab phi a b) j)
    (hN : IsCompact (sourceSlab phi a b)) (he : PLDomain e (sourceSlab phi a b))
    (hopen : IsOpen ((Subtype.val : sourceSlab phi a b → X) ⁻¹' P.openStrip))
    {U : Set X} (hU : IsOpen U) (hUR : U ⊆ interior R) (hSU : P.closedStrip ⊆ U)
    {f : X → ℝ} (hf : ContinuousOn f U)
    (hfPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U))
    (hphase : ∀ x ∈ U, ambientSourcePhase phi x = (b : C) - (f x : C))
    (hpos : ∀ x ∈ U, x ∈ interior (sourceSlab phi a b) ↔ 0 < f x)
    (hzero : ∀ x ∈ U, x ∈ frontier (sourceSlab phi a b) ↔ f x = 0)
    {rm rp : ℝ} (hm : 0 < rm) (hp : 0 < rp)
    (hpgap : rp < b - a) (hmgap : rm < p - (b - a))
    (hbound : ∀ x ∈ U, -rm ≤ f x ∧ f x ≤ rp) :
    ∃ (psi : C(H, H)) (A : Set X), IsCompact A ∧ PLDomain e A ∧
      P.closedStrip ⊆ interior A ∧ A ⊆ U ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L psi) ∧
      Nonempty (phi.HomotopyRel psi B) ∧
      Nonempty ((ContinuousMap.id H).HomotopyRel psi B) ∧
      (∀ x : H, ((latticeHandleDomainEquiv (Fin 1) (Fin 2) L).symm x : X) ∉ interior A →
        psi x = phi x) ∧
      sourceSurface psi (b : C) = (sourceSurface phi (b : C) \ P.openStrip) ∪ P.endDisks ∧
      sourceSurface psi (a : C) = sourceSurface phi (a : C) ∧
      sourceSlab psi a b = P.cutCarrier ∧ psi ⁻¹' B = phi ⁻¹' B := by
  let : T2Space ((Fin 2 → ℝ) ⧸ (hamiltonLowerPeriodLattice (Fin 2)).toAddSubgroup) :=
    (hamiltonLowerLatticePiEquiv (Fin 2)).isEmbedding.t2Space
  let : LocallyCompactSpace X := he.locallyCompactSpace
  obtain ⟨A0, hA0, hSA0, hA0U, hhalf⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e he.compatible he.cover
      (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)) hU hSU
  have heA0 : PLDomain e A0 := ⟨he.cover, he.compatible, hA0.isClosed, hhalf⟩
  let r := max rm rp
  have hr : 0 < r := lt_of_lt_of_le hm (le_max_left _ _)
  have hfbound (x : X) (hx : x ∈ U) : |f x| ≤ r :=
    abs_le.mpr ⟨(neg_le_neg (le_max_left _ _)).trans (hbound x hx).1,
      (hbound x hx).2.trans (le_max_right _ _)⟩
  obtain ⟨old0, hoc0, ho0, hof0, hobound0, hosign0⟩ :=
    exists_compact_domain_relative_defining_function he hN heA0 hA0 hU hA0U hf hfPL
      (fun x hx => hpos x (hA0U hx)) (fun x hx => hzero x (hA0U hx))
      hr (fun x hx => hfbound x (hA0U hx))
  obtain ⟨g0, A, hA, heA, hSA, hAA0, hgc0, hg0, hgo0, _, _, hgneg0, hgzero0⟩ :=
    exists_supported_compression_scalar P hN he hopen isOpen_interior hSA0 hoc0 ho0
      (fun x => (hosign0 x).2.1) (fun x => (hosign0 x).1) hr hobound0
  let clip : ℝ → ℝ := fun u => min rp (max (-rm) u)
  have clip_eq (u : ℝ) (hu : -rm ≤ u ∧ u ≤ rp) : clip u = u := by
    simp only [clip, max_eq_right hu.1, min_eq_right hu.2]
  have clip_bound (u : ℝ) : -rm ≤ clip u ∧ clip u ≤ rp :=
    ⟨le_min (by linarith) (le_max_left _ _), min_le_left _ _⟩
  have clip_pos (u : ℝ) : 0 < clip u ↔ 0 < u := by
    simp only [clip, lt_min_iff, lt_max_iff, hp, true_and,
      not_lt.mpr (neg_nonpos.mpr hm.le), false_or]
  have clip_neg (u : ℝ) : clip u < 0 ↔ u < 0 := by
    simp only [clip, min_lt_iff, max_lt_iff, not_lt.mpr hp.le, false_or,
      neg_lt_zero.mpr hm, true_and]
  have clip_zero (u : ℝ) : clip u = 0 ↔ u = 0 := by
    constructor
    · intro h
      have hnp : ¬ 0 < u := fun hu => ((clip_pos u).mpr hu).ne' h
      have hnn : ¬ u < 0 := fun hu => ((clip_neg u).mpr hu).ne h
      linarith
    · rintro rfl
      exact clip_eq 0 ⟨by linarith, hp.le⟩
  let old := clip ∘ old0
  let g := clip ∘ g0
  have hoc : Continuous old := continuous_const.min (continuous_const.max hoc0)
  have hgc : Continuous g := continuous_const.min (continuous_const.max hgc0)
  have hclip {v : X → ℝ}
      (hv : ∀ i, LocallyPiecewiseAffineOn (v ∘ (e i).symm) (e i).target) (i : α) :
      LocallyPiecewiseAffineOn ((clip ∘ v) ∘ (e i).symm) (e i).target :=
    (locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 rp) (e i).open_target).min
      ((locallyPiecewiseAffineOn_affine (ContinuousAffineMap.const ℝ V3 (-rm))
        (e i).open_target).max (hv i))
  have ho := hclip ho0
  have hg := hclip hg0
  have hof : EqOn old f A0 := by
    intro x hx
    change clip (old0 x) = f x
    rw [hof0 hx]
    exact clip_eq _ (hbound x (hA0U hx))
  have hgbound (x : X) : -rm ≤ g x ∧ g x ≤ rp := clip_bound (g0 x)
  have hgo : EqOn g old (interior A)ᶜ := fun _ hx => congrArg clip (hgo0 hx)
  have hgneg (x : X) : x ∉ P.cutCarrier ↔ g x < 0 :=
    (hgneg0 x).trans (clip_neg (g0 x)).symm
  have hgzero : g ⁻¹' {0} = (frontier (sourceSlab phi a b) \ P.openStrip) ∪ P.endDisks := by
    ext x
    exact (clip_zero (g0 x)).trans (Set.ext_iff.mp hgzero0 x)
  let w : C(X, ℝ) := ⟨fun x => old x - g x, hoc.sub hgc⟩
  have hw (i : α) : LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target :=
    ((ho i).add (hg i).neg).congr (fun _ _ => (sub_eq_add_neg _ _).symm)
  have hAU : A ⊆ U := hAA0.trans (interior_subset.trans hA0U)
  have hwzero (x : X) (hx : x ∉ interior A) : w x = 0 := sub_eq_zero.mpr (hgo hx).symm
  have hwB (x : X) (hx : x ∈ frontier R) : w x = 0 := by
    apply hwzero
    exact fun h => disjoint_left.mp disjoint_interior_frontier
      (hUR (hAU (interior_subset h))) hx
  let psi := translatedMap phi w
  obtain ⟨hpsi, hF, hF0, hboundary⟩ := translatedMap_relative_properties hd hphi F0 w hw hwB
  have hfixed (x : R) (hx : (x : X) ∉ interior A) :
      ambientSourcePhase psi x = ambientSourcePhase phi x := by
    rw [ambientSourcePhase_translatedMap, hwzero _ hx, AddCircle.coe_zero, add_zero]
  have hnormal (x : X) (hx : x ∈ interior A) :
      ambientSourcePhase psi x = (b : C) - (g x : C) := by
    have hxA0 : x ∈ A0 := interior_subset (hAA0 (interior_subset hx))
    have hxR : x ∈ R := interior_subset (hUR (hAU (interior_subset hx)))
    rw [ambientSourcePhase_translatedMap phi w ⟨x, hxR⟩, hphase x (hA0U hxA0)]
    change (b : C) - (f x : C) + ((old x - g x : ℝ) : C) = _
    rw [← hof hxA0, AddCircle.coe_sub]
    abel
  have hUC : P.openStrip ⊆ P.closedStrip := image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hEC : P.endDisks ⊆ P.closedStrip := P.closedStrip_sdiff_openStrip.symm.subset.trans sdiff_subset
  have hsum : rm + rp < p := by linarith
  have hnota (u : ℝ) (hu : -rm ≤ u ∧ u ≤ rp) : (b : C) - (u : C) ≠ (a : C) := by
    intro h
    have huI : b - u ∈ Ico a (a + p) := by
      constructor <;> linarith [hu.1, hu.2]
    have haI : a ∈ Ico a (a + p) := by constructor <;> linarith
    rw [← AddCircle.coe_sub] at h
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico huI haI).mp h
    linarith [hu.2]
  refine ⟨psi, A, hA, heA, hSA, hAU, hpsi, hF, hF0, ?_, ?_, ?_, ?_, hboundary⟩
  · intro x hx
    change handleTranslation (w _, phi x) = phi x
    rw [hwzero _ hx, handleTranslation_zero]
  · ext x
    by_cases hx : x ∈ interior A
    · have hxU := hAU (interior_subset hx)
      have hxR := interior_subset (hUR hxU)
      have hqfront : x ∈ frontier (sourceSlab phi a b) ↔ x ∈ sourceSurface phi (b : C) := by
        rw [sourceSurface_eq_inter_phase]
        change _ ↔ x ∈ R ∧ ambientSourcePhase phi x = (b : C)
        rw [and_iff_right hxR, hphase x hxU, (AddCircle.bounded_sub_phase_eq p) hm hp hsum (hbound x hxU)]
        exact hzero x hxU
      rw [sourceSurface_eq_inter_phase psi]
      change (x ∈ R ∧ ambientSourcePhase psi x = (b : C)) ↔ _
      rw [and_iff_right hxR, hnormal x hx, (AddCircle.bounded_sub_phase_eq p) hm hp hsum (hgbound x)]
      exact (Set.ext_iff.mp hgzero x).trans (or_congr (and_congr hqfront Iff.rfl) Iff.rfl)
    · have hxopen : x ∉ P.openStrip := fun h => hx (hSA (hUC h))
      have hxend : x ∉ P.endDisks := fun h => hx (hSA (hEC h))
      rw [sourceSurface_eq_inter_phase psi, sourceSurface_eq_inter_phase phi]
      change (x ∈ R ∧ ambientSourcePhase psi x = (b : C)) ↔
        ((x ∈ R ∧ ambientSourcePhase phi x = (b : C)) ∧ x ∉ P.openStrip) ∨ x ∈ P.endDisks
      simp only [hxopen, hxend, not_false_eq_true, and_true, or_false]
      by_cases hxR : x ∈ R
      · rw [hfixed ⟨x, hxR⟩ hx]
      · simp only [hxR, false_and]
  · rw [sourceSurface_eq_inter_phase, sourceSurface_eq_inter_phase]
    ext x
    change (x ∈ R ∧ ambientSourcePhase psi x = (a : C)) ↔
      (x ∈ R ∧ ambientSourcePhase phi x = (a : C))
    by_cases hx : x ∈ interior A
    · have hxA0 : x ∈ A0 := interior_subset (hAA0 (interior_subset hx))
      rw [hnormal x hx, hphase x (hA0U hxA0)]
      simp only [hnota _ (hgbound x), hnota _ (hbound x (hA0U hxA0)), and_false]
    · by_cases hxR : x ∈ R
      · rw [hfixed ⟨x, hxR⟩ hx]
      · simp only [hxR, false_and]
  · ext x
    by_cases hx : x ∈ interior A
    · have hxR := interior_subset (hUR (hAU (interior_subset hx)))
      rw [sourceSlab_eq_inter_phase]
      change (x ∈ R ∧ ambientSourcePhase psi x ∈ AddCircle.closedIntervalArc p a b) ↔ _
      rw [and_iff_right hxR, hnormal x hx, (AddCircle.bounded_sub_mem_closedIntervalArc p) hm (hgbound x) hpgap hmgap]
      exact ⟨fun h => by by_contra hn; exact (not_lt_of_ge h) ((hgneg x).mp hn),
        fun h => le_of_not_gt (fun hn => (hgneg x).mpr hn h)⟩
    · have hxopen : x ∉ P.openStrip := fun h => hx (hSA (hUC h))
      change x ∈ sourceSlab psi a b ↔ x ∈ sourceSlab phi a b ∧ x ∉ P.openStrip
      rw [and_iff_left hxopen, sourceSlab_eq_inter_phase, sourceSlab_eq_inter_phase]
      change (x ∈ R ∧ ambientSourcePhase psi x ∈ AddCircle.closedIntervalArc p a b) ↔
        (x ∈ R ∧ ambientSourcePhase phi x ∈ AddCircle.closedIntervalArc p a b)
      by_cases hxR : x ∈ R
      · rw [hfixed ⟨x, hxR⟩ hx]
      · simp only [hxR, false_and]


end PoincareConjecture.M76.HamiltonIntervalTorus
