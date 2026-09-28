import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Compression.Homotopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.SupportedScalar
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_hamiltonZero_third_coordinate_compression_map
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} {a b : ℝ}
    {j : (Fin 2 → ℝ) → X0}
    (P : OriginalDiskProduct e
      (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) j)
    (hN : IsCompact (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (he : PLDomain e (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hopen : IsOpen ((Subtype.val :
      ↥(R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) → X0) ⁻¹' P.openStrip))
    {U : Set X0} (hU : IsOpen U) (hUR : U ⊆ interior R) (hSU : P.closedStrip ⊆ U)
    {f : X0 → ℝ} (hf : ContinuousOn f U)
    (hfPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' U))
    (hphase : ∀ x ∈ U, hamiltonZeroThirdCircleMap phi x = (a : C0) + (f x : C0))
    (hpos : ∀ x ∈ U,
      x ∈ interior (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ↔ 0 < f x)
    (hzero : ∀ x ∈ U,
      x ∈ frontier (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ↔ f x = 0)
    {rm rp : ℝ} (hm : 0 < rm) (hp : 0 < rp)
    (hpgap : rp < b - a) (hmgap : rm < p - (b - a))
    (hbound : ∀ x ∈ U, -rm ≤ f x ∧ f x ≤ rp) :
    ∃ (psi : C(H0, H0)) (A : Set X0) (G : C(unitInterval × X0, X0)),
      IsCompact A ∧ PLDomain e A ∧ P.closedStrip ⊆ interior A ∧ A ⊆ U ∧
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ x, G (1, x) = hamiltonZeroAmbientMap psi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ interior A →
        G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0),
        (Q0 (G (t, x))).2 = hamiltonZeroCircleMap phi x) ∧
      (∀ (t : unitInterval) (x : X0),
        (Q0 (G (t, x))).1.2 = hamiltonZeroSecondCircleMap phi x) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(a : C0)}) =
        ((R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}) \ P.openStrip) ∪ P.endDisks ∧
      (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' {(b : C0)}) =
        (R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(b : C0)}) ∧
      (R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
        P.cutCarrier := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : LocallyCompactSpace X0 := he.locallyCompactSpace
  let N := R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b
  obtain ⟨A0, hA0, hSA0, hA0U, hhalf⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_halfspace_neighborhood e he.compatible he.cover
      (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)) hU hSU
  have heA0 : PLDomain e A0 := ⟨he.cover, he.compatible, hA0.isClosed, hhalf⟩
  let r := max rm rp
  have hr : 0 < r := lt_of_lt_of_le hm (le_max_left _ _)
  have hfbound (x : X0) (hx : x ∈ U) : |f x| ≤ r :=
    abs_le.mpr ⟨(neg_le_neg (le_max_left _ _)).trans (hbound x hx).1,
      (hbound x hx).2.trans (le_max_right _ _)⟩
  obtain ⟨old0, hoc0, ho0, hof0, hobound0, hosign0⟩ :=
    HamiltonIntervalTorus.exists_compact_domain_relative_defining_function he hN heA0 hA0
      hU hA0U hf hfPL (fun x hx => hpos x (hA0U hx))
      (fun x hx => hzero x (hA0U hx)) hr (fun x hx => hfbound x (hA0U hx))
  obtain ⟨g0, A, hA, heA, hSA, hAA0, hgc0, hg0, hgo0, _, _, hgneg0, hgzero0⟩ :=
    HamiltonIntervalTorus.exists_supported_compression_scalar P hN he hopen isOpen_interior
      hSA0 hoc0 ho0 (fun x => (hosign0 x).2.1) (fun x => (hosign0 x).1) hr hobound0
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
  have hclip {v : X0 → ℝ}
      (hv : ∀ i, LocallyPiecewiseAffineOn (v ∘ (e i).symm) (e i).target) (i : ι) :
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
  have hgbound (x : X0) : -rm ≤ g x ∧ g x ≤ rp := clip_bound (g0 x)
  have hgo : EqOn g old (interior A)ᶜ := fun _ hx => congrArg clip (hgo0 hx)
  have hgneg (x : X0) : x ∉ P.cutCarrier ↔ g x < 0 :=
    (hgneg0 x).trans (clip_neg (g0 x)).symm
  have hgzero : g ⁻¹' {0} = (frontier N \ P.openStrip) ∪ P.endDisks := by
    ext x
    exact (clip_zero (g0 x)).trans (Set.ext_iff.mp hgzero0 x)
  let w : C(X0, ℝ) := ⟨fun x => g x - old x, hgc.sub hoc⟩
  have hw (i : ι) : LocallyPiecewiseAffineOn (w ∘ (e i).symm) (e i).target :=
    ((hg i).add (ho i).neg).congr (fun _ _ => (sub_eq_add_neg _ _).symm)
  have hAU : A ⊆ U := hAA0.trans (interior_subset.trans hA0U)
  have hwzero (x : X0) (hx : x ∉ interior A) : w x = 0 := sub_eq_zero.mpr (hgo hx)
  obtain ⟨psi, hPL, hF, hF0, hfirst, hsecond, hthird, G, hG⟩ :=
    hphi.exists_hamiltonZero_third_scalar_homotopy hd F0 w hw hwzero
  have hnormal (t : unitInterval) (x : X0) :
      (Q0 (G (t, x))).2 = hamiltonZeroCircleMap phi x := by
    have h := congrArg Prod.snd (hG t x)
    exact h
  have hsecondnormal (t : unitInterval) (x : X0) :
      (Q0 (G (t, x))).1.2 = hamiltonZeroSecondCircleMap phi x := by
    have h := congrArg (fun z : (C0 × C0) × C0 => z.1.2) (hG t x)
    exact h
  have hqfixed (x : X0) (hx : x ∉ interior A) :
      hamiltonZeroThirdCircleMap psi x = hamiltonZeroThirdCircleMap phi x := by
    rw [hthird, hwzero x hx, AddCircle.coe_zero, add_zero]
  have hqnew (x : X0) (hx : x ∈ interior A) :
      hamiltonZeroThirdCircleMap psi x = (a : C0) + (g x : C0) := by
    have hxA0 : x ∈ A0 := interior_subset (hAA0 (interior_subset hx))
    rw [hthird, hphase x (hA0U hxA0)]
    change (a : C0) + (f x : C0) + ((g x - old x : ℝ) : C0) = _
    rw [← hof hxA0, AddCircle.coe_sub]
    abel
  have hUC : P.openStrip ⊆ P.closedStrip := image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hEC : P.endDisks ⊆ P.closedStrip := P.closedStrip_sdiff_openStrip.symm.subset.trans sdiff_subset
  have hsum : rm + rp < p := by linarith
  have hnotb (u : ℝ) (hu : -rm ≤ u ∧ u ≤ rp) : (a : C0) + (u : C0) ≠ (b : C0) := by
    intro h
    have huI : a + u ∈ Ico (a - rm) (a - rm + p) := by
      constructor <;> linarith [hu.1, hu.2]
    have hbI : b ∈ Ico (a - rm) (a - rm + p) := by constructor <;> linarith
    rw [← AddCircle.coe_add] at h
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico huI hbI).mp h
    linarith [hu.2]
  refine ⟨psi, A, G.toHomotopy.toContinuousMap, hA, heA, hSA, hAU,
    G.apply_zero, G.apply_one, (fun t x hx => G.prop t x hx), hnormal,
    hsecondnormal, hPL, hF, hF0, hfirst, hsecond, ?_, ?_, ?_⟩
  · ext x
    by_cases hx : x ∈ interior A
    · have hxU := hAU (interior_subset hx)
      have hxR := interior_subset (hUR hxU)
      have hqfront : x ∈ frontier N ↔ x ∈ R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)} := by
        change _ ↔ x ∈ R ∧ hamiltonZeroThirdCircleMap phi x = (a : C0)
        rw [and_iff_right hxR, hphase x hxU,
          (AddCircle.bounded_add_phase_eq p) hm hp hsum (hbound x hxU)]
        exact hzero x hxU
      change (x ∈ R ∧ hamiltonZeroThirdCircleMap psi x = (a : C0)) ↔ _
      rw [and_iff_right hxR, hqnew x hx, (AddCircle.bounded_add_phase_eq p) hm hp hsum (hgbound x)]
      exact (Set.ext_iff.mp hgzero x).trans (or_congr (and_congr hqfront Iff.rfl) Iff.rfl)
    · have hxopen : x ∉ P.openStrip := fun h => hx (hSA (hUC h))
      have hxend : x ∉ P.endDisks := fun h => hx (hSA (hEC h))
      change (x ∈ R ∧ hamiltonZeroThirdCircleMap psi x = (a : C0)) ↔
        ((x ∈ R ∧ hamiltonZeroThirdCircleMap phi x = (a : C0)) ∧ x ∉ P.openStrip) ∨ x ∈ P.endDisks
      rw [hqfixed x hx]
      simp only [hxopen, hxend, not_false_eq_true, and_true, or_false]
  · ext x
    change (x ∈ R ∧ hamiltonZeroThirdCircleMap psi x = (b : C0)) ↔
      (x ∈ R ∧ hamiltonZeroThirdCircleMap phi x = (b : C0))
    by_cases hx : x ∈ interior A
    · have hxA0 : x ∈ A0 := interior_subset (hAA0 (interior_subset hx))
      rw [hqnew x hx, hphase x (hA0U hxA0)]
      simp only [hnotb _ (hgbound x), hnotb _ (hbound x (hA0U hxA0)), and_false]
    · rw [hqfixed x hx]
  · ext x
    by_cases hx : x ∈ interior A
    · have hxR := interior_subset (hUR (hAU (interior_subset hx)))
      change (x ∈ R ∧ hamiltonZeroThirdCircleMap psi x ∈ AddCircle.closedIntervalArc p a b) ↔ _
      rw [and_iff_right hxR, hqnew x hx,
        (AddCircle.bounded_add_mem_closedIntervalArc p) hm (hgbound x) hpgap hmgap]
      exact ⟨fun h => by by_contra hn; exact (not_lt_of_ge h) ((hgneg x).mp hn),
        fun h => le_of_not_gt (fun hn => (hgneg x).mpr hn h)⟩
    · have hxopen : x ∉ P.openStrip := fun h => hx (hSA (hUC h))
      change (x ∈ R ∧ hamiltonZeroThirdCircleMap psi x ∈ AddCircle.closedIntervalArc p a b) ↔
        (x ∈ R ∧ hamiltonZeroThirdCircleMap phi x ∈ AddCircle.closedIntervalArc p a b) ∧ x ∉ P.openStrip
      rw [and_iff_left hxopen, hqfixed x hx]

end PoincareConjecture.M76
