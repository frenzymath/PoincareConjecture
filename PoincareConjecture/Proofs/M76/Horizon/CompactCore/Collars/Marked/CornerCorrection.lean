import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Corner.CentralInterval
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Corner.PlanarPatch
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Patches.Cylinder
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.OriginalProduct
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.FullBand

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

open Dehn.Annuli Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.exists_sheet_preserving_correction_of_corner_charts
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    {R S T D : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (he : PLDomain e R)
    (hopen : ∀ v : ℝ, 0 < v → v ≤ 1 →
      IsOpen ((Subtype.val : R → X) ⁻¹' (P.map '' (Disk ×ˢ Ioo (-v) v))) ∧
      IsOpen ((Subtype.val : frontier R → X) ⁻¹' (P.map '' (Rim ×ˢ Ioo (-v) v))))
    (hSclosed : IsClosed S) (hTclosed : IsClosed T)
    (hcover : frontier R ⊆ S ∪ T)
    (ends : Bool → V2) (hends : ∀ k, ends k ∈ Rim)
    (hends_ne : ends false ≠ ends true)
    (hseam : ∀ z ∈ Rim, j z ∈ S ∩ T ↔ ∃ k : Bool, z = ends k)
    (hD : j '' Disk ⊆ D)
    (B : ∀ k : Bool, OriginalSurfacePairChart e D T (j (ends k)) true)
    (sign : Bool → ℝ) (_hsign : ∀ k, sign k = -1 ∨ sign k = 1)
    (hSchart : ∀ k z, z ∈ (B k).coordinates.source →
      ((B k).chart.symm z ∈ S ↔ ((B k).coordinates z).1.2 = 0))
    (hfront : ∀ k z, z ∈ (B k).coordinates.source →
      ((B k).chart.symm z ∈ frontier R ↔
        (((B k).coordinates z).1.2 = 0 ∧ 0 ≤ sign k * ((B k).coordinates z).1.1) ∨
        (((B k).coordinates z).1.1 = 0 ∧ 0 ≤ ((B k).coordinates z).1.2))) :
    ∃ P' : OriginalDiskProduct e R j,
      P'.map '' (Disk ×ˢ I) ⊆ P.map '' (Disk ×ˢ I) ∧
      (∀ z ∈ Rim, ∀ t ∈ I,
        (P'.map (z, t) ∈ S ↔ j z ∈ S) ∧ (P'.map (z, t) ∈ T ↔ j z ∈ T)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 →
        IsOpen ((Subtype.val : R → X) ⁻¹' (P'.map '' (Disk ×ˢ Ioo (-v) v))) := by
  classical
  obtain ⟨H, hH, hmarks⟩ := exists_rim_homeomorph_at_two_points ends hends hends_ne
  obtain ⟨h, hhPL, hh⟩ := hH
  have hmid (i : Bool) : h (armPoint i (1 / 2)) = ends i :=
    (hh ⟨_, (armPoint_mem i (by norm_num)).1⟩).symm.trans (hmarks i)
  have hinterval (i : Bool) : ∃ a b : ℝ,
      0 < a ∧ a < 1 / 2 ∧ 1 / 2 < b ∧ b < 1 ∧
      PolyhedralPLInCharts e (j ∘ h ∘ armPoint i) (Icc a b) ∧
      InjOn (j ∘ h ∘ armPoint i) (Icc a b) ∧
      MapsTo (j ∘ h ∘ armPoint i) (Icc a b) (B i).chart.source ∧
      MapsTo ((B i).chart ∘ (j ∘ h ∘ armPoint i)) (Icc a b) (B i).coordinates.source := by
    exact P.exists_corner_central_interval H hhPL hh i (B i) (congrArg j (hmid i))
  choose a b ha ham hmb hb hp hpi hps hpc using hinterval
  have hH : H.IsFinitePL := ⟨h, hhPL, hh⟩
  choose w g hw hwsmall hg hgi hgmap hg0 hgz hgmark using fun i =>
    P.exists_corner_planar_patch he (hopen (1 / 2) (by norm_num) (by norm_num)).1
      hD (B i) (sign i) (hSchart i) (hfront i) H hH h hh i
      (ha i).le (lt_trans (ham i) (hmb i)) (hb i).le
      (hp i) (hpi i) (hps i) (hpc i) (fun _ _ => rfl)
  obtain ⟨o, G, hG, hfixed, hformula⟩ := exists_rimCylinder_correction_with_signed_formula
    a b w (fun i => by linarith [ha i]) (fun i => lt_trans (ham i) (hmb i))
      (fun i => by linarith [hb i]) hw hwsmall g hg hgi hgmap hg0 hgz
  obtain ⟨G', hG', hfixed', hconj⟩ := exists_conjugate_rimCylinder_correction H hH G hG hfixed
  obtain ⟨F, hF, hFi, hFfront, hF0, hFo, hFvalue⟩ :=
    exists_full_original_band_of_cylinder_correction P
      (hopen (1 / 2) (by norm_num) (by norm_num)).2 G' hG'
      (fun z hz => hfixed' _ (Or.inl rfl)) (fun z hz => hfixed' z (Or.inr hz))
  let U : Bool → Set Rim := fun i => {z |
    0 < TubeExterior.CornerBands.sign i * (H.symm z : V2) 0 ∧
      armPhase i (H.symm z) ∈ Ioo (a i) (b i)}
  have hU (i) : IsOpen (U i) := by
    have hc : Continuous (fun z : Rim => (H.symm z : V2)) :=
      continuous_subtype_val.comp H.symm.continuous
    exact (isOpen_lt continuous_const (continuous_const.mul ((continuous_apply 0).comp hc))).inter
      (isOpen_Ioo.preimage ((continuous_armPhase i).comp hc))
  have hseamU (z : Rim) (hz : j z ∈ S ∩ T) : z ∈ ⋃ i, U i := by
    obtain ⟨i, hi⟩ := (hseam z z.property).mp hz
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    have hzi : z = H ⟨armPoint i (1 / 2), (armPoint_mem i (by norm_num)).1⟩ :=
      Subtype.ext (hi.trans (hmarks i).symm)
    change 0 < TubeExterior.CornerBands.sign i * (H.symm z : V2) 0 ∧ _
    rw [hzi, H.symm_apply_apply]
    constructor
    · exact (armPoint_mem i (show (1 / 2 : ℝ) ∈ Ioo (-(1 / 2 : ℝ)) (3 / 2) by norm_num)).2
    · change armPhase i (armPoint i (1 / 2)) ∈ Ioo (a i) (b i)
      rw [armPhase_armPoint i (by norm_num)]
      exact ⟨ham i, hmb i⟩
  let r := min (w false) (w true)
  have hr : 0 < r := lt_min (hw false) (hw true)
  have hrw (i : Bool) : r ≤ w i := by
    cases i
    · exact min_le_left _ _
    · exact min_le_right _ _
  apply P.exists_sheet_preserving_correction he (fun v hv hv1 => (hopen v hv hv1).1)
    hF hFi hFfront hF0 hFo hSclosed hTclosed hcover (isOpen_iUnion hU) hseamU hr
  intro z hz t ht htr
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
  let s := armPhase i (H.symm z)
  have hs : s ∈ Icc (a i) (b i) := Ioo_subset_Icc_self hzi.2
  have harm : armPoint i s = (H.symm z : V2) :=
    armPoint_armPhase i (H.symm z).property hzi.1
  have hbase : h (armPoint i s) = (z : V2) := by
    rw [harm, ← hh (H.symm z), H.apply_symm_apply]
  let x : rimCylinder := ⟨((H.symm z : V2), t / 2), (H.symm z).property,
    by linarith [ht.1], by linarith [ht.2]⟩
  have htbound : |t / 2| ≤ w i / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (htr.trans (hrw i)) (by norm_num)
  have hx : (x : E) = (armPoint i s, t / 2) := Prod.ext harm.symm rfl
  have hGx := hformula i s (t / 2) x hs htbound hx
  have hCx : (⟨halfBandScale ((z : V2), t), halfBandScale_mem.mpr ⟨z.property, ht⟩⟩ :
      rimCylinder) = rimCylinderReparam H x := by
    apply Subtype.ext
    simp [x]
  have hvalue : F ((z : V2), t) = P.map
      (h (armPoint i (g i (TubeExterior.CornerBands.sign (o i) * (t / 2), s)).1),
        (g i (TubeExterior.CornerBands.sign (o i) * (t / 2), s)).2) := by
    have hCvalue : (rimCylinderReparam H (G x) : E) =
        (h (G x : E).1, (G x : E).2) := by
      rw [rimCylinderReparam_apply, hh]
    exact (hFvalue _ ⟨z.property, ht⟩).trans
      ((congrArg (fun q : rimCylinder => P.map (G' q)) hCx).trans
        ((congrArg (fun q : rimCylinder => P.map q) (hconj x)).trans
          (congrArg P.map (hCvalue.trans
            (congrArg (fun p : E => (h p.1, p.2)) hGx)))))
  have hpbox : (TubeExterior.CornerBands.sign (o i) * (t / 2), s) ∈
      Icc (-w i) (w i) ×ˢ Icc (a i) (b i) := by
    refine ⟨?_, hs⟩
    have habs := abs_le.mp htbound
    cases o i <;> simp only [TubeExterior.CornerBands.sign, Bool.false_eq_true, if_false,
      if_true, one_mul, neg_one_mul]
    all_goals constructor <;> linarith [habs.1, habs.2, hw i]
  have hmark := hgmark i _ hpbox
  dsimp only [Function.comp_apply] at hmark
  rw [hbase] at hmark
  rw [hvalue]
  exact and_congr hmark.1 hmark.2

end PoincareConjecture.M76
