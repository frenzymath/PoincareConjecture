import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.FinitePLPeriodLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates
import Mathlib.Topology.Homotopy.Lifting









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

theorem finitePiecewiseAffineOn_annular_real_lift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L d : ℝ} (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {r : E → ℝ × ℝ}
    (hr : ContinuousOn r K.space) (hheight : ∀ x ∈ K.space, (r x).2 ∈ Ioo (-d) d)
    (hf : FinitePiecewiseAffineOn
      (fun x => annulusMap L hL (((r x).1 : AddCircle (4 * L)), (r x).2)) K.space) :
    FinitePiecewiseAffineOn r K.space := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  obtain ⟨e, heS, heval, hePL⟩ := exists_annulus_PL_openPartialHomeomorph hL hd hwidth
  apply K.finitePiecewiseAffineOn_of_relative_local hK
  intro x
  let a := (r x).1 - 2 * L
  let Q := (AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
    (OpenPartialHomeomorph.refl ℝ)
  let C := Q.trans e
  have hxC : r x ∈ C.source := by
    change (((r x).1 ∈ Ioo a (a + 4 * L)) ∧ (r x).2 ∈ univ) ∧ Q (r x) ∈ e.source
    refine ⟨⟨⟨?_, ?_⟩, mem_univ _⟩, ?_⟩
    · dsimp [a]; linarith
    · dsimp [a]; linarith
    · rw [heS]
      exact ⟨mem_univ _, hheight x x.property⟩
  obtain ⟨N, W, hN, hNK, hW, hxW, hWN, hNW⟩ :=
    K.exists_relative_polyhedral_neighborhood hK x
      (C.open_source.preimage hr.domRestrict) hxC
  have hNsource (y : E) (hy : y ∈ N.space) : r y ∈ C.source :=
    hNW (show (⟨y, hNK hy⟩ : K.space) ∈ Subtype.val ⁻¹' N.space from hy)
  have hCv (y : E) : C (r y) =
      annulusMap L hL (((r y).1 : AddCircle (4 * L)), (r y).2) := by
    change e (Q (r y)) = _
    rw [heval]
    rfl
  have hCPL : C ∈ piecewiseAffineGroupoid (ℝ × ℝ) := hePL a
  have hInv := ((mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) C).mp hCPL).2
  have hlocal := hInv.comp_finitePiecewiseAffineOn (hf.restrict N hN hNK) (by
    intro y hy
    dsimp only
    rw [← hCv]
    exact C.mapsTo (hNsource y hy))
  have hrN : FinitePiecewiseAffineOn r N.space := hlocal.congr (by
    intro y hy
    change C.symm (annulusMap L hL (((r y).1 : AddCircle (4 * L)), (r y).2)) = r y
    rw [← hCv, C.left_inv (hNsource y hy)])
  obtain ⟨J, hJ, hJs, hrJ⟩ := hrN
  exact ⟨J, W, hJ, hW, hxW, fun y hy => hJs.symm.subset (hWN hy), hrJ⟩

local notation "I" => unitInterval
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

private instance : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩

theorem exists_finitePL_annular_arc_lift
    (gamma : C(I, Ann)) (hinj : Function.Injective gamma)
    (f : ℝ → ℝ × ℝ) (hf : FinitePiecewiseAffineOn f (Icc 0 1))
    (hfv : ∀ t : I, f t = (gamma t : ℝ × ℝ))
    (hzero : gamma 0 = annulusRimPoint false 0)
    (hone : gamma 1 = annulusRimPoint true 0) :
    ∃ (n : ℤ) (r : ℝ → ℝ × ℝ), FinitePiecewiseAffineOn r (Icc 0 1) ∧
      InjOn r (Icc 0 1) ∧ r 0 = (0, -1) ∧ r 1 = (32 * (n : ℝ), 1) ∧
      (∀ t : I, (r t).2 = depth 8 (gamma t : ℝ × ℝ)) ∧
      (∀ t : I, annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) = gamma t) ∧
      (∀ (t s : I) (k : ℤ), r t = r s + (32 * (k : ℝ), 0) → t = s ∧ k = 0) := by
  classical
  obtain ⟨C, hC⟩ := exists_annulus_homeomorph
    (by norm_num : (0 : ℝ) < 8) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : 4 * (1 : ℝ) < 8)
  let angular : C(I, Circle) :=
    ⟨fun t => (C.symm (gamma t)).1, continuous_fst.comp (C.symm.continuous.comp gamma.continuous)⟩
  have hCzero : C (0, ⟨-1, by simp⟩) = annulusRimPoint false 0 := Subtype.ext (hC _)
  have hCone : C (0, ⟨1, by simp⟩) = annulusRimPoint true 0 := Subtype.ext (hC _)
  have hangzero : angular 0 = (0 : ℝ) := by
    change (C.symm (gamma 0)).1 = _
    rw [hzero, ← hCzero, C.symm_apply_apply]
    rfl
  let cov := AddCircle.isCoveringMap_coe (4 * (8 : ℝ))
  let lift := cov.liftPath angular 0 hangzero
  have hlift (t : I) : (lift t : Circle) = angular t :=
    congrFun (cov.liftPath_lifts angular 0 hangzero) t
  have hliftzero : lift 0 = 0 := cov.liftPath_zero angular 0 hangzero
  have hliftone : (lift 1 : Circle) = 0 := by
    rw [hlift]
    change (C.symm (gamma 1)).1 = 0
    rw [hone, ← hCone, C.symm_apply_apply]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mp hliftone
  have hn' : lift 1 = 32 * (n : ℝ) := by
    rw [← hn]
    simp [zsmul_eq_mul]
    ring
  let rr : C(I, ℝ × ℝ) :=
    ⟨fun t => (lift t, ((C.symm (gamma t)).2 : ℝ)), by fun_prop⟩
  let r : ℝ → ℝ × ℝ := fun t => if ht : t ∈ Icc 0 1 then rr ⟨t, ht⟩ else 0
  have hrval (t : I) : r t = rr t := by simp only [r, dif_pos t.property]
  have hproject (t : I) :
      annulusMap 8 (by norm_num) (((r t).1 : Circle), (r t).2) = gamma t := by
    rw [hrval]
    change annulusMap 8 (by norm_num) ((lift t : Circle), ((C.symm (gamma t)).2 : ℝ)) = _
    rw [hlift]
    exact (hC (C.symm (gamma t))).symm.trans (congrArg Subtype.val (C.apply_symm_apply _))
  have hheight (t : I) : (r t).2 = depth 8 (gamma t : ℝ × ℝ) := by
    rw [← hproject t, depth_annulusMap (by norm_num) ?_]
    have ht := (C.symm (gamma t)).2.property
    rw [hrval]
    change 4 * |((C.symm (gamma t)).2 : ℝ)| < 8
    have := abs_le.mpr ht
    linarith
  have hfcopy := hf
  obtain ⟨K, hK, hKs, _⟩ := hfcopy
  have hrcont : ContinuousOn r K.space := by
    rw [hKs]
    exact continuousOn_iff_continuous_domRestrict.mpr
      (rr.continuous.congr fun t => (hrval t).symm)
  have hrPL : FinitePiecewiseAffineOn r (Icc 0 1) := by
    rw [← hKs]
    apply finitePiecewiseAffineOn_annular_real_lift (L := 8) (d := 3 / 2)
      (by norm_num) (by norm_num) (by norm_num) K hK hrcont
    · intro t ht
      rw [hrval ⟨t, hKs.subset ht⟩]
      have hv := (C.symm (gamma ⟨t, hKs.subset ht⟩)).2.property
      change -(3 / 2 : ℝ) < ((C.symm (gamma ⟨t, hKs.subset ht⟩)).2 : ℝ) ∧
        ((C.symm (gamma ⟨t, hKs.subset ht⟩)).2 : ℝ) < 3 / 2
      constructor <;> linarith [hv.1, hv.2]
    · apply (hKs.symm ▸ hf).congr
      intro t ht
      exact (hfv ⟨t, hKs.subset ht⟩).trans (hproject ⟨t, hKs.subset ht⟩).symm
  have htranslate (t s : I) (k : ℤ)
      (heq : r t = r s + (32 * (k : ℝ), 0)) : t = s ∧ k = 0 := by
    have hperiod : ((32 * (k : ℝ) : ℝ) : Circle) = 0 :=
      (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨k, by simp [zsmul_eq_mul]; ring⟩
    have hsame : gamma t = gamma s := by
      apply Subtype.ext
      rw [← hproject t, ← hproject s, heq]
      simp only [Prod.fst_add, Prod.snd_add, add_zero, AddCircle.coe_add, hperiod]
    have hts := hinj hsame
    refine ⟨hts, ?_⟩
    have he := congrArg Prod.fst heq
    rw [hts] at he
    have hk : (k : ℝ) = 0 := by change (r s).1 = (r s).1 + 32 * (k : ℝ) at he; linarith
    exact_mod_cast hk
  refine ⟨n, r, hrPL, ?_, ?_, ?_, hheight, hproject, htranslate⟩
  · intro t ht s hs heq
    exact congrArg Subtype.val (hinj (Subtype.ext ((hproject ⟨t, ht⟩).symm.trans
      ((congrArg (fun z : ℝ × ℝ => annulusMap 8 (by norm_num) ((z.1 : Circle), z.2)) heq).trans
        (hproject ⟨s, hs⟩)))))
  · change r ((0 : I) : ℝ) = _
    rw [hrval 0]
    change (lift 0, ((C.symm (gamma 0)).2 : ℝ)) = _
    rw [hliftzero, hzero, ← hCzero, C.symm_apply_apply]
  · change r ((1 : I) : ℝ) = _
    rw [hrval 1]
    change (lift 1, ((C.symm (gamma 1)).2 : ℝ)) = _
    rw [hn', hone, ← hCone, C.symm_apply_apply]

end PoincareConjecture.M76.Dehn
