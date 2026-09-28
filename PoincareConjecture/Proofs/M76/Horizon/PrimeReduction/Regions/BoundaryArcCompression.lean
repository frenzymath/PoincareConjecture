import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLPrescribedBoundaryArc
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall
import PoincareConjecture.Proofs.M76.Mathlib.CompactParameterThickening
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedGraph

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V" => (ℝ × ℝ)

theorem exists_disk_compression_toward_boundary_arc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C rim w U : Set E} {a b : E}
    (hC : IsFinitePLBallPair V C rim) (hw : IsFinitePLBallPair ℝ w {a, b})
    (hab : a ≠ b) (hwr : w ⊆ rim) (hU : IsOpen U) (hwU : w ⊆ U) :
    ∃ f : E → E, FinitePiecewiseAffineOn f C ∧ InjOn f C ∧
      MapsTo f C (C ∩ U) ∧ EqOn f id w := by
  classical
  let I := Icc (0 : ℝ) 1
  let B : Set V := I ×ˢ I
  let q : Set V := ({0, 1} ×ˢ I) ∪ (I ×ˢ {0, 1})
  let base : Set V := I ×ˢ {0}
  let line : ℝ →ᴬ[ℝ] V :=
    (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ 0)
  have hline : line '' I = base := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht, rfl⟩
    · rintro ⟨hx, hy⟩
      exact ⟨z.1, hx, Prod.ext rfl hy.symm⟩
  have hbase : IsFinitePLBallPair ℝ base {((0 : ℝ), 0), (1, 0)} := by
    have hh := isFinitePLBallPair_affine_interval (show (0 : ℝ) < 1 by norm_num)
      line (fun _ _ _ _ h => congrArg Prod.fst h)
    change IsFinitePLBallPair ℝ (line '' I) {(0, 0), (1, 0)} at hh
    rwa [hline] at hh
  have hB : IsFinitePLBallPair V B q :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num))
  have hbaseq : base ⊆ q := fun z hz => Or.inr ⟨hz.1, Or.inl hz.2⟩
  have h01 : ((0, 0) : V) ≠ (1, 0) := by norm_num
  obtain ⟨v, hv, hwhole, hinter⟩ := hC.exists_boundary_arc_complement hw hwr hab
  obtain ⟨top, htop, hBwhole, hBinter⟩ :=
    hB.exists_boundary_arc_complement hbase hbaseq h01
  obtain ⟨e, he, hea, heb⟩ := hw.exists_marked_interval_homeomorph hbase hab h01
  have hends (x : w) : (x : E) ∈ ({a, b} : Set E) ↔
      (e x : V) ∈ ({(0, 0), (1, 0)} : Set V) := by
    simp only [mem_insert_iff, mem_singleton_iff, hea, heb]
  have hC' : IsFinitePLBallPair V C (v ∪ w) := by rwa [union_comm, hwhole]
  have hB' : IsFinitePLBallPair V B (top ∪ base) := by rwa [union_comm, hBwhole]
  obtain ⟨H, hH, _, _, hbaseH⟩ := hC'.exists_extension_of_boundary_piece hB'
    hv htop ((inter_comm _ _).trans hinter) ((inter_comm _ _).trans hBinter) e he hends
  let scale (t : ℝ) : V →ᴬ[ℝ] V :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
      (t • (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)
  have hscale (t : ℝ) (x : V) : scale t x = (x.1, t * x.2) := rfl
  have hscaleB (t : ℝ) (ht : t ∈ I) : MapsTo (scale t) B B := by
    rintro x ⟨hx, hy⟩
    exact ⟨hx, mul_nonneg ht.1 hy.1,
      (mul_le_mul_of_nonneg_left hy.2 ht.1).trans (by simpa using ht.2)⟩
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclamp (t : ℝ) : clamp t ∈ I :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hclamp0 : clamp 0 = 0 := by norm_num [clamp]
  let shrink : B × ℝ → B := fun z =>
    ⟨scale (clamp z.2) z.1, hscaleB _ (hclamp _) z.1.property⟩
  have hshrink : Continuous shrink := by
    apply Continuous.subtype_mk
    change Continuous (fun z : B × ℝ =>
      (((z.1 : V).1), max 0 (min 1 z.2) * (z.1 : V).2))
    fun_prop
  let family : B × ℝ → E := fun z => H.symm (shrink z)
  have hfamily : Continuous family := continuous_subtype_val.comp
    (H.symm.continuous.comp hshrink)
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  have hfamily0 (x : B) : family (x, 0) ∈ U := by
    apply hwU
    apply (hbaseH (H.symm (shrink (x, 0)))).mpr
    rw [H.apply_symm_apply]
    exact ⟨x.property.1, by change clamp 0 * (x : V).2 = 0; rw [hclamp0, zero_mul]⟩
  obtain ⟨δ, hδ, hsmall⟩ := hfamily.exists_pos_closedBall_thickening
    isCompact_univ hU (fun x _ => hfamily0 x)
  let t := min δ (1 / 2)
  have ht : 0 < t := lt_min hδ (by norm_num)
  have htI : t ∈ I := ⟨ht.le, (min_le_right _ _).trans (by norm_num)⟩
  have hct : clamp t = t := by
    dsimp only [clamp]
    rw [min_eq_right htI.2, max_eq_right ht.le]
  have htd : t ∈ Metric.closedBall (0 : ℝ) δ := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos ht]
    exact min_le_left _ _
  have hval (x : B) : family (x, t) =
      (H.symm ⟨scale t x, hscaleB t htI x.property⟩ : E) := by
    simp only [family, shrink, hct]
  obtain ⟨f₀, hf₀, hfval⟩ := hH
  have hH' : H.IsFinitePL := ⟨f₀, hf₀, hfval⟩
  obtain ⟨g, hg, hgval⟩ := hH'.symm
  have hfB : MapsTo f₀ C B := fun x hx => hfval ⟨x, hx⟩ ▸ (H ⟨x, hx⟩).property
  have hgC : MapsTo g B C := fun x hx => hgval ⟨x, hx⟩ ▸ (H.symm ⟨x, hx⟩).property
  have hfgi : LeftInvOn g f₀ C := by
    intro x hx
    rw [← hfval ⟨x, hx⟩, ← hgval, H.symm_apply_apply]
  have hgfi : LeftInvOn f₀ g B := by
    intro x hx
    rw [← hgval ⟨x, hx⟩, ← hfval, H.apply_symm_apply]
  let f := g ∘ scale t ∘ f₀
  have hf : FinitePiecewiseAffineOn f C :=
    hg.comp (hf₀.postcomp (scale t)) (fun x hx => hscaleB t htI (hfB hx))
  have hfi : InjOn f C := by
    intro x hx y hy hxy
    apply hfgi.injOn hx hy
    have hh := hgfi.injOn (hscaleB t htI (hfB hx)) (hscaleB t htI (hfB hy)) hxy
    rw [hscale, hscale] at hh
    apply Prod.ext
    · simpa only [Prod.fst] using congrArg (fun z : V => z.1) hh
    · exact mul_left_cancel₀ ht.ne' (congrArg (fun z : V => z.2) hh)
  refine ⟨f, hf, hfi, ?_, ?_⟩
  · intro x hx
    refine ⟨hgC (hscaleB t htI (hfB hx)), ?_⟩
    have h := hsmall (show (H ⟨x, hx⟩, t) ∈ (univ : Set B) ×ˢ Metric.closedBall 0 δ from
      ⟨mem_univ _, htd⟩)
    rw [hval, hgval] at h
    change g (scale t (H ⟨x, hx⟩)) ∈ U at h
    rw [hfval] at h
    exact h
  · intro x hx
    have hxC := hC.1 (hwr hx)
    have hxbase := (hbaseH ⟨x, hxC⟩).mp hx
    rw [hfval] at hxbase
    have hs : scale t (f₀ x) = f₀ x := by
      rw [hscale]
      apply Prod.ext
      · rfl
      · change t * (f₀ x).2 = (f₀ x).2
        rw [show (f₀ x).2 = 0 from hxbase.2, mul_zero]
    change g (scale t (f₀ x)) = x
    rw [hs, hfgi hxC]

end PoincareConjecture.M76
