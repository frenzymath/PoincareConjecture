import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInitialSegment
import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms
import PoincareConjecture.Proofs.M76.Mathlib.CentralLinkSigns
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine









set_option autoImplicit false

open Set Metric Geometry Topology Filter unitInterval
open scoped Topology

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)



theorem link_zero_ncard_of_crossing_chart (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    (hzero : (0 : V3) ∈ K.vertices) (ell : V3 →ₗ[ℝ] ℝ)
    (H : OpenPartialHomeomorph V3 C3) (hsource : (0 : V3) ∈ H.source)
    (hcenter : H 0 = 0) (hinverse : LocallyPiecewiseAffineOn H.symm H.target)
    (hsection : ∀ x ∈ H.source, x ∈ K.space ∩ {z | ell z = 0} ↔
      (H x).1.1 = 0 ∧ (H x).2 = 0) :
    ((K.link 0).space ∩ {x | ell x = 0}).ncard = 2 := by
  have htarget : (0 : C3) ∈ H.target := hcenter ▸ H.map_source hsource
  have hinvzero : H.symm 0 = 0 := by
    rw [← hcenter]
    exact H.left_inv hsource
  obtain ⟨N, hN, hzeroN, hNH, hNaff⟩ := hinverse 0 htarget
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 hzeroN
  let d := r / 2
  have hd : 0 < d := half_pos hr
  have hdr : d < r := half_lt_self hr
  let axis : ℝ →L[ℝ] C3 :=
    { toLinearMap :=
        { toFun := fun z => ((0, z), 0)
          map_add' := by intros; ext <;> simp
          map_smul' := by intros; ext <;> simp }
      cont := by fun_prop }
  have hnorm (z : ℝ) : ‖axis z‖ = |z| := by
    simp [axis, Prod.norm_def, Real.norm_eq_abs]
  have small (k : ℝ) (hk : |k| = d) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
      axis (k * u) ∈ N.space := by
    apply interior_subset (hball ?_)
    rw [mem_ball, dist_zero_right, hnorm, abs_mul, hk, abs_of_nonneg hu.1]
    exact (mul_le_of_le_one_right hd.le hu.2).trans_lt hdr
  have initial (k : ℝ) (hk : |k| = d) :
      ∃ δ ∈ Ioc (0 : ℝ) 1, ∃ v : V3, v ≠ 0 ∧
        ∀ u ∈ Icc (0 : ℝ) 1,
          u • v ∈ H.source ∧ H (u • v) = axis (k * δ * u) := by
    let a : ℝ →ᴬ[ℝ] C3 :=
      axis.toContinuousAffineMap.comp (k • ContinuousAffineMap.id ℝ ℝ)
    have ha : MapsTo a (Icc (0 : ℝ) 1) N.space := fun _ hu => small k hk hu
    obtain ⟨δ, hδ, A, hA⟩ :=
      (hNaff.finitePiecewiseAffineOn hN).exists_initial_affine_segment a ha
    have hA0 : A 0 = 0 := by
      have h := hA ⟨le_rfl, hδ.1.le⟩
      change H.symm (axis (k * 0)) = A 0 at h
      rw [mul_zero, map_zero, hinvzero] at h
      exact h.symm
    have hlin (u : ℝ) : A u = u • A 1 := by
      have h := A.toAffineMap.apply_lineMap (0 : ℝ) 1 u
      change A (AffineMap.lineMap 0 1 u) = AffineMap.lineMap (A 0) (A 1) u at h
      simpa [AffineMap.lineMap_apply_ring', AffineMap.lineMap_apply_module', hA0] using h
    let v := δ • A 1
    have hmap (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
        u • v ∈ H.source ∧ H (u • v) = axis (k * δ * u) := by
      have hdu : δ * u ∈ Icc (0 : ℝ) δ :=
        ⟨mul_nonneg hδ.1.le hu.1, mul_le_of_le_one_right hδ.1.le hu.2⟩
      have hdu1 : δ * u ∈ Icc (0 : ℝ) 1 := ⟨hdu.1, hdu.2.trans hδ.2⟩
      have hval : H.symm (axis (k * δ * u)) = u • v := by
        have h := (hA hdu).trans (hlin (δ * u))
        change H.symm (axis (k * (δ * u))) = (δ * u) • A 1 at h
        simpa only [v, smul_smul, mul_assoc, mul_comm δ u] using h
      have hpoint : axis (k * δ * u) ∈ H.target := by
        apply hNH
        simpa only [mul_assoc] using small k hk hdu1
      exact ⟨hval ▸ H.map_target hpoint, by rw [← hval]; exact H.right_inv hpoint⟩
    have hv : v ≠ 0 := by
      intro hv0
      have h := (hmap 1 (by simp)).2
      rw [one_smul, hv0, hcenter, mul_one] at h
      have hkδ : k * δ = 0 := (congrArg (fun x : C3 => x.1.2) h).symm
      have hk0 : k ≠ 0 := by
        intro hk0
        have hd0 : d = 0 := by simpa only [hk0, abs_zero] using hk.symm
        exact hd.ne' hd0
      exact (mul_ne_zero hk0 hδ.1.ne') hkδ
    exact ⟨δ, hδ, v, hv, hmap⟩
  obtain ⟨a, ha, u, hu, hplus⟩ := initial d (abs_of_pos hd)
  obtain ⟨b, hb, v, hv, hminus⟩ := initial (-d) (by rw [abs_neg, abs_of_pos hd])
  have hda : 0 < d * a := mul_pos hd ha.1
  have hdb : 0 < d * b := mul_pos hd hb.1
  have radial (w : V3) {x : V3} (hx : x ∈ segment ℝ 0 w) :
      ∃ u ∈ Icc (0 : ℝ) 1, u • w = x := by
    obtain ⟨u, hu, hux⟩ := (segment_eq_image_lineMap ℝ (0 : V3) w).subset hx
    exact ⟨u, hu, by simpa [AffineMap.lineMap_apply_module] using hux⟩
  have hinter : segment ℝ 0 u ∩ segment ℝ 0 v ⊆ {0} := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := radial u hx.1
    obtain ⟨j, hj, hjx⟩ := radial v hx.2
    have heq : H (i • u) = H (j • v) := congrArg H (hix.trans hjx.symm)
    rw [(hplus i hi).2, (hminus j hj).2] at heq
    have hcoeff : d * a * i = -d * b * j := congrArg (fun z : C3 => z.1.2) heq
    have hprod : d * a * i = 0 := by
      apply le_antisymm
      · rw [hcoeff]
        simp only [neg_mul]
        exact neg_nonpos.mpr (mul_nonneg hdb.le hj.1)
      · exact mul_nonneg hda.le hi.1
    have hi0 := (mul_eq_zero.mp hprod).resolve_left hda.ne'
    exact hix.symm.trans (by rw [hi0, zero_smul])
  let O : Set C3 := {x | -(d * b) < x.1.2 ∧ x.1.2 < d * a}
  have hO : IsOpen O :=
    (isOpen_lt continuous_const (continuous_snd.comp continuous_fst)).inter
      (isOpen_lt (continuous_snd.comp continuous_fst) continuous_const)
  have hzeroO : H 0 ∈ O := by
    rw [hcenter]
    exact ⟨neg_neg_of_pos hdb, hda⟩
  have hlocal : ∀ᶠ x in 𝓝 (0 : V3), x ∈ K.space ∩ {z | ell z = 0} ↔
      x ∈ segment ℝ 0 u ∪ segment ℝ 0 v := by
    filter_upwards [(H.isOpen_inter_preimage hO).mem_nhds ⟨hsource, hzeroO⟩] with x hx
    constructor
    · intro hsectionx
      have haxes := (hsection x hx.1).mp hsectionx
      have hxaxis : H x = axis (H x).1.2 := Prod.ext (Prod.ext haxes.1 rfl) haxes.2
      by_cases hn : 0 ≤ (H x).1.2
      · let t := (H x).1.2 / (d * a)
        have ht : t ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg hn hda.le, (div_le_one hda).mpr hx.2.2.le⟩
        have htx : t • u = x := H.injOn (hplus t ht).1 hx.1 (by
          rw [(hplus t ht).2, hxaxis]
          dsimp only [t]
          rw [mul_div_cancel₀ _ hda.ne'])
        exact Or.inl (htx ▸ (convex_segment (0 : V3) u).smul_mem_of_zero_mem
          (left_mem_segment ℝ 0 u) (right_mem_segment ℝ 0 u) ht)
      · have hn' : (H x).1.2 ≤ 0 := le_of_not_ge hn
        let t := -(H x).1.2 / (d * b)
        have ht : t ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg (neg_nonneg.mpr hn') hdb.le,
            (div_le_one hdb).mpr (by linarith [hx.2.1])⟩
        have htx : t • v = x := H.injOn (hminus t ht).1 hx.1 (by
          rw [(hminus t ht).2, hxaxis]
          dsimp only [t]
          rw [neg_mul, neg_mul, mul_div_cancel₀ _ hdb.ne', neg_neg])
        exact Or.inr (htx ▸ (convex_segment (0 : V3) v).smul_mem_of_zero_mem
          (left_mem_segment ℝ 0 v) (right_mem_segment ℝ 0 v) ht)
    · intro hsegment
      apply (hsection x hx.1).mpr
      rcases hsegment with hxu | hxv
      · obtain ⟨i, hi, rfl⟩ := radial u hxu
        rw [(hplus i hi).2]
        exact ⟨rfl, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := radial v hxv
        rw [(hminus i hi).2]
        exact ⟨rfl, rfl⟩
  exact K.ncard_link_zero_of_local_segments hK hzero ell hu hv hinter hlocal



theorem signed_approach_of_crossing_chart (K : SimplicialComplex ℝ V3) (ell : V3 →L[ℝ] ℝ)
    (w : V3) (hw : ell w = 1) (H : OpenPartialHomeomorph V3 C3)
    (hsource : (0 : V3) ∈ H.source) (hcenter : H 0 = 0)
    (hflat : ∀ x ∈ H.source, ell x = 0 ↔ (H x).2 = 0)
    (hsheet : ∀ x ∈ H.source, x ∈ K.space ↔ (H x).1.1 = 0) :
    (0 : V3) ∈ closure (K.space ∩ {x | 0 < ell x}) ∧
      (0 : V3) ∈ closure (K.space ∩ {x | ell x < 0}) := by
  have htarget : (0 : C3) ∈ H.target := hcenter ▸ H.map_source hsource
  have hinvzero : H.symm 0 = 0 := by
    rw [← hcenter]
    exact H.left_inv hsource
  have positive (L : V3 →L[ℝ] ℝ) (w : V3) (hw : L w = 1)
      (hflat : ∀ x ∈ H.source, L x = 0 ↔ (H x).2 = 0) :
      (0 : V3) ∈ closure (K.space ∩ {x | 0 < L x}) := by
    apply _root_.mem_closure_iff.mpr
    intro N hN hzeroN
    have hN' := H.symm.isOpen_inter_preimage hN
    have hzeroN' : (0 : C3) ∈ H.target ∩ H.symm ⁻¹' N := by
      refine ⟨htarget, ?_⟩
      change H.symm 0 ∈ N
      rw [hinvzero]
      exact hzeroN
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN' 0 hzeroN'
    let I₀ := Ioo (-r) r
    let P := (I₀ ×ˢ I₀) ×ˢ I₀
    have hPopen : IsOpen P := (isOpen_Ioo.prod isOpen_Ioo).prod isOpen_Ioo
    have hzeroP : (0 : C3) ∈ P := by
      have hz : (0 : ℝ) ∈ I₀ := ⟨neg_neg_of_pos hr, hr⟩
      exact ⟨⟨hz, hz⟩, hz⟩
    have hP (z : C3) (hz : z ∈ P) : z ∈ H.target ∩ H.symm ⁻¹' N := by
      apply hball
      rw [mem_ball, dist_zero_right, Prod.norm_def, Prod.norm_def]
      simp only [Real.norm_eq_abs, max_lt_iff, abs_lt]
      exact hz
    have hpre : H.source ∩ H ⁻¹' P ∈ 𝓝 (0 : V3) := by
      apply (H.isOpen_inter_preimage hPopen).mem_nhds
      refine ⟨hsource, ?_⟩
      change H 0 ∈ P
      rw [hcenter]
      exact hzeroP
    obtain ⟨a, ha, haw⟩ := Set.exists_pos_smul_mem_of_mem_nhds hpre w
    have hawpos : 0 < L (a • w) := by rw [map_smul, hw, smul_eq_mul, mul_one]; exact ha.1
    let f : C3 → ℝ := L ∘ H.symm
    have hf : ContinuousOn f P :=
      L.continuous.comp_continuousOn (H.continuousOn_symm.mono fun z hz => (hP z hz).1)
    have hfv : 0 < f (H (a • w)) := by
      change 0 < L (H.symm (H (a • w)))
      rw [H.left_inv haw.1]
      exact hawpos
    have hnz : (H (a • w)).2 ≠ 0 := fun h =>
      hawpos.ne' ((hflat _ haw.1).mpr h)
    have nonzero (z : C3) (hz : z ∈ P) (hz0 : z.2 ≠ 0) : f z ≠ 0 := by
      intro heq
      have h := (hflat _ (H.map_target (hP z hz).1)).mp heq
      rw [H.right_inv (hP z hz).1] at h
      exact hz0 h
    rcases lt_or_gt_of_ne hnz with hneg | hpos
    · let z : C3 := ((0, 0), -(r / 2))
      have hz : z ∈ (I₀ ×ˢ I₀) ×ˢ Ioo (-r) 0 := by
        dsimp only [z, I₀]
        exact ⟨hzeroP.1, ⟨by linarith, by linarith⟩⟩
      have hsub : (I₀ ×ˢ I₀) ×ˢ Ioo (-r) 0 ⊆ P :=
        fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hr⟩
      have hzpos : 0 < f z :=
        ((isPreconnected_Ioo.prod isPreconnected_Ioo).prod isPreconnected_Ioo).lt_of_ne
          (hf.mono hsub) (fun z hz => nonzero z (hsub hz) hz.2.2.ne)
          ⟨H (a • w), ⟨haw.2.1, haw.2.2.1, hneg⟩, hfv⟩ hz
      refine ⟨H.symm z, (hP z (hsub hz)).2, ?_, hzpos⟩
      apply (hsheet _ (H.map_target (hP z (hsub hz)).1)).mpr
      rw [H.right_inv (hP z (hsub hz)).1]
    · let z : C3 := ((0, 0), r / 2)
      have hz : z ∈ (I₀ ×ˢ I₀) ×ˢ Ioo 0 r := by
        dsimp only [z, I₀]
        exact ⟨hzeroP.1, ⟨half_pos hr, half_lt_self hr⟩⟩
      have hsub : (I₀ ×ˢ I₀) ×ˢ Ioo 0 r ⊆ P :=
        fun z hz => ⟨hz.1, (neg_neg_of_pos hr).trans hz.2.1, hz.2.2⟩
      have hzpos : 0 < f z :=
        ((isPreconnected_Ioo.prod isPreconnected_Ioo).prod isPreconnected_Ioo).lt_of_ne
          (hf.mono hsub) (fun z hz => nonzero z (hsub hz) hz.2.1.ne')
          ⟨H (a • w), ⟨haw.2.1, hpos, haw.2.2.2⟩, hfv⟩ hz
      refine ⟨H.symm z, (hP z (hsub hz)).2, ?_, hzpos⟩
      apply (hsheet _ (H.map_target (hP z (hsub hz)).1)).mpr
      rw [H.right_inv (hP z (hsub hz)).1]
  have hpos := positive ell w hw hflat
  have hneg := positive (-ell) (-w)
    (by simp only [neg_apply, map_neg, neg_neg, hw])
    (fun x hx => by simpa only [neg_apply, neg_eq_zero] using hflat x hx)
  exact ⟨hpos, by simpa only [neg_apply, neg_pos] using hneg⟩

end Geometry.OriginalPLTower
