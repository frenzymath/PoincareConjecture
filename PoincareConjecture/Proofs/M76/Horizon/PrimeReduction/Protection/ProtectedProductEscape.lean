import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.ExtendedProductChart
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.SupportedFiberExpansion
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.SupportedChartPLTransition
import PoincareConjecture.Proofs.M76.Mathlib.PositiveSlopeBend







set_option autoImplicit false
noncomputable section
open Set Metric Geometry

namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (-1 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set P2)
local notation "Cube" => (Square ×ˢ I : Set P3)
local notation "Extended" => (Set.prod Square (Icc (-2 : ℝ) 2) : Set P3)
local notation "OpenExtended" => (Set.prod (Set.prod (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1)) (Ioo (-2 : ℝ) 2))

private theorem open_extended_iff (z : P3) :
    z ∈ OpenExtended ↔ ‖z.1‖ < 1 ∧ |z.2| < 2 := by
  change (((-1 < z.1.1 ∧ z.1.1 < 1) ∧ (-1 < z.1.2 ∧ z.1.2 < 1)) ∧
    (-2 < z.2 ∧ z.2 < 2)) ↔ _
  simp only [Prod.norm_def, Real.norm_eq_abs, max_lt_iff, abs_lt]

private theorem open_extended_subset : OpenExtended ⊆ Extended := by
  intro z hz
  exact ⟨⟨⟨hz.1.1.1.le, hz.1.1.2.le⟩, ⟨hz.1.2.1.le, hz.1.2.2.le⟩⟩,
    ⟨hz.2.1.le, hz.2.2.le⟩⟩

theorem exists_original_protected_product_escape
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R D S : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (p : P3 → X) (hp : PolyhedralPLInCharts e p Cube) (hpi : InjOn p Cube)
    (hpimage : p '' Cube = D)
    (hproper : ∀ z ∈ Cube, p z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1)
    (hS : IsCompact S) (hSR : S ⊆ interior R)
    (hcentral : Disjoint S (p '' (Square ×ˢ ({0} : Set ℝ)))) :
    ∃ F : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      F '' R = R ∧ EqOn F id (interior R)ᶜ ∧ Disjoint (F '' S) D := by
  obtain ⟨q, hq, hqi, hqp, hqR, hqproper⟩ :=
    ProtectedProductExtension.exists_extension hR he hDR p hp hpi hpimage hproper
  obtain ⟨Q, hQS, hQT, hQval, hQtrans⟩ :=
    ProtectedProductExtension.exists_compatible_chart he.compatible q hq hqi
  let A := ProtectedProductExtension.extendedCoordinates
  let C : Set P3 := Extended ∩ q ⁻¹' S
  have hEC : IsCompact Extended := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  let : CompactSpace Extended := isCompact_iff_compactSpace.mp hEC
  have hC : IsCompact C := by
    have hc : IsCompact ((fun z : Extended => q z) ⁻¹' S) :=
      (hS.isClosed.preimage hq.continuousOn.domRestrict).isCompact
    have him : Subtype.val '' ((fun z : Extended => q z) ⁻¹' S) = C := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.property, hw⟩
      · rintro ⟨hz, hqz⟩
        exact ⟨⟨z, hz⟩, hqz, rfl⟩
    rw [← him]
    exact hc.image continuous_subtype_val
  have hCr (z : P3) (hz : z ∈ C) : ‖z.1‖ < 1 := by
    have hn : q z ∉ frontier R :=
      (mem_interior_iff_notMem_frontier (interior_subset (hSR hz.2))).mp (hSR hz.2)
    have hnot := mt (hqproper z hz.1).mpr hn
    have h0 := abs_le.mpr hz.1.1.1
    have h1 := abs_le.mpr hz.1.1.2
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff]
    exact ⟨lt_of_le_of_ne h0 (fun h => hnot (Or.inl h)),
      lt_of_le_of_ne h1 (fun h => hnot (Or.inr h))⟩
  have hC0 (z : P3) (hz : z ∈ C) : z.2 ≠ 0 := by
    intro h0
    have hzC : z ∈ Cube := ⟨hz.1.1, by rw [h0]; norm_num⟩
    apply Set.disjoint_left.mp hcentral hz.2
    exact ⟨z, ⟨hz.1.1, h0⟩, (hqp hzC).symm⟩
  obtain ⟨s, v, hs0, hs1, hv0, hv2, H, hH, hHfst, hH0, hHfix, hHmove⟩ :=
    ProtectedFiberExpansion.exists_supported_expansion_of_compact_with_support hC hCr hC0
  let K : Set P3 := closedBall (0 : P2) s ×ˢ Icc (-v) v
  have hK : IsCompact K := (isCompact_closedBall _ _).prod isCompact_Icc
  have hKO : K ⊆ OpenExtended := by
    intro z hz
    apply (open_extended_iff z).mpr
    exact ⟨(mem_closedBall_zero_iff.mp hz.1).trans_lt hs1,
      (abs_le.mpr hz.2).trans_lt hv2⟩
  have hfix : EqOn H id Kᶜ := by
    intro z hz
    apply hHfix
    by_cases hr : s ≤ ‖z.1‖
    · exact Or.inl hr
    · right
      have ht : ¬ |z.2| ≤ v := fun ht => hz ⟨mem_closedBall_zero_iff.mpr (le_of_not_ge hr), abs_le.mp ht⟩
      exact (lt_of_not_ge ht).le
  have hHO : MapsTo H OpenExtended OpenExtended := by
    intro z hz
    by_contra hn
    have hnot : H z ∉ K := fun hk => hn (hKO hk)
    have heq : H z = z := H.injective (hfix hnot)
    exact hn (heq.symm ▸ hz)
  let K3 : Set V3 := A.symm '' K
  have hK3 : IsCompact K3 := hK.image A.symm.continuous
  have hKQ : K3 ⊆ Q.target := by
    rintro z ⟨w, hw, rfl⟩
    rw [hQT]
    change A (A.symm w) ∈ OpenExtended
    rw [A.apply_symm_apply]
    exact hKO hw
  let H3 : V3 ≃ₜ V3 := (A.toHomeomorph.trans H).trans A.symm.toHomeomorph
  have hH3val (z : V3) : H3 z = A.symm (H (A z)) := rfl
  have hH3fix : EqOn H3 id K3ᶜ := by
    intro z hz
    have hnot : A z ∉ K := fun h => hz ⟨A z, h, A.symm_apply_apply z⟩
    rw [hH3val, hfix hnot]
    exact A.symm_apply_apply z
  have hH3 : H3.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid V3 := by
    have hforward := (mem_piecewiseAffineGroupoid_iff_forward H.toOpenPartialHomeomorph).mp hH
    change LocallyPiecewiseAffineOn H univ at hforward
    have ha := locallyPiecewiseAffineOn_affine A.toContinuousAffineMap isOpen_univ
    have hai := locallyPiecewiseAffineOn_affine A.symm.toContinuousAffineMap isOpen_univ
    have hall := hai.comp (hforward.comp ha)
    simp only [preimage_univ, inter_univ] at hall
    apply (mem_piecewiseAffineGroupoid_iff_forward H3.toOpenPartialHomeomorph).mpr
    exact hall
  obtain ⟨F, hFQ, hFout⟩ := Q.symm.exists_supported_chart_homeomorph H3 hK3 hKQ hH3fix
  have hforward (i j : α) : (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3 :=
    Q.symm.supported_chart_transition_mem_piecewiseAffineGroupoid (e i).symm (e j).symm
      H3 F hK3 hKQ hH3fix hFQ hFout hH3 (hQtrans i) (hQtrans j) (he.compatible i j)
  have hQK : Q.symm '' K3 ⊆ interior R := by
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hQval]
    change q (A (A.symm w)) ∈ interior R
    rw [A.apply_symm_apply]
    have hwE := open_extended_subset (hKO hw)
    apply (mem_interior_iff_notMem_frontier (hqR hwE)).mpr
    rw [hqproper w hwE]
    have hr := (open_extended_iff w).mp (hKO hw)
    intro h
    rcases h with h | h
    · have hh := norm_fst_le w.1
      rw [Real.norm_eq_abs, h] at hh
      linarith
    · have hh := norm_snd_le w.1
      rw [Real.norm_eq_abs, h] at hh
      linarith
  have hFfix : EqOn F id (interior R)ᶜ := fun x hx => hFout (fun hk => hx (hQK hk))
  have hFR : F '' R = R := by
    have hfixR : EqOn F id Rᶜ := fun x hx => hFfix (fun hi => hx (interior_subset hi))
    rw [← compl_inj_iff, ← image_compl_eq F.bijective, hfixR.image_eq_self]
  refine ⟨F, hforward, ?_, hFR, hFfix, ?_⟩
  · intro i j
    simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc,
      Homeomorph.symm_toOpenPartialHomeomorph] using
      (piecewiseAffineGroupoid V3).symm (hforward j i)
  · apply Set.disjoint_left.mpr
    rintro x ⟨y, hyS, rfl⟩ hFyD
    have hDyQ (y : X) (hyD : y ∈ D) (hyR : y ∈ interior R) : y ∈ Q.source := by
      obtain ⟨z, hz, rfl⟩ := hpimage.symm.subset hyD
      have hnot := (mem_interior_iff_notMem_frontier (hDR (hpimage.subset ⟨z, hz, rfl⟩))).mp hyR
      have hr : ‖z.1‖ < 1 := by
        rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_lt_iff]
        exact ⟨lt_of_le_of_ne (abs_le.mpr hz.1.1)
          (fun h => hnot ((hproper z hz).mpr (Or.inl h))),
          lt_of_le_of_ne (abs_le.mpr hz.1.2)
            (fun h => hnot ((hproper z hz).mpr (Or.inr h)))⟩
      have hzO : z ∈ OpenExtended := (open_extended_iff z).mpr
        ⟨hr, (abs_le.mpr hz.2).trans_lt (by norm_num)⟩
      have haQ : A.symm z ∈ Q.target := by
        rw [hQT]
        change A (A.symm z) ∈ OpenExtended
        simpa only [A.apply_symm_apply] using hzO
      have hqz := Q.map_target haQ
      rw [hQval] at hqz
      change q (A (A.symm z)) ∈ Q.source at hqz
      rw [A.apply_symm_apply, hqp hz] at hqz
      exact hqz
    have hyQ : y ∈ Q.source := by
      by_contra hn
      have hyout : y ∉ Q.symm '' K3 := fun ⟨z, hz, heq⟩ => hn
        (heq ▸ Q.map_target (hKQ hz))
      have hf : F y = y := hFout hyout
      exact hn (hDyQ y (hf ▸ hFyD) (hSR hyS))
    let z : P3 := A (Q y)
    have hzO : z ∈ OpenExtended := by
      have ht := Q.map_source hyQ
      rw [hQT] at ht
      exact ht
    have hqz : q z = y := by
      exact (hQval (Q y)).symm.trans (Q.left_inv hyQ)
    have hzC : z ∈ C := ⟨open_extended_subset hzO, by change q z ∈ S; rw [hqz]; exact hyS⟩
    have hFyz : F y = q (H z) := by
      have hh := hFQ hyQ
      change F y = Q.symm (H3 (Q y)) at hh
      rw [hQval, hH3val] at hh
      change F y = q (A (A.symm (H z))) at hh
      simpa only [A.apply_symm_apply] using hh
    obtain ⟨w, hw, hwFy⟩ := hpimage.symm.subset hFyD
    have heq : H z = w := hqi (open_extended_subset (hHO hzO))
      ⟨hw.1, by constructor <;> linarith [hw.2.1, hw.2.2]⟩
      (hFyz.symm.trans (hwFy.symm.trans (hqp hw).symm))
    have hgt := hHmove z hzC
    rw [heq] at hgt
    linarith [abs_le.mpr hw.2]

theorem exists_original_protected_product_escape_at_height
    {X α : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R D S : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (p : P3 → X) (hp : PolyhedralPLInCharts e p Cube) (hpi : InjOn p Cube)
    (hpimage : p '' Cube = D)
    (hproper : ∀ z ∈ Cube, p z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1)
    (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 1)
    (hS : IsCompact S) (hSR : S ⊆ interior R)
    (hsection : Disjoint S (p '' (Square ×ˢ ({t} : Set ℝ)))) :
    ∃ F : X ≃ₜ X,
      (∀ i j, (e i).symm.trans (F.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      (∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
        piecewiseAffineGroupoid V3) ∧
      F '' R = R ∧ EqOn F id (interior R)ᶜ ∧ Disjoint (F '' S) D := by
  let f : ℝ → ℝ := fun u => t + PLStrip.bend (1 + t) (1 - t) u
  have hfc : Continuous f := continuous_const.add (PLStrip.continuous_bend _ _)
  have hmono : StrictMono f :=
    (PLStrip.strictMono_bend (by linarith [ht.1]) (by linarith [ht.2])).const_add t
  have hflo : f (-1) = -1 := by
    dsimp [f]
    rw [PLStrip.bend_of_nonpos _ _ (by norm_num)]
    ring
  have hfhi : f 1 = 1 := by
    dsimp [f]
    rw [PLStrip.bend_of_nonneg _ _ (by norm_num)]
    ring
  have hf0 : f 0 = t := by simp [f, PLStrip.bend]
  have hfimage : f '' I = I := by
    rw [hfc.image_Icc_of_strictMono hmono, hflo, hfhi]
  let a : P3 → P3 := fun z => (z.1, f z.2)
  have haimage : a '' Cube = Cube := by
    change (Prod.map (id : P2 → P2) f) '' Cube = Cube
    rw [prodMap_image_prod, image_id, hfimage]
  have ha : MapsTo a Cube Cube := fun z hz => haimage.subset ⟨z, hz, rfl⟩
  have hai : Function.Injective a := by
    intro z w h
    have hf := congrArg Prod.fst h
    have hs := congrArg Prod.snd h
    change z.1 = w.1 at hf
    change f z.2 = f w.2 at hs
    exact Prod.ext hf (hmono.injective hs)
  obtain ⟨K, _, hK, hKs, _, _⟩ :=
    (((isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)).prod
      (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))).prod
        (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num))).exists_finite_carrier_and_rim_complexes
  have hPL : FinitePiecewiseAffineOn a K.space := by
    have hfst := (K.affineOnFaces_affine
      (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
    have hsnd := (K.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ P2 ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
    have hz := (K.affineOnFaces_affine
      (ContinuousAffineMap.const ℝ P3 (0 : ℝ))).finitePiecewiseAffineOn hK
    have hl := ((hsnd.min hz).postcomp ((1 + t) • ContinuousAffineMap.id ℝ ℝ))
    have hr := ((hsnd.max hz).postcomp ((1 - t) • ContinuousAffineMap.id ℝ ℝ))
    have ht' := (K.affineOnFaces_affine
      (ContinuousAffineMap.const ℝ P3 t)).finitePiecewiseAffineOn hK
    exact hfst.prod_mk ((ht'.add (hl.add hr)).congr (fun _ _ => rfl))
  have hpa : PolyhedralPLInCharts e (p ∘ a) Cube := by
    rw [← hKs]
    exact hp.comp_finitePiecewiseAffineOn K hK hPL (fun z hz => ha (hKs.subset hz))
  have himage : (p ∘ a) '' Cube = D := by rw [image_comp, haimage, hpimage]
  have hmark (z : P3) (hz : z ∈ Cube) :
      (p ∘ a) z ∈ frontier R ↔ |z.1.1| = 1 ∨ |z.1.2| = 1 := hproper (a z) (ha hz)
  have hzero : a '' (Square ×ˢ ({0} : Set ℝ)) = Square ×ˢ ({t} : Set ℝ) := by
    ext z
    constructor
    · rintro ⟨w, ⟨hw, hw0⟩, rfl⟩
      refine ⟨hw, ?_⟩
      change f w.2 = t
      rw [show w.2 = 0 from hw0, hf0]
    · rintro ⟨hz, hzt⟩
      refine ⟨(z.1, 0), ⟨hz, rfl⟩, ?_⟩
      change (z.1, f 0) = z
      apply Prod.ext
      · rfl
      · rw [hf0]
        exact hzt.symm
  apply exists_original_protected_product_escape hR he hDR (p ∘ a) hpa
    (hpi.comp hai.injOn ha) himage hmark hS hSR
  rw [image_comp, hzero]
  exact hsection

end PoincareConjecture.M76
