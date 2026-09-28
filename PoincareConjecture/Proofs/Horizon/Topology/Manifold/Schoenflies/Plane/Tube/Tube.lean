import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Tube.AnnularRegularity
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

set_option autoImplicit false

open Set Metric Function Filter
open scoped Topology Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

theorem exists_openPartialHomeomorph_of_injective_localInverses
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (U : Set E) (hU : IsOpen U) (hc : ContinuousOn f U)
    (hi : InjOn f U)
    (hl : ∀ x ∈ U, ∃ l : OpenPartialHomeomorph E F, x ∈ l.source ∧
      (∀ y : E, l y = f y) ∧ ContDiffAt ℝ ∞ l.symm (f x)) :
    ∃ e : OpenPartialHomeomorph E F, e.source = U ∧
      (∀ x : E, e x = f x) ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hopen : ∀ V : Set E, IsOpen V → V ⊆ U → IsOpen (f '' V) := by
    intro V hV hVU
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨l, hxl, hlf, _⟩ := hl x (hVU hx)
    have hf : (l : E → F) = f := funext hlf
    have hn : l '' (l.source ∩ V) ∈ 𝓝 (f x) := by
      rw [← hlf x]
      exact (l.isOpen_image_source_inter hV).mem_nhds ⟨x, ⟨hxl, hx⟩, rfl⟩
    exact mem_of_superset hn (by
      rw [hf]
      exact image_mono inter_subset_right)
  have hrestrict : IsOpenMap (U.domRestrict f) := by
    intro V hV
    have hval : IsOpen ((Subtype.val : U → E) '' V) := hU.isOpenMap_subtype_val V hV
    have hsub : (Subtype.val : U → E) '' V ⊆ U := by
      rintro x ⟨y, _, rfl⟩
      exact y.property
    have h := hopen ((Subtype.val : U → E) '' V) hval hsub
    change IsOpen ((f ∘ (Subtype.val : U → E)) '' V)
    rw [image_image] at h
    exact h
  let e : OpenPartialHomeomorph E F :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f U) hc hrestrict hU
  have he : ∀ x : E, e x = f x := fun _ => rfl
  have hsource : e.source = U := rfl
  refine ⟨e, hsource, he, ?_⟩
  intro y hy
  have hx : e.symm y ∈ U := hsource ▸ e.map_target hy
  obtain ⟨l, hxl, hlf, hlsmooth⟩ := hl (e.symm y) hx
  have hfy : f (e.symm y) = y := (he _).symm.trans (e.right_inv hy)
  rw [hfy] at hlsmooth
  have hn : ∀ᶠ y' in 𝓝 y, e.symm y' ∈ l.source :=
    (e.continuousAt_symm hy) (l.open_source.mem_nhds hxl)
  have hEq : (e.symm : F → E) =ᶠ[𝓝 y] (l.symm : F → E) := by
    filter_upwards [hn, e.open_target.mem_nhds hy] with y' hyl hye
    calc
      e.symm y' = l.symm (l (e.symm y')) := (l.left_inv hyl).symm
      _ = l.symm y' := by rw [hlf, ← he, e.right_inv hye]
  exact (hlsmooth.congr_of_eventuallyEq hEq).contDiffWithinAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fact (Module.finrank ℝ E = 2)]
variable (o : Orientation ℝ E (Fin 2)) (q0 : sphere (0 : E) 1)
variable (c : ℝ → sphere (0 : E) 1 → E)
variable (hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E) ∞
  (fun p : ℝ × sphere (0 : E) 1 => c p.1 p.2))
variable {a b : ℝ} (hab : a ≤ b)
variable (hi : ∀ z ∈ Icc a b, Injective (c z))
variable (hm : ∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
  Injective (mfderiv (𝓡 1) 𝓘(ℝ, E) (c z) q))

include hc hab hi hm

theorem exists_uniform_curveAnnularNeighborhood :
    ∃ m : ℝ, 0 < m ∧ ∃ w : ℝ, 0 < w ∧ w < 1 ∧
      InjOn (fun p : ℝ × E => (p.1, curveAnnularExtension o q0 c p))
        (Ioo (a - m) (b + m) ×ˢ {x : E | |‖x‖ - 1| < w}) ∧
      (∀ p ∈ Ioo (a - m) (b + m) ×ˢ {x : E | |‖x‖ - 1| < w},
        p.2 ≠ 0 ∧ ContDiffAt ℝ ∞ (curveAnnularExtension o q0 c) p ∧
          Injective (fderiv ℝ (fun x => curveAnnularExtension o q0 c (p.1, x)) p.2)) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  let A := curveAnnularExtension o q0 c
  let T : ℝ × E → ℝ × E := fun p => (p.1, A p)
  let K : Set (ℝ × E) := Icc a b ×ˢ sphere (0 : E) 1
  have hv : ∀ z ∈ Icc a b, ∀ q : sphere (0 : E) 1,
      curveFamilyVelocity o (radialFamilyExtension q0 c) (z, (q : E)) ≠ 0 :=
    fun z hz q => curveFamilyVelocity_radial_ne_zero o q0 c hc z q (hm z hz q)
  have hinj : InjOn T K := by
    rintro ⟨z, x⟩ hx ⟨z', y⟩ hy h
    have hz : z = z' := congrArg Prod.fst h
    subst z'
    have hxy : c z ⟨x, hx.2⟩ = c z ⟨y, hy.2⟩ :=
      (curveAnnularExtension_apply_sphere o q0 c z ⟨x, hx.2⟩).symm.trans
        ((congrArg Prod.snd h).trans (curveAnnularExtension_apply_sphere o q0 c z ⟨y, hy.2⟩))
    exact Prod.ext rfl (congrArg Subtype.val (hi z hx.1 hxy))
  have hcont : ∀ p ∈ K, ContinuousAt T p := by
    intro p hp
    have hA := contDiffAt_curveAnnularExtension o q0 c hc p.1 ⟨p.2, hp.2⟩
      (hv p.1 hp.1 ⟨p.2, hp.2⟩)
    exact (contDiffAt_fst.prodMk hA).continuousAt
  have hlocal : ∀ p ∈ K, ∃ W ∈ 𝓝 p, InjOn T W := by
    intro p hp
    obtain ⟨e, he, hf, _⟩ := exists_curveAnnularTrack_localInverse o q0 c hc p.1
      ⟨p.2, hp.2⟩ (hv p.1 hp.1 ⟨p.2, hp.2⟩)
    have hfun : (e : ℝ × E → ℝ × E) = T := funext hf
    refine ⟨e.source, e.open_source.mem_nhds he, ?_⟩
    rw [← hfun]
    exact e.injOn
  obtain ⟨W, hW, hKW, hinjW⟩ :=
    hinj.exists_isOpen_superset (isCompact_Icc.prod (isCompact_sphere 0 1)) hcont hlocal
  obtain ⟨U, hU, hcentral, hregular⟩ :=
    exists_open_curveAnnularRegularNeighborhood o q0 c hc
  have hKU : K ⊆ U := fun p hp =>
    hcentral p.1 ⟨p.2, hp.2⟩ (hv p.1 hp.1 ⟨p.2, hp.2⟩)
  let Phi : (ℝ × sphere (0 : E) 1) × ℝ → ℝ × E :=
    fun p => (p.1.1, (1 + p.2) • (p.1.2 : E))
  have hPhi : Continuous Phi :=
    continuous_fst.fst.prodMk ((continuous_const.add continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst.snd))
  have hzero : (Icc a b ×ˢ (univ : Set (sphere (0 : E) 1))) ×ˢ ({0} : Set ℝ) ⊆
      Phi ⁻¹' (W ∩ U) := by
    rintro ⟨⟨z, q⟩, r⟩ ⟨⟨hz, _⟩, hr⟩
    have hr0 : r = 0 := hr
    subst r
    have hq : (z, (q : E)) ∈ W ∩ U := ⟨hKW ⟨hz, q.property⟩, hKU ⟨hz, q.property⟩⟩
    simpa only [mem_preimage, Phi, add_zero, one_smul] using hq
  obtain ⟨m, hm0, w0, hw0, hbox⟩ :=
    exists_uniform_zero_section_tube hab ((hW.inter hU).preimage hPhi) hzero
  let w := min w0 (1 / 2 : ℝ)
  have hw : 0 < w := lt_min hw0 (by norm_num)
  have hw1 : w < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hww0 : w ≤ w0 := min_le_left _ _
  have hsubset : Ioo (a - m) (b + m) ×ˢ {x : E | |‖x‖ - 1| < w} ⊆ W ∩ U := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    change |‖x‖ - 1| < w at hx
    have hb := abs_lt.mp hx
    have hnorm : 0 < ‖x‖ := by linarith [hb.1]
    have hx0 : x ≠ 0 := norm_pos_iff.mp hnorm
    let q := unitRadialProjection q0 x
    let r := ‖x‖ - 1
    have hr : r ∈ Ioo (-w0) w0 := ⟨by dsimp [r]; linarith [hb.1],
      by dsimp [r]; linarith [hb.2]⟩
    have hrecover : Phi ((z, q), r) = (z, x) := by
      apply Prod.ext
      · rfl
      · change (1 + (‖x‖ - 1)) • (unitRadialProjection q0 x : E) = x
        rw [unitRadialProjection_coe_of_ne_zero q0 hx0, smul_smul,
          show 1 + (‖x‖ - 1) = ‖x‖ by ring, mul_inv_cancel₀ (ne_of_gt hnorm), one_smul]
    have hmem : Phi ((z, q), r) ∈ W ∩ U := hbox ⟨⟨hz, mem_univ q⟩, hr⟩
    exact hrecover ▸ hmem
  exact ⟨m, hm0, w, hw, hw1, hinjW.mono (hsubset.trans inter_subset_left),
    fun p hp => hregular p (hsubset hp).2⟩

theorem exists_curveAnnularTube :
    ∃ m : ℝ, 0 < m ∧ ∃ w : ℝ, 0 < w ∧ w < 1 ∧
      ∃ e : OpenPartialHomeomorph (ℝ × E) (ℝ × E),
        e.source = Ioo (a - m) (b + m) ×ˢ {x : E | |‖x‖ - 1| < w} ∧
        (∀ p : ℝ × E, e p = (p.1, curveAnnularExtension o q0 c p)) ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by
    rw [show Module.finrank ℝ E = 2 from Fact.out]
    norm_num)
  obtain ⟨m, hm0, w, hw, hw1, hinj, hregular⟩ :=
    exists_uniform_curveAnnularNeighborhood o q0 c hc hab hi hm
  let B := Ioo (a - m) (b + m) ×ˢ {x : E | |‖x‖ - 1| < w}
  let T : ℝ × E → ℝ × E := fun p => (p.1, curveAnnularExtension o q0 c p)
  have hB : IsOpen B := isOpen_Ioo.prod
    (isOpen_lt ((continuous_norm.sub continuous_const).abs) continuous_const)
  have hT : ∀ p ∈ B, ContDiffAt ℝ ∞ T p := fun p hp =>
    contDiffAt_fst.prodMk (hregular p hp).2.1
  have hlocal : ∀ p ∈ B, ∃ l : OpenPartialHomeomorph (ℝ × E) (ℝ × E),
      p ∈ l.source ∧ (∀ y : ℝ × E, l y = T y) ∧ ContDiffAt ℝ ∞ l.symm (T p) := by
    intro p hp
    exact exists_smoothTrack_localInverse (curveAnnularExtension o q0 c) p
      (hregular p hp).2.1 (hregular p hp).2.2
  obtain ⟨e, hsource, he, hinverse⟩ :=
    exists_openPartialHomeomorph_of_injective_localInverses T B hB
      (fun p hp => (hT p hp).continuousAt.continuousWithinAt) hinj hlocal
  refine ⟨m, hm0, w, hw, hw1, e, hsource, he, ?_, hinverse⟩
  have heq : (e : ℝ × E → ℝ × E) = T := funext he
  rw [heq, hsource]
  exact fun p hp => (hT p hp).contDiffWithinAt

end Poincare.Manifold.Schoenflies.Plane
