import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.StandardOrientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.NestedOrientation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

private theorem embedding_of_left_inverse_coe
    (C : S1 → E2) (hC : ContMDiff (𝓡 1) (𝓡 2) ∞ C)
    (L : E2 → E2) (hL : ContDiff Real ∞ L)
    (hLC : ∀ q, L (C q) = (q : E2)) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ C := by
  apply isSmoothEmbedding_of_injective_mfderiv hC
  · intro q r hqr
    apply Subtype.ext
    rw [← hLC q, ← hLC r, hqr]
  · intro q
    have heq : L ∘ C = ((↑) : S1 → E2) := funext hLC
    have hd : Injective (mfderiv (𝓡 1) (𝓡 2) ((↑) : S1 → E2) q) := by
      convert! injective_mvfderiv_subtypeVal_sphere (n := 1) q
    rw [← heq, mfderiv_comp q ((hL.contMDiff _).mdifferentiableAt (by simp))
      ((hC q).mdifferentiableAt (by simp))] at hd
    intro u v huv
    apply hd
    exact congrArg (mfderiv (𝓡 2) (𝓡 2) L (C q)) huv

private theorem joint_injective_of_disjoint
    (C : Fin 2 → S1 → E2) (hi : ∀ i, Injective (C i))
    (hd : Disjoint (range (C 0)) (range (C 1))) :
    Injective (fun x : Fin 2 × S1 => C x.1 x.2) := by
  rintro ⟨i, q⟩ ⟨j, r⟩ heq
  have hij : i = j := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (disjoint_left.mp hd (mem_range_self q) ⟨r, heq.symm⟩)
    · exact False.elim (disjoint_left.mp hd ⟨r, heq.symm⟩ (mem_range_self q))
    · rfl
  subst j
  exact Prod.ext rfl (hi i heq)

private theorem small_radius_mem_lowerDomain {r : Real} (hr : r < 1 / 2)
    {q : E2} (hq : ‖q‖ = r) : q ∈ Saddle.lowerDomain := by
  have hr0 : 0 ≤ r := hq ▸ norm_nonneg q
  have hn : (q 0) ^ 2 + (q 1) ^ 2 = r ^ 2 := by
    rw [← Saddle.norm_sq_two, hq]
  have hy : -r ≤ q 1 := by nlinarith [sq_nonneg (q 0)]
  change (q 0) ^ 2 + (q 1 - 1 / 2) ^ 2 < 1
  nlinarith

private theorem standard_lower_circle_pair
    (T : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (c scale : Real) (hscale : 0 < scale)
    (hT : ∀ y, T y 2 = c + scale * (y 2 + 1))
    {s : Real} (hs : 0 < s) (hsu : s < 1 / 4) :
    ∃ C : Fin 2 → S1 → E2,
      (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
      Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
      (⋃ i, range (C i)) =
        {x : E2 | Saddle.toE3 x (c - scale * s) ∈
          (Saddle.shear.trans T) '' sphere (0 : E3) 1} := by
  let r := Real.sqrt (1 / 4 - s)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hrsq : r ^ 2 = 1 / 4 - s := Real.sq_sqrt (by linarith)
  have hru : r < 1 / 2 := by nlinarith
  let σ : Fin 2 → Real := ![1, -1]
  have hσ (i : Fin 2) : σ i ^ 2 = 1 := by fin_cases i <;> norm_num [σ]
  let v (q : S1) : E2 := r • (q : E2)
  have hv (q : S1) : ‖v q‖ = r := by
    simp [v, norm_smul, abs_of_pos hr, norm_eq_of_mem_sphere q]
  have hvdom (q : S1) : v q ∈ Saddle.lowerDomain :=
    small_radius_mem_lowerDomain hru (hv q)
  let k (i : Fin 2) (q : S1) := T (Saddle.lowerCap (σ i) (v q))
  let C (i : Fin 2) : S1 → E2 := Saddle.toE2 ∘ k i
  have hkheight (i : Fin 2) (q : S1) : k i q 2 = c - scale * s := by
    dsimp [k]
    rw [hT, Saddle.lowerCap_height, hv, hrsq]
    ring
  have hlift (i : Fin 2) (q : S1) :
      Saddle.toE3 (C i q) (c - scale * s) = k i q := by
    ext j
    fin_cases j
    · rfl
    · rfl
    · exact (hkheight i q).symm
  have hvsm : ContMDiff (𝓡 1) (𝓡 2) ∞ v :=
    (contMDiff_const : ContMDiff (𝓡 1) 𝓘(Real, Real) ∞ (fun _ : S1 => r)).smul
      (contMDiff_coe_sphere (n := 1))
  have hksm (i : Fin 2) : ContMDiff (𝓡 1) (𝓡 3) ∞ (k i) := by
    apply T.contMDiff.comp
    intro q
    exact ((Saddle.lowerCap_contDiffOn (σ i) _ (hvdom q)).contDiffAt
      (Saddle.isOpen_lowerDomain.mem_nhds (hvdom q))).comp_contMDiffAt (hvsm q)
  have hproj : ContDiff Real ∞ Saddle.toE2 := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 3)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 3)).contDiff
  have hliftsm : ContDiff Real ∞ (fun x => Saddle.toE3 x (c - scale * s)) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := Real) (0 : Fin 2)).contDiff
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff
    · exact contDiff_const
  let L (x : E2) := r⁻¹ • Saddle.lowerCoordinates (T.symm (Saddle.toE3 x (c - scale * s)))
  have hL : ContDiff Real ∞ L :=
    (contDiff_const : ContDiff Real ∞ (fun _ : E2 => r⁻¹)).smul
    (Saddle.lowerCoordinates_contDiff.comp (T.symm.contMDiff.contDiff.comp hliftsm))
  have hLC (i : Fin 2) (q : S1) : L (C i q) = (q : E2) := by
    dsimp [L]
    rw [hlift]
    change r⁻¹ • Saddle.lowerCoordinates (T.symm (T _)) = _
    rw [T.symm_apply_apply, Saddle.lowerCoordinates_lowerCap (hσ i) (hvdom q)]
    simp [v, smul_smul, hr.ne']
  have hC (i : Fin 2) : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i) :=
    embedding_of_left_inverse_coe (C i) (hproj.contMDiff.comp (hksm i)) L hL (hLC i)
  have hdis : Disjoint (range (C 0)) (range (C 1)) := by
    apply disjoint_left.mpr
    rintro x ⟨q, rfl⟩ ⟨u, hu⟩
    have heq : k 1 u = k 0 q := by rw [← hlift, ← hlift, hu]
    have hc := congrArg (fun y : E3 => y 0) (T.injective heq)
    have hp (z : S1) : 0 < Real.sqrt (1 - (v z 0) ^ 2 - (v z 1 - 1 / 2) ^ 2) := by
      apply Real.sqrt_pos.2
      have := hvdom z
      change (v z 0) ^ 2 + (v z 1 - 1 / 2) ^ 2 < 1 at this
      linarith
    change -1 * Real.sqrt _ = 1 * Real.sqrt _ at hc
    linarith [hp q, hp u]
  refine ⟨C, hC, joint_injective_of_disjoint C (fun i => (hC i).isEmbedding.injective) hdis, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, q, rfl⟩ := by simpa only [mem_iUnion, mem_range] using hx
    have hm : Saddle.lowerCap (σ i) (v q) ∈ Saddle.shear '' sphere (0 : E3) 1 := by
      rw [Saddle.shear_image_sphere]
      exact Saddle.lowerCap_mem_surface (hσ i) (hvdom q)
    obtain ⟨y, hy, heq⟩ := hm
    refine ⟨y, hy, ?_⟩
    change T (Saddle.shear y) = _
    rw [heq]
    exact (hlift i q).symm
  · rintro ⟨y, hy, heq⟩
    let p := Saddle.shear y
    have hpoly : Saddle.polynomial p = 1 := by
      have hm : p ∈ Saddle.shear '' sphere (0 : E3) 1 := ⟨y, hy, rfl⟩
      rwa [Saddle.shear_image_sphere] at hm
    have hpheight : p 2 = -1 - s := by
      have hh := congrArg (fun z : E3 => z 2) heq
      change T p 2 = c - scale * s at hh
      rw [hT] at hh
      nlinarith
    let u := Saddle.lowerCoordinates p
    have hu : ‖u‖ = r := by
      have hn := Saddle.lowerCoordinates_norm_sq hpoly
      rw [hpheight] at hn
      change ‖u‖ ^ 2 = _ at hn
      nlinarith [norm_nonneg u]
    have hudom : u ∈ Saddle.lowerDomain := small_radius_mem_lowerDomain hru hu
    have hvq : ‖r⁻¹ • u‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hu, inv_mul_cancel₀ hr.ne']
    let q : S1 := ⟨r⁻¹ • u, mem_sphere_zero_iff_norm.mpr hvq⟩
    have hvu : v q = u := by simp [v, q, smul_smul, hr.ne']
    have hrad : 1 - (u 0) ^ 2 - (u 1 - 1 / 2) ^ 2 = (p 0) ^ 2 := by
      change 1 - (p 1) ^ 2 - (p 2 + (p 0) ^ 2 + 1 / 2 - 1 / 2) ^ 2 = _
      unfold Saddle.polynomial at hpoly
      nlinarith
    have hcap (i : Fin 2) (hi : σ i * |p 0| = p 0) : Saddle.lowerCap (σ i) (v q) = p := by
      rw [hvu]
      ext j
      fin_cases j
      · change σ i * Real.sqrt _ = p 0
        rw [hrad, Real.sqrt_sq_eq_abs, hi]
      · rfl
      · change Saddle.lowerCap (σ i) u 2 = p 2
        rw [Saddle.lowerCap_height, hu, hrsq, hpheight]
        ring
    have hmem (i : Fin 2) (hi : σ i * |p 0| = p 0) : x ∈ range (C i) := by
      refine ⟨q, ?_⟩
      change Saddle.toE2 (T (Saddle.lowerCap (σ i) (v q))) = x
      rw [hcap i hi]
      change Saddle.toE2 (T (Saddle.shear y)) = x
      change T (Saddle.shear y) = Saddle.toE3 x (c - scale * s) at heq
      rw [heq]
      ext j
      fin_cases j <;> rfl
    by_cases hp : 0 ≤ p 0
    · exact mem_iUnion.mpr ⟨0, hmem 0 (by simp [σ, abs_of_nonneg hp])⟩
    · exact mem_iUnion.mpr ⟨1, hmem 1 (by simp [σ, abs_of_neg (lt_of_not_ge hp)])⟩

private def shiftHeight (c : Real) : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ where
  toFun y := y - c • (EuclideanSpace.single 2 1 : E3)
  invFun y := y + c • (EuclideanSpace.single 2 1 : E3)
  left_inv y := by simp
  right_inv y := by simp
  contMDiff_toFun := (contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_model_lower_slice_circle_pair
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Ico (-ε) (0 : Real),
      ∃ C : Fin 2 → S1 → E2,
        (∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (C i)) ∧
        Injective (fun x : Fin 2 × S1 => C x.1 x.2) ∧
        (⋃ i, range (C i)) = d.B (inner Real (M.v : E3) (g p) + t) := by
  let c := inner Real (M.v : E3) (g p)
  rcases d.model_kind with hmodel | hmodel
  · let T := d.transport.trans d.flatten
    have hcenter := terminal_standard_model_chart_center d hmodel hform
    have hheight : d.model (d.modelChart 0) 2 = -1 := by
      rw [hmodel, hcenter]
      exact Saddle.height_saddlePoint
    have hT (y : E3) : T y 2 = c + d.scale * (y 2 + 1) := by
      change d.frame (d.D (d.transport y)) 2 = _
      rw [d.frame_height, d.D_height, d.transport_height, hheight]
      simp only [sub_neg_eq_add]
      rfl
    refine ⟨d.scale / 8, div_pos d.scale_pos (by norm_num), ?_⟩
    intro t ht
    let s := -t / d.scale
    have hs : 0 < s := div_pos (neg_pos.mpr ht.2) d.scale_pos
    have hsu : s < 1 / 4 := (div_lt_iff₀ d.scale_pos).mpr (by linarith [ht.1, d.scale_pos])
    have hst : c - d.scale * s = c + t := by
      dsimp [s]
      field_simp [d.scale_pos.ne']; ring
    obtain ⟨C, hC, hi, hcover⟩ := standard_lower_circle_pair T c d.scale d.scale_pos hT hs hsu
    rw [hst] at hcover
    refine ⟨C, hC, hi, hcover.trans ?_⟩
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      refine ⟨d.transport (d.model y), ⟨y, hy, rfl⟩, ?_⟩
      change d.flatten (d.transport (d.model y)) = Saddle.toE3 x (c + t)
      rw [hmodel]
      exact heq
    · rintro ⟨_, ⟨y, hy, rfl⟩, heq⟩
      refine ⟨y, hy, ?_⟩
      change d.flatten (d.transport (d.model y)) = Saddle.toE3 x (c + t) at heq
      rw [hmodel] at heq
      exact heq
  · let S := shiftHeight c
    let T := (d.transport.trans d.flatten).trans S
    have hc := terminal_model_chart_critical d hform
    rw [hmodel] at hc
    have hTheight (y : E3) : T y 2 =
        d.scale * (y 2 - Saddle.Nested.height (d.modelChart 0)) := by
      change (d.frame (d.D (d.transport y)) - c • (EuclideanSpace.single 2 1 : E3)) 2 = _
      simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul,
        mul_one]
      rw [d.frame_height, d.D_height, d.transport_height, hmodel]
      change c + d.scale * (y 2 - Saddle.Nested.height (d.modelChart 0)) - c = _
      ring
    obtain ⟨ε, hε, hcircles⟩ := Saddle.Nested.exists_uniform_negative_nested_level_circles
      T (Diffeomorph.refl (𝓡 3) E3 (n := ∞)) (fun _ => rfl) hc
      (terminal_nested_model_chart_latitude d hmodel hform) d.scale_pos hTheight
    refine ⟨ε, hε, ?_⟩
    intro t ht
    obtain ⟨C, hC, _, hdis, hcover, _⟩ := hcircles t ht
    have hS (x : E2) : S (Saddle.toE3 x (c + t)) = Saddle.toE3 x t := by
      change Saddle.toE3 x (c + t) - c • EuclideanSpace.single 2 1 = _
      ext i
      fin_cases i <;> simp [Saddle.toE3]
    refine ⟨C, hC, joint_injective_of_disjoint C (fun i => (hC i).isEmbedding.injective)
      hdis, hcover.trans ?_⟩
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      refine ⟨d.transport (d.model y), ⟨y, hy, rfl⟩, ?_⟩
      apply S.injective
      change S (d.flatten (d.transport (d.model y))) = S (Saddle.toE3 x (c + t))
      rw [hS, hmodel]
      exact heq
    · rintro ⟨_, ⟨y, hy, rfl⟩, heq⟩
      change d.flatten (d.transport (d.model y)) = Saddle.toE3 x (c + t) at heq
      refine ⟨y, hy, ?_⟩
      change S (d.flatten (d.transport (Saddle.Nested.shear (3 / 10) y))) = _
      rw [← hmodel, heq, hS]

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
