import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneCrossingArc
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneRetraction
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => (ℝ × V2)
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-1 : ℝ) 1

private noncomputable def edge (vertical : Bool) (c : ℝ) : ℝ →ᴬ[ℝ] V2 :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.toContinuousAffineEquiv.toContinuousAffineMap.comp
    (if vertical then (ContinuousAffineMap.const ℝ ℝ c).prod (ContinuousAffineMap.id ℝ ℝ)
     else (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ c))

private theorem edge_injective (vertical : Bool) (c : ℝ) :
    Function.Injective (edge vertical c) := by
  intro s t h
  cases vertical
  · exact congrFun h 0
  · exact congrFun h 1

private theorem square_bounds (x : Q) (i : Fin 2) : (x : V2) i ∈ J := by
  have h := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp
    (mem_sphere_zero_iff_norm.mp x.property).le i
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using h)

private theorem square_has_edge (x : Q) :
    (x : V2) 0 = -1 ∨ (x : V2) 0 = 1 ∨ (x : V2) 1 = -1 ∨ (x : V2) 1 = 1 := by
  by_contra hx
  push Not at hx
  have hsmall : ‖(x : V2)‖ < 1 := by
    rw [pi_norm_lt_iff (by norm_num)]
    intro i
    rw [Real.norm_eq_abs, abs_lt]
    have hb := square_bounds x i
    fin_cases i
    · exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hx.1), lt_of_le_of_ne hb.2 hx.2.1⟩
    · exact ⟨lt_of_le_of_ne hb.1 (Ne.symm hx.2.2.1),
        lt_of_le_of_ne hb.2 hx.2.2.2⟩
  rw [mem_sphere_zero_iff_norm.mp x.property] at hsmall
  exact (lt_irrefl (1 : ℝ)) hsmall

private theorem edge_mem_square (vertical : Bool) {c : ℝ}
    (hc : c = -1 ∨ c = 1) (s : J) : edge vertical c s ∈ Q := by
  have hs := abs_le.mpr s.property
  have hnorm : ‖edge vertical c s‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    cases vertical <;> fin_cases i
    · simpa [edge, Real.norm_eq_abs] using hs
    · rcases hc with rfl | rfl <;> norm_num [edge]
    · rcases hc with rfl | rfl <;> norm_num [edge]
    · simpa [edge, Real.norm_eq_abs] using hs
  apply mem_sphere_zero_iff_norm.mpr
  apply le_antisymm hnorm
  cases vertical
  · have h := norm_le_pi_norm (edge false c (s : ℝ)) 1
    rcases hc with rfl | rfl <;> simpa [edge] using h
  · have h := norm_le_pi_norm (edge true c (s : ℝ)) 0
    rcases hc with rfl | rfl <;> simpa [edge] using h

theorem exists_marked_meridian
    (u0 : Q) (f : ℝ → V) (hf : FinitePiecewiseAffineOn f J) (hinj : InjOn f J)
    (hfminus : f (-1) = (-1, (3 / 2 : ℝ) • (u0 : V2)))
    (hfplus : f 1 = (1, (3 / 2 : ℝ) • (u0 : V2)))
    (hminus : ∀ s ∈ J, (f s).1 = -1 → s = -1)
    (hplus : ∀ s ∈ J, (f s).1 = 1 → s = 1)
    (houter : ∀ s ∈ J, ‖(f s).2‖ < 2)
    (ellI : C(J, ℝ))
    (hellminus : ellI ⟨-1, by norm_num⟩ = 0)
    (hellplus : ellI ⟨1, by norm_num⟩ = 0) :
    ∃ (S : Set V) (gamma : Q ≃ₜ S) (ell : C(Q, ℝ)),
      gamma.IsFinitePL ∧
      (∀ x : Q, (x : V2) 1 = -1 → (gamma x : V) = f ((x : V2) 0)) ∧
      (∀ x : Q, (x : V2) 1 ≠ -1 →
        (gamma x : V) = ((x : V2) 0, ((1 / 4 : ℝ) * ((x : V2) 1 + 7)) • (u0 : V2))) ∧
      (∀ (x : Q) (s : J), (s : ℝ) = (x : V2) 0 →
        (x : V2) 1 = -1 → ell x = ellI s) ∧
      ∀ x : Q, (x : V2) 1 ≠ -1 → ell x = 0 := by
  classical
  let B : Set V2 := edge false (-1) '' J
  let R : Set V2 := (edge true 1 '' J ∪ edge false 1 '' J) ∪ edge true (-1) '' J
  have hBR : B ∪ R = Q := by
    ext x
    constructor
    · rintro (hx | ((hx | hx) | hx)) <;> obtain ⟨s, hs, rfl⟩ := hx
      · exact edge_mem_square false (Or.inl rfl) ⟨s, hs⟩
      · exact edge_mem_square true (Or.inr rfl) ⟨s, hs⟩
      · exact edge_mem_square false (Or.inr rfl) ⟨s, hs⟩
      · exact edge_mem_square true (Or.inl rfl) ⟨s, hs⟩
    · intro hx
      rcases square_has_edge ⟨x, hx⟩ with hm | hp | hm | hp
      · right; right
        refine ⟨x 1, square_bounds ⟨x, hx⟩ 1, ?_⟩
        ext i
        fin_cases i
        · exact hm.symm
        · rfl
      · right; left; left
        refine ⟨x 1, square_bounds ⟨x, hx⟩ 1, ?_⟩
        ext i
        fin_cases i
        · exact hp.symm
        · rfl
      · left
        refine ⟨x 0, square_bounds ⟨x, hx⟩ 0, ?_⟩
        ext i
        fin_cases i
        · rfl
        · exact hm.symm
      · right; left; right
        refine ⟨x 0, square_bounds ⟨x, hx⟩ 0, ?_⟩
        ext i
        fin_cases i
        · rfl
        · exact hp.symm
  have hB (x : Q) : (x : V2) ∈ B ↔ (x : V2) 1 = -1 := by
    constructor
    · rintro ⟨s, _, hs⟩
      exact (congrFun hs 1).symm
    · intro hx
      refine ⟨(x : V2) 0, square_bounds x 0, ?_⟩
      ext i; fin_cases i <;> simp [edge, hx]
  have hRbottom (s : J) : edge false (-1) s ∈ R ↔ (s : ℝ) = -1 ∨ (s : ℝ) = 1 := by
    constructor
    · rintro ((⟨t, _, ht⟩ | ⟨t, _, ht⟩) | ⟨t, _, ht⟩)
      · exact Or.inr (congrFun ht 0).symm
      · have h := congrFun ht 1
        change (1 : ℝ) = -1 at h
        norm_num at h
      · exact Or.inl (congrFun ht 0).symm
    · rintro (hs | hs)
      · right
        refine ⟨-1, by norm_num, ?_⟩
        ext i; fin_cases i <;> simp [edge, hs]
      · left; left
        refine ⟨-1, by norm_num, ?_⟩
        ext i; fin_cases i <;> simp [edge, hs]
  let p0 : V2 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj 0 : V2 →L[ℝ] ℝ).toContinuousAffineMap
  let p1 : V2 →ᴬ[ℝ] ℝ := (ContinuousLinearMap.proj 1 : V2 →L[ℝ] ℝ).toContinuousAffineMap
  let radial : V2 →ᴬ[ℝ] ℝ := (1 / 4 : ℝ) •
    (p1 + ContinuousAffineMap.const ℝ V2 7)
  let out : V2 →ᴬ[ℝ] V := p0.prod
    (((ContinuousLinearMap.id ℝ ℝ).smulRight (u0 : V2)).toContinuousAffineMap.comp radial)
  have hout (x : V2) : out x = (x 0, ((1 / 4 : ℝ) * (x 1 + 7)) • (u0 : V2)) := rfl
  have hu0 : ‖(u0 : V2)‖ = 1 := mem_sphere_zero_iff_norm.mp u0.property
  have hu0ne : (u0 : V2) ≠ 0 := by intro h; rw [h, norm_zero] at hu0; norm_num at hu0
  have houtinj : Function.Injective out := by
    intro x y h
    have h0 : x 0 = y 0 := congrArg Prod.fst h
    have h1 := smul_left_injective ℝ hu0ne (congrArg Prod.snd h)
    change (1 / 4 : ℝ) * (x 1 + 7) = (1 / 4 : ℝ) * (y 1 + 7) at h1
    ext i
    fin_cases i
    · exact h0
    · change x 1 = y 1
      linarith
  have hcorner (s : J) (hs : (s : ℝ) = -1 ∨ (s : ℝ) = 1) :
      f s = out (edge false (-1) s) := by
    rcases hs with hs | hs
    · rw [hs, hfminus, hout]
      change (-1, (3 / 2 : ℝ) • (u0 : V2)) =
        (-1, ((1 / 4 : ℝ) * (-1 + 7)) • (u0 : V2))
      norm_num
    · rw [hs, hfplus, hout]
      change (1, (3 / 2 : ℝ) • (u0 : V2)) =
        (1, ((1 / 4 : ℝ) * (-1 + 7)) • (u0 : V2))
      norm_num
  have hcontact (s : J) (hs : f s ∈ out '' R) : (s : ℝ) = -1 ∨ (s : ℝ) = 1 := by
    obtain ⟨y, ((hy | hy) | hy), hys⟩ := hs
    · obtain ⟨t, ht, rfl⟩ := hy
      exact Or.inr (hplus s s.property (congrArg Prod.fst hys).symm)
    · obtain ⟨t, ht, rfl⟩ := hy
      have hnorm : ‖(f s).2‖ = 2 := by
        rw [← hys, hout]
        change ‖((1 / 4 : ℝ) * (1 + 7)) • (u0 : V2)‖ = 2
        norm_num [norm_smul, hu0]
      exact False.elim (by have h := houter s s.property; linarith)
    · obtain ⟨t, ht, rfl⟩ := hy
      exact Or.inl (hminus s s.property (congrArg Prod.fst hys).symm)
  let G : V2 → V := fun x => if x 1 = -1 then f (x 0) else out x
  have hGbottom (x : V2) (hx : x ∈ B) : G x = f (x 0) := by
    obtain ⟨s, hs, rfl⟩ := hx
    exact if_pos rfl
  have hGrest (x : V2) (hx : x ∈ R) : G x = out x := by
    by_cases hb : x 1 = -1
    · have hxq : x ∈ Q := hBR ▸ Or.inr hx
      let s : J := ⟨x 0, square_bounds ⟨x, hxq⟩ 0⟩
      have hxe : edge false (-1) s = x := by ext i; fin_cases i <;> simp [edge, s, hb]
      have hs : (s : ℝ) = -1 ∨ (s : ℝ) = 1 := (hRbottom s).mp (hxe.symm ▸ hx)
      change (if x 1 = -1 then f (x 0) else out x) = out x
      rw [if_pos hb]
      exact (hcorner s hs).trans (congrArg out hxe)
    · exact if_neg hb
  have hedgePL (vertical : Bool) (c : ℝ) (a : V2 →ᴬ[ℝ] V) :
      FinitePiecewiseAffineOn a (edge vertical c '' J) := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKS, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_affine_interval (by norm_num : (-1 : ℝ) < 1)
        (edge vertical c) (edge_injective vertical c).injOn
    exact ⟨K, hK, hKS, K.affineOnFaces_affine a⟩
  have hGB : FinitePiecewiseAffineOn G B := by
    obtain ⟨K, hK, hKB, _⟩ := hedgePL false (-1) out
    have hp0 : FinitePiecewiseAffineOn p0 B :=
      ⟨K, hK, hKB, K.affineOnFaces_affine p0⟩
    have hfcomp := hf.comp hp0 (by rintro x ⟨s, hs, rfl⟩; exact hs)
    exact hfcomp.congr (fun x hx => (hGbottom x hx).symm)
  have houtR : FinitePiecewiseAffineOn out R :=
    finitePiecewiseAffineOn_union
      (finitePiecewiseAffineOn_union (hedgePL true 1 out) (hedgePL false 1 out))
      (hedgePL true (-1) out)
  have hGR : FinitePiecewiseAffineOn G R := houtR.congr (fun x hx => (hGrest x hx).symm)
  have hG : FinitePiecewiseAffineOn G Q := hBR ▸ finitePiecewiseAffineOn_union hGB hGR
  have hGinj : InjOn G Q := by
    intro x hx y hy hxy
    by_cases hxb : x 1 = -1 <;> by_cases hyb : y 1 = -1
    · have hfst := hinj (square_bounds ⟨x, hx⟩ 0) (square_bounds ⟨y, hy⟩ 0)
        (by simpa only [G, if_pos hxb, if_pos hyb] using hxy)
      ext i; fin_cases i
      · exact hfst
      · exact hxb.trans hyb.symm
    · have hyR : y ∈ R := (hBR.symm ▸ hy).resolve_left
        (fun hb => hyb ((hB ⟨y, hy⟩).mp hb))
      let s : J := ⟨x 0, square_bounds ⟨x, hx⟩ 0⟩
      have hfout : f s = out y := by simpa only [G, if_pos hxb, if_neg hyb] using hxy
      have hc := hcorner s (hcontact s ⟨y, hyR, hfout.symm⟩)
      have hxe : edge false (-1) s = x := by ext i; fin_cases i <;> simp [edge, s, hxb]
      exact houtinj ((congrArg out hxe).symm.trans (hc.symm.trans hfout))
    · have hxR : x ∈ R := (hBR.symm ▸ hx).resolve_left
        (fun hb => hxb ((hB ⟨x, hx⟩).mp hb))
      let s : J := ⟨y 0, square_bounds ⟨y, hy⟩ 0⟩
      have hfout : f s = out x := by simpa only [G, if_neg hxb, if_pos hyb] using hxy.symm
      have hc := hcorner s (hcontact s ⟨x, hxR, hfout.symm⟩)
      have hye : edge false (-1) s = y := by ext i; fin_cases i <;> simp [edge, s, hyb]
      exact (houtinj ((congrArg out hye).symm.trans (hc.symm.trans hfout))).symm
    · apply houtinj
      simpa only [G, if_neg hxb, if_neg hyb] using hxy
  obtain ⟨gamma, hgamma, hgammaval⟩ := hG.exists_homeomorph_image hGinj
  let BQ : Set Q := Subtype.val ⁻¹' B
  let RQ : Set Q := Subtype.val ⁻¹' R
  let pr : C(Q, J) := ⟨fun x => ⟨(x : V2) 0, square_bounds x 0⟩,
    ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _⟩
  let low : C(BQ, ℝ) := ellI.comp (pr.comp ⟨Subtype.val, continuous_subtype_val⟩)
  let high : C(RQ, ℝ) := ⟨fun _ => 0, continuous_const⟩
  have hcover : BQ ∪ RQ = univ := by
    ext x
    exact iff_true_intro (hBR.symm.subset x.property)
  obtain ⟨ell, hellB, hellR⟩ := glue_closed_cover BQ RQ
    (hGB.isCompact.isClosed.preimage continuous_subtype_val)
    (hGR.isCompact.isClosed.preimage continuous_subtype_val) hcover low high (by
      intro x hxB hxR
      obtain ⟨s, hs, hse⟩ := hxB
      have hsend := (hRbottom ⟨s, hs⟩).mp (hse.symm ▸ hxR)
      have hp : pr x = ⟨s, hs⟩ := Subtype.ext (congrFun hse 0).symm
      change ellI (pr x) = 0
      rw [hp]
      rcases hsend with hs' | hs'
      · have he : (⟨s, hs⟩ : J) = ⟨-1, by norm_num⟩ := Subtype.ext hs'
        rw [he, hellminus]
      · have he : (⟨s, hs⟩ : J) = ⟨1, by norm_num⟩ := Subtype.ext hs'
        rw [he, hellplus])
  refine ⟨G '' Q, gamma, ell, hgamma, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hgammaval]
    exact if_pos hx
  · intro x hx
    rw [hgammaval]
    exact if_neg hx
  · intro x s hs hx
    have hxB : x ∈ BQ := (hB x).mpr hx
    rw [hellB ⟨x, hxB⟩]
    change ellI (pr x) = ellI s
    congr 1
    exact Subtype.ext hs.symm
  · intro x hx
    have hxR : x ∈ RQ := (hBR.symm.subset x.property).resolve_left
      (fun hb => hx ((hB x).mp hb))
    exact hellR ⟨x, hxR⟩

end PoincareConjecture.M76.HamiltonIndexOne
