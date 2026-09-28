import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.PlanarTubeStrands
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Arcs.ReturningRibbonSides

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "D" => Dehn.signedTubeDiamond
local notation "Z" => (Set.preimage (Prod.snd : (ℝ × ℝ) → ℝ) ({0} : Set ℝ))

theorem exists_outer_strand_of_planar_signed_ribbon
    {r : ℝ} (hr : 0 < r) (f : V → V)
    (hf : FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ I))
    (hi : InjOn f (Icc (-r) r ×ˢ I))
    (hup : ∀ z ∈ Icc (-r) r ×ˢ I, 0 ≤ (f z).2)
    (hends : ∀ c ∈ Icc (-r) r, (f (c, 0)).2 = 0 ∧ (f (c, 1)).2 = 0)
    {S : Set V} (hS : ∀ z ∈ Icc (-r) r ×ˢ I, f z ∈ S ↔ z.1 = 0)
    {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hPu : ∀ i, 0 ≤ (P i).2)
    (hboundary : P.boundary ℝ = ((fun t : ℝ => f (0, t)) '' I) ∪
      segment ℝ (f (0, 0)) (f (0, 1)))
    (horder : (f (0, 0)).1 < (f (0, 1)).1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, c ∈ Ioo (-r) r ∧ |c| < ε ∧ c ≠ 0 ∧
      (f (c, 0)).1 < (f (0, 0)).1 ∧
      (f (0, 0)).1 < (f (0, 1)).1 ∧ (f (0, 1)).1 < (f (c, 1)).1 ∧
      FinitePiecewiseAffineOn (fun t : ℝ => f (c, t)) I ∧
      InjOn (fun t : ℝ => f (c, t)) I ∧
      IsFinitePLBallPair ℝ ((fun t : ℝ => f (c, t)) '' I) {f (c, 0), f (c, 1)} ∧
      ((fun t : ℝ => f (c, t)) '' I) ∩ Z = {f (c, 0), f (c, 1)} ∧
      Disjoint ((fun t : ℝ => f (c, t)) '' I) S := by
  classical
  have h0 : (0 : ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.mpr hr, hr⟩
  have hIc : Ioo (-r) r ⊆ Icc (-r) r := Ioo_subset_Icc_self
  have h01 : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩
  let B : ℝ → Set V := fun c => (fun t : ℝ => f (c, t)) '' I
  let a : ℝ → V := fun c => f (c, 0)
  let b : ℝ → V := fun c => f (c, 1)
  have hstrands (c : ℝ) (hc : c ∈ Icc (-r) r) :
      FinitePiecewiseAffineOn (fun t : ℝ => f (c, t)) I ∧
      InjOn (fun t : ℝ => f (c, t)) I ∧ IsFinitePLBallPair ℝ (B c) {a c, b c} := by
    have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
    have hcopy := hI
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcopy
    let line : ℝ →ᴬ[ℝ] V :=
      (ContinuousAffineMap.const ℝ ℝ c).prod (ContinuousAffineMap.id ℝ ℝ)
    have hline : FinitePiecewiseAffineOn line I :=
      ⟨K, hK, hKs, K.affineOnFaces_affine line⟩
    have hfc : FinitePiecewiseAffineOn (fun t : ℝ => f (c, t)) I :=
      hf.comp hline (fun t ht => ⟨hc, ht⟩)
    have hic : InjOn (fun t : ℝ => f (c, t)) I := by
      intro t ht u hu htu
      exact congrArg Prod.snd (hi ⟨hc, ht⟩ ⟨hc, hu⟩ htu)
    refine ⟨hfc, hic, ?_⟩
    simpa only [image_pair] using hI.image hfc hic
  have hpositive (z : V) (hz : z ∈ Ioo (-r) r ×ˢ Ioo (0 : ℝ) 1) :
      0 < (f z).2 := by
    have hmap : f '' (Icc (-r) r ×ˢ I) ⊆ (univ : Set ℝ) ×ˢ Ici (0 : ℝ) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨mem_univ _, hup x hx⟩
    have hfi := hf.mem_interior_image rfl hi
      (show z ∈ interior (Icc (-r) r ×ˢ I) by
        simpa only [interior_prod_eq, interior_Icc] using hz)
    have h := interior_mono hmap hfi
    rw [interior_prod_eq, interior_univ, interior_Ici] at h
    exact h.2
  have haxis (c : ℝ) (hc : c ∈ Ioo (-r) r) : B c ∩ Z = {a c, b c} := by
    ext y
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hy0⟩
      by_cases ht0 : t = 0
      · exact Or.inl (by subst t; rfl)
      by_cases ht1 : t = 1
      · exact Or.inr (by subst t; rfl)
      have hp := hpositive (c, t) ⟨hc,
        lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
      exact (hp.ne' hy0).elim
    · rintro (rfl | rfl)
      · exact ⟨⟨0, h01, rfl⟩, (hends c (hIc hc)).1⟩
      · exact ⟨⟨1, h11, rfl⟩, (hends c (hIc hc)).2⟩
  have htrace (t : ℝ) (ht : t ∈ I) :
      ContinuousOn (fun c => (f (c, t)).1) (Icc (-r) r) :=
    continuous_fst.continuousOn.comp
      (hf.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun c hc => ⟨hc, ht⟩)) (fun _ _ => mem_univ _)
  have hatrace : InjOn (fun c => (a c).1) (Icc (-r) r) := by
    intro c hc d hd hcd
    have hpair : f (c, 0) = f (d, 0) :=
      Prod.ext hcd ((hends c hc).1.trans (hends d hd).1.symm)
    exact congrArg Prod.fst (hi ⟨hc, h01⟩ ⟨hd, h01⟩ hpair)
  have hBup (c : ℝ) (hc : c ∈ Icc (-r) r) : ∀ z ∈ B c, 0 ≤ z.2 := by
    rintro _ ⟨t, ht, rfl⟩
    exact hup (c, t) ⟨hc, ht⟩
  have hBS (c : ℝ) (hc : c ∈ Icc (-r) r) (hc0 : c ≠ 0) : Disjoint (B c) S := by
    apply disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ hs
    exact hc0 ((hS (c, t) ⟨hc, ht⟩).mp hs)
  have hAS : B 0 ⊆ S := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hS (0, t) ⟨hIc h0, ht⟩).mpr rfl
  have hclosed : IsClosed (B 0) :=
    (isCompact_Icc.image_of_continuousOn (hstrands 0 (hIc h0)).1.continuousOn).isClosed
  obtain ⟨c, hc, hcε, hc0, hac, huv, hbc, hball, _⟩ :=
    P.exists_outer_returning_ribbon_side hP hPi hPu hboundary hclosed (haxis 0 h0)
      hr B a b (htrace 0 h01) hatrace (htrace 1 h11) rfl rfl horder
      (fun c hc hc0 => ⟨(hstrands c (hIc hc)).2.2, haxis c hc, hBup c (hIc hc),
        (hBS c (hIc hc) hc0).symm.mono_left hAS⟩) hε
  exact ⟨c, hc, hcε, hc0, hac, huv, hbc, (hstrands c (hIc hc)).1,
    (hstrands c (hIc hc)).2.1, hball, haxis c hc, hBS c (hIc hc) hc0⟩

theorem exists_outer_signed_tube_strand
    {T triangle sphere arc : Set V3}
    (tube : ↥(D ×ˢ I) ≃ₜ T) (htube : tube.IsFinitePL)
    (htriangle : ∀ x : ↥(D ×ˢ I),
      (x : P3).1 ∈ Dehn.signedTubeSheet 0 ↔ (tube x : V3) ∈ triangle)
    (hsphere : ∀ x : ↥(D ×ˢ I),
      (x : P3).1 ∈ Dehn.signedTubeSheet 1 ↔ (tube x : V3) ∈ sphere)
    (R : V3 →ᴬ[ℝ] V) (F : V → V3) (hFR : EqOn (F ∘ R) id triangle)
    (hupper : ∀ y ∈ triangle, 0 ≤ (R y).2)
    (hends : ∀ x : ↥(D ×ˢ I), (x : P3).1 ∈ Dehn.signedTubeSheet 0 →
      ((x : P3).2 = 0 ∨ (x : P3).2 = 1) → (R (tube x : V3)).2 = 0)
    (b : I ≃ₜ arc)
    (haxis : ∀ t : I, (tube ⟨((0, 0), t),
      (Dehn.signedTubeDiamond_coordinate_iff (0, 0)).mpr (by norm_num), t.property⟩ : V3) = b t)
    {u v : V} (hu : R (b ⟨0, le_rfl, zero_le_one⟩ : V3) = u)
    (hv : R (b ⟨1, zero_le_one, le_rfl⟩ : V3) = v)
    {n : ℕ} (P : Polygon V (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hPu : ∀ i, 0 ≤ (P i).2)
    (hboundary : P.boundary ℝ = R '' arc ∪ segment ℝ u v)
    (horder : u.1 < v.1) {r ε : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hε : 0 < ε) :
    ∃ (f : V → V) (c : ℝ),
      FinitePiecewiseAffineOn f (Icc (-r) r ×ˢ I) ∧
      InjOn f (Icc (-r) r ×ˢ I) ∧
      (∀ (d : Icc (-r) r) (t : I),
        f (d, t) = R (tube ⟨((0, d), t),
          (Dehn.signedTubeDiamond_coordinate_iff (0, d)).mpr
            (by simpa using (abs_le.mpr d.property).trans hr1), t.property⟩ : V3)) ∧
      c ∈ Ioo (-r) r ∧ |c| < ε ∧ c ≠ 0 ∧
      (f (c, 0)).1 < u.1 ∧ u.1 < v.1 ∧ v.1 < (f (c, 1)).1 ∧
      FinitePiecewiseAffineOn (fun t : ℝ => f (c, t)) I ∧
      InjOn (fun t : ℝ => f (c, t)) I ∧
      IsFinitePLBallPair ℝ ((fun t : ℝ => f (c, t)) '' I) {f (c, 0), f (c, 1)} ∧
      ((fun t : ℝ => f (c, t)) '' I) ∩ Z = {f (c, 0), f (c, 1)} ∧
      Disjoint ((fun t : ℝ => f (c, t)) '' I) (R '' (triangle ∩ sphere)) := by
  obtain ⟨f, hf, hfi, hmap, hfval, hfS, _, _, _⟩ :=
    exists_planar_signed_tube_ribbon tube htube htriangle hsphere R F hFR hr hr1
  have h0 : (0 : ℝ) ∈ Icc (-r) r := ⟨(neg_lt_zero.mpr hr).le, hr.le⟩
  have hfaxis (t : I) : f (0, t) = R (b t : V3) :=
    (hfval ⟨0, h0⟩ t).trans (congrArg R (haxis t))
  have hfu : f (0, 0) = u := (hfaxis ⟨0, le_rfl, zero_le_one⟩).trans hu
  have hfv : f (0, 1) = v := (hfaxis ⟨1, zero_le_one, le_rfl⟩).trans hv
  have hcentral : (fun t : ℝ => f (0, t)) '' I = R '' arc := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨b ⟨t, ht⟩, (b ⟨t, ht⟩).property, (hfaxis ⟨t, ht⟩).symm⟩
    · rintro ⟨x, hx, rfl⟩
      let t : I := b.symm ⟨x, hx⟩
      refine ⟨t, t.property, ?_⟩
      change f (0, (t : ℝ)) = R x
      rw [hfaxis t]
      exact congrArg (fun z : arc => R (z : V3)) (b.apply_symm_apply ⟨x, hx⟩)
  have hfends (c : ℝ) (hc : c ∈ Icc (-r) r) :
      (f (c, 0)).2 = 0 ∧ (f (c, 1)).2 = 0 := by
    have hface (t : I) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) : (f (c, t)).2 = 0 := by
      rw [hfval ⟨c, hc⟩ t]
      apply hends _ _ ht
      apply (Dehn.signedTubeSheet_coordinate_iff (0, c)
        ((Dehn.signedTubeDiamond_coordinate_iff (0, c)).mpr
          (by simpa using (abs_le.mpr hc).trans hr1)) 0).mpr
      simp
    exact ⟨hface ⟨0, le_rfl, zero_le_one⟩ (Or.inl rfl),
      hface ⟨1, zero_le_one, le_rfl⟩ (Or.inr rfl)⟩
  have hfup (z : V) (hz : z ∈ Icc (-r) r ×ˢ I) : 0 ≤ (f z).2 := by
    obtain ⟨y, hy, heq⟩ := hmap hz
    rw [← heq]
    exact hupper y hy
  have hfb : P.boundary ℝ = ((fun t : ℝ => f (0, t)) '' I) ∪
      segment ℝ (f (0, 0)) (f (0, 1)) := by
    rw [hcentral, hfu, hfv]
    exact hboundary
  have hfo : (f (0, 0)).1 < (f (0, 1)).1 := by rwa [hfu, hfv]
  obtain ⟨c, hc, hcε, hc0, hac, huv, hbc, hfc, hci, hball, haxis', hdis⟩ :=
    exists_outer_strand_of_planar_signed_ribbon hr f hf hfi hfup hfends hfS
      P hP hPi hPu hfb hfo hε
  simp only [hfu, hfv] at hac huv hbc
  exact ⟨f, c, hf, hfi, hfval, hc, hcε, hc0, hac, huv, hbc, hfc, hci, hball, haxis', hdis⟩

end PoincareConjecture.M76
