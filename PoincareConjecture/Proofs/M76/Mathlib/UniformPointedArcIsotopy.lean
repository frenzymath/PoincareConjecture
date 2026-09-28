import PoincareConjecture.Proofs.M76.Mathlib.FixedResidualPointedIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.PointedArcResidualContact











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]











theorem IsFinitePL.exists_uniform_pointed_arc_isotopy_with_charts_with_global_finitePL_and_signs
    {B T d b U R : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    (hupperPL : FinitePiecewiseAffineOn upper B)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hqB : (q : E) ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x)
    (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {(q : E)})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ r g : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      (∀ x ∈ d,
        (0 < r x → x ∈ closure (d ∩ {y | r y < r x})) ∧
          (r x < 2 → x ∈ closure (d ∩ {y | r x < r y}))) ∧
      FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧ EqOn g r d ∧
      (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ R, g x = 0) ∧
      (∀ x, x ∉ U → g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          (∀ x ∈ R, H t x = x) ∧
          FinitePiecewiseAffineOn (H t : E → E) d ∧
          FinitePiecewiseAffineOn (H t : E → E) T ∧
          (∀ c : ℝ,
            ∃ L : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                ((H t '' T) ∩ {x | A x = c} : Set E), L.IsFinitePL ∧
              (∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                (L x : E) ∈ R ↔ upper x = c) ∧
              ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                  (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                  ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                  (upper x = c ↔ (p : E × ℝ).2 = upper x)) ∧
          ∀ _ht : 0 < (t : ℝ), ∀ a ∈ Ioo (0 : ℝ) 2,
            ∃ L : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                ((H t '' T) ∩ {x | A x = (t : ℝ) * a} : Set E), L.IsFinitePL ∧
              (∀ x ∈ b, a ≤ r x → (t : ℝ) * a < upper x) ∧
              IsFinitePLBallPair ℝ (b ∩ {x | (t : ℝ) * a ≤ upper x})
                (b ∩ {x | upper x = (t : ℝ) * a}) ∧
              (∀ x : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)},
                (L x : E) ∈ R ↔ upper x = (t : ℝ) * a) ∧
              (∀ x : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)},
                ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                  (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                  ((t : ℝ) * g x = (t : ℝ) * a ↔ (p : E × ℝ).2 = 0) ∧
                  (upper x = (t : ℝ) * a ↔ (p : E × ℝ).2 = upper x)) ∧
              ∃ f : E → E, (∀ x, (L x : E) = f x) ∧
                FinitePiecewiseAffineOn f
                  ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x}) ∧
                IsFinitePLBallPair ℝ
                  (((H t '' d) ∩ {x | A x = (t : ℝ) * a}) ∪
                    f '' ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x}))
                  (f '' (b ∩ {x | upper x = (t : ℝ) * a})) ∧
                ((((H t '' d) ∩ {x | A x = (t : ℝ) * a}) ∪
                    f '' ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x})) ∩ R =
                  f '' (b ∩ {x | upper x = (t : ℝ) * a})) ∧
                (∀ x ∈ b ∩ {x | r x = a}, f x = H t x) ∧
                ∀ x ∈ b ∩ {x | upper x = (t : ℝ) * a},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = x ∧ (p : E × ℝ).2 = upper x ∧ f x = C p := by
  obtain ⟨r, hr, hmin, hmax, hsigns, hrsub, hrsuper, g, hgT, hgn, hgr, hgQ, hgR, hgU, _,
      ε₀, hε₀, H₀, hglobal, hc₀, hci₀, hformula, hall⟩ :=
    hC.exists_pointed_cap_collar_isotopy_fixed_residual_with_global_finitePL_and_signs
      hupper hupperPL
      A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv Q hQ hQd
      J hJ hJR hRzero hresidual hU hdU
  have hbB : b ⊆ B := by
    intro x hx
    have hxT : x ∈ T := (hcap.symm.subset hx).2
    let p := C.symm ⟨x, hxT⟩
    have hCp : (C p : E) = x := congrArg Subtype.val (C.apply_symm_apply _)
    have hp0 : (p : E × ℝ).2 = 0 :=
      (hheight p).symm.trans ((congrArg A hCp).trans (hdplane (hd.1 hx)))
    have hpx : (p : E × ℝ).1 = x := (hbottom p hp0).symm.trans hCp
    exact hpx ▸ p.property.1
  have hone : (1 : ℝ) ∈ Ioo 0 2 := by constructor <;> norm_num
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K₀, hK₀, hK₀s, _⟩, _⟩, _⟩ := hrsub 1 hone
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K₁, hK₁, hK₁s, _⟩, _⟩, _⟩ := hrsuper 1 hone
  obtain ⟨K, hK, hKs⟩ := K₀.exists_finite_triangulation_union K₁ hK₀ hK₁
  have hKb : K.space = b := by
    rw [hKs, hK₀s, hK₁s]
    ext x
    constructor
    · rintro (hx | hx) <;> exact hx.1
    · intro hx
      rcases le_total (r x) 1 with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hurb : FinitePiecewiseAffineOn upper b := by
    rw [← hKb]
    exact hupperPL.restrict K hK (hKb.subset.trans hbB)
  obtain ⟨δ, hδ, hcuts⟩ := hd.exists_uniform_pointed_rim_cuts hr hurb q
    ((hmin q (hd.1 q.property)).2.mpr rfl) hqzero (fun x hx => hpos x (hbB hx))
  let ε := min ε₀ δ
  have hε : 0 < ε := lt_min hε₀ hδ
  have hεle : ε ≤ ε₀ := min_le_left _ _
  let embed : Icc (-ε) ε → Icc (-ε₀) ε₀ := fun t =>
    ⟨t, (neg_le_neg hεle).trans t.property.1, t.property.2.trans hεle⟩
  have hembed : Continuous embed := continuous_subtype_val.subtype_mk _
  let H : Icc (-ε) ε → E ≃ₜ E := fun t => H₀ (embed t)
  have hHval (t : Icc (-ε) ε) (x : E) : H t x = x + ((t : ℝ) * g x) • v :=
    hformula (embed t) x
  refine ⟨r, g, hr, hmin, hmax, hsigns, hgT, hgn, hgr, hgQ, hgR, hgU, ε, hε, H,
    (fun t => hglobal (embed t)),
    hc₀.comp ((hembed.comp continuous_fst).prodMk continuous_snd),
    hci₀.comp ((hembed.comp continuous_fst).prodMk continuous_snd), hHval, fun t => ?_⟩
  obtain ⟨hfix, hHd, hHT, _, hcaplevels, _, hlevels⟩ := hall (embed t)
  refine ⟨hfix, hHd, hHT, hlevels, fun ht a ha => ?_⟩
  have htδ : (t : ℝ) ∈ Ioc 0 δ :=
    ⟨ht, t.property.2.trans (min_le_right _ _)⟩
  obtain ⟨hhigh, hwidth⟩ := hcuts t htδ a ha
  obtain ⟨L, hL, hLres, hLp⟩ := hlevels ((t : ℝ) * a)
  have hHheight (x : E) (hx : x ∈ d) : A (H t x) = (t : ℝ) * r x := by
    rw [hHval, hgr hx, add_comm x]
    change A (((t : ℝ) * r x) • v +ᵥ x) = (t : ℝ) * r x
    rw [A.map_vadd, map_smul, hv]
    change (t : ℝ) * r x * 1 + A x = (t : ℝ) * r x
    rw [hdplane hx, mul_one, add_zero]
  obtain ⟨f, hfval, hfJ, hball, hlow⟩ :=
    hL.exists_pointed_cap_collar_level_arc A hheight hbottom hdplane hcap (H t) ht
      hgr hHheight hhigh (hrsub a ha) (hrsuper a ha) hwidth
      (hcaplevels ht.ne' a ha) hLp
  have hJS : (b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x} ⊆
      {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)} := by
    intro x hx
    refine ⟨hbB hx.1.1, ?_, hx.2⟩
    rw [hgr (hd.1 hx.1.1)]
    exact mul_le_mul_of_nonneg_left hx.1.2 ht.le
  have hcontact (x : E)
      (hx : x ∈ (b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x}) :
      f x ∈ R ↔ upper x = (t : ℝ) * a := by
    rw [← hfval ⟨x, hJS hx⟩]
    exact hLres _
  refine ⟨L, hL, hhigh, hwidth, hLres, hLp, f, hfval, hfJ, hball,
    (H t).pointed_cap_collar_arc_inter_fixed_residual hdplane (mul_pos ht ha.1)
      hfix hhigh hcontact, hlow, ?_⟩
  intro x hx
  obtain ⟨_, _, houter⟩ := rim_superlevel_truncated_sublevel_partition hhigh
  obtain ⟨p, hpbase, hpval, _, hphi⟩ := hLp ⟨x, hJS (houter hx)⟩
  have hptop : (p : E × ℝ).2 = upper x := hphi.mp hx.2
  have hpR : (C p : E) ∈ R := (hresidual p).mpr (hptop.trans (congrArg upper hpbase).symm)
  refine ⟨p, hpbase, hptop, ?_⟩
  exact (hfval _).symm.trans (hpval.trans (hfix _ hpR))




theorem IsFinitePL.exists_uniform_pointed_arc_isotopy_with_charts_with_global_finitePL
    {B T d b U R : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    (hupperPL : FinitePiecewiseAffineOn upper B)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hqB : (q : E) ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x)
    (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {(q : E)})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ r g : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧ EqOn g r d ∧
      (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ R, g x = 0) ∧
      (∀ x, x ∉ U → g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          (∀ x ∈ R, H t x = x) ∧
          FinitePiecewiseAffineOn (H t : E → E) d ∧
          FinitePiecewiseAffineOn (H t : E → E) T ∧
          (∀ c : ℝ,
            ∃ L : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                ((H t '' T) ∩ {x | A x = c} : Set E), L.IsFinitePL ∧
              (∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                (L x : E) ∈ R ↔ upper x = c) ∧
              ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                  (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                  ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                  (upper x = c ↔ (p : E × ℝ).2 = upper x)) ∧
          ∀ _ht : 0 < (t : ℝ), ∀ a ∈ Ioo (0 : ℝ) 2,
            ∃ L : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                ((H t '' T) ∩ {x | A x = (t : ℝ) * a} : Set E), L.IsFinitePL ∧
              (∀ x ∈ b, a ≤ r x → (t : ℝ) * a < upper x) ∧
              IsFinitePLBallPair ℝ (b ∩ {x | (t : ℝ) * a ≤ upper x})
                (b ∩ {x | upper x = (t : ℝ) * a}) ∧
              (∀ x : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)},
                (L x : E) ∈ R ↔ upper x = (t : ℝ) * a) ∧
              (∀ x : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)},
                ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                  (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                  ((t : ℝ) * g x = (t : ℝ) * a ↔ (p : E × ℝ).2 = 0) ∧
                  (upper x = (t : ℝ) * a ↔ (p : E × ℝ).2 = upper x)) ∧
              ∃ f : E → E, (∀ x, (L x : E) = f x) ∧
                FinitePiecewiseAffineOn f
                  ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x}) ∧
                IsFinitePLBallPair ℝ
                  (((H t '' d) ∩ {x | A x = (t : ℝ) * a}) ∪
                    f '' ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x}))
                  (f '' (b ∩ {x | upper x = (t : ℝ) * a})) ∧
                ((((H t '' d) ∩ {x | A x = (t : ℝ) * a}) ∪
                    f '' ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x})) ∩ R =
                  f '' (b ∩ {x | upper x = (t : ℝ) * a})) ∧
                (∀ x ∈ b ∩ {x | r x = a}, f x = H t x) ∧
                ∀ x ∈ b ∩ {x | upper x = (t : ℝ) * a},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = x ∧ (p : E × ℝ).2 = upper x ∧ f x = C p := by
  obtain ⟨r, g, hr, hmin, hmax, _, hrest⟩ :=
    hC.exists_uniform_pointed_arc_isotopy_with_charts_with_global_finitePL_and_signs
      hupper hupperPL A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv
      Q hQ hQd J hJ hJR hRzero hresidual hU hdU
  exact ⟨r, g, hr, hmin, hmax, hrest⟩




theorem IsFinitePL.exists_uniform_pointed_arc_isotopy_with_charts
    {B T d b U R : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    (hupperPL : FinitePiecewiseAffineOn upper B)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hqB : (q : E) ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x)
    (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {(q : E)})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ r g : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧ EqOn g r d ∧
      (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ R, g x = 0) ∧
      (∀ x, x ∉ U → g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          (∀ x ∈ R, H t x = x) ∧
          FinitePiecewiseAffineOn (H t : E → E) d ∧
          FinitePiecewiseAffineOn (H t : E → E) T ∧
          (∀ c : ℝ,
            ∃ L : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                ((H t '' T) ∩ {x | A x = c} : Set E), L.IsFinitePL ∧
              (∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                (L x : E) ∈ R ↔ upper x = c) ∧
              ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                  (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                  ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                  (upper x = c ↔ (p : E × ℝ).2 = upper x)) ∧
          ∀ _ht : 0 < (t : ℝ), ∀ a ∈ Ioo (0 : ℝ) 2,
            ∃ L : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                ((H t '' T) ∩ {x | A x = (t : ℝ) * a} : Set E), L.IsFinitePL ∧
              (∀ x ∈ b, a ≤ r x → (t : ℝ) * a < upper x) ∧
              IsFinitePLBallPair ℝ (b ∩ {x | (t : ℝ) * a ≤ upper x})
                (b ∩ {x | upper x = (t : ℝ) * a}) ∧
              (∀ x : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)},
                (L x : E) ∈ R ↔ upper x = (t : ℝ) * a) ∧
              (∀ x : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)},
                ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                  (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                  ((t : ℝ) * g x = (t : ℝ) * a ↔ (p : E × ℝ).2 = 0) ∧
                  (upper x = (t : ℝ) * a ↔ (p : E × ℝ).2 = upper x)) ∧
              ∃ f : E → E, (∀ x, (L x : E) = f x) ∧
                FinitePiecewiseAffineOn f
                  ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x}) ∧
                IsFinitePLBallPair ℝ
                  (((H t '' d) ∩ {x | A x = (t : ℝ) * a}) ∪
                    f '' ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x}))
                  (f '' (b ∩ {x | upper x = (t : ℝ) * a})) ∧
                ((((H t '' d) ∩ {x | A x = (t : ℝ) * a}) ∪
                    f '' ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x})) ∩ R =
                  f '' (b ∩ {x | upper x = (t : ℝ) * a})) ∧
                (∀ x ∈ b ∩ {x | r x = a}, f x = H t x) ∧
                ∀ x ∈ b ∩ {x | upper x = (t : ℝ) * a},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = x ∧ (p : E × ℝ).2 = upper x ∧ f x = C p := by
  obtain ⟨r, g, hr, hmin, hmax, hgT, hgn, hgr, hgQ, hgR, hgU,
      ε, hε, H, _, hrest⟩ :=
    hC.exists_uniform_pointed_arc_isotopy_with_charts_with_global_finitePL
      hupper hupperPL A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv
      Q hQ hQd J hJ hJR hRzero hresidual hU hdU
  exact ⟨r, g, hr, hmin, hmax, hgT, hgn, hgr, hgQ, hgR, hgU,
    ε, hε, H, hrest⟩







theorem IsFinitePL.exists_uniform_pointed_arc_isotopy
    {B T d b U R : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    (hupperPL : FinitePiecewiseAffineOn upper B)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hqB : (q : E) ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x)
    (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {(q : E)})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ r g : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧ EqOn g r d ∧
      (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ R, g x = 0) ∧
      (∀ x, x ∉ U → g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          (∀ x ∈ R, H t x = x) ∧
          FinitePiecewiseAffineOn (H t : E → E) d ∧
          FinitePiecewiseAffineOn (H t : E → E) T ∧
          ∀ _ht : 0 < (t : ℝ), ∀ a ∈ Ioo (0 : ℝ) 2,
            ∃ L : {x : E | x ∈ B ∧ (t : ℝ) * a ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                ((H t '' T) ∩ {x | A x = (t : ℝ) * a} : Set E), L.IsFinitePL ∧
              ∃ f : E → E, (∀ x, (L x : E) = f x) ∧
                FinitePiecewiseAffineOn f
                  ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x}) ∧
                IsFinitePLBallPair ℝ
                  (((H t '' d) ∩ {x | A x = (t : ℝ) * a}) ∪
                    f '' ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x}))
                  (f '' (b ∩ {x | upper x = (t : ℝ) * a})) ∧
                ((((H t '' d) ∩ {x | A x = (t : ℝ) * a}) ∪
                    f '' ((b ∩ {x | r x ≤ a}) ∩ {x | (t : ℝ) * a ≤ upper x})) ∩ R =
                  f '' (b ∩ {x | upper x = (t : ℝ) * a})) ∧
                (∀ x ∈ b ∩ {x | r x = a}, f x = H t x) ∧
                ∀ x ∈ b ∩ {x | upper x = (t : ℝ) * a},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = x ∧ (p : E × ℝ).2 = upper x ∧ f x = C p := by
  obtain ⟨r, g, hr, hmin, hmax, hgT, hgn, hgr, hgQ, hgR, hgU,
      ε, hε, H, hc, hci, hformula, hall⟩ :=
    hC.exists_uniform_pointed_arc_isotopy_with_charts hupper hupperPL A hheight hbottom
      hd hdplane q hqB hqzero hpos hcap v hv Q hQ hQd J hJ hJR hRzero hresidual hU hdU
  refine ⟨r, g, hr, hmin, hmax, hgT, hgn, hgr, hgQ, hgR, hgU,
    ε, hε, H, hc, hci, hformula, fun t => ?_⟩
  obtain ⟨hfix, hHd, hHT, _, hlevels⟩ := hall t
  refine ⟨hfix, hHd, hHT, fun ht a ha => ?_⟩
  obtain ⟨L, hL, _, _, _, _, hrest⟩ := hlevels ht a ha
  exact ⟨L, hL, hrest⟩

end Homeomorph
