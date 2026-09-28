import PoincareConjecture.Proofs.M76.Mathlib.FixedUpperPointedIsotopy

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.exists_pointed_cap_collar_isotopy_fixed_residual_with_global_finitePL_and_signs
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
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      (∀ x ∈ d,
        (0 < r x → x ∈ closure (d ∩ {y | r y < r x})) ∧
          (r x < 2 → x ∈ closure (d ∩ {y | r x < r y}))) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a})) ∧
      ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
        EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ R, g x = 0) ∧
        (∀ x, x ∉ U → g x = 0) ∧
        (∀ x (hx : x ∈ B), g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0) ∧
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
            IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
            ((t : ℝ) ≠ 0 → ∀ a : ℝ, a ∈ Ioo 0 2 →
              IsFinitePLBallPair ℝ ((H t '' d) ∩ {x | A x = (t : ℝ) * a})
                ((H t '' b) ∩ {x | A x = (t : ℝ) * a})) ∧
            (∀ c : ℝ, ((H t '' d) ∩ {x | A x = c}) ∩
                ((H t '' T) ∩ {x | A x = c}) = (H t '' b) ∩ {x | A x = c}) ∧
            ∀ c : ℝ,
              ∃ L : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                  ((H t '' T) ∩ {x | A x = c} : Set E), L.IsFinitePL ∧
                (∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  (L x : E) ∈ R ↔ upper x = c) ∧
                ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                    ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                    (upper x = c ↔ (p : E × ℝ).2 = upper x) := by
  obtain ⟨W, hW, hWs⟩ := Q.exists_finite_triangulation_union J hQ hJ
  have hWd : d ∩ W.space ⊆ {(q : E)} := by
    intro x hx
    rcases hWs.subset hx.2 with hxQ | hxJ
    · exact hQd ⟨hx.1, hxQ⟩
    · exact hRzero ⟨hJR.subset hxJ, hdplane hx.1⟩
  obtain ⟨r, hr, hmin, hmax, hsigns, hrsub, hrsuper, g, hgT, hgn, hgr, hgW, hgU, hgtop,
      ε, hε, H, hglobal, hc, hci, hformula, hall⟩ :=
    hC.exists_pointed_cap_collar_isotopy_fixed_upper_with_global_finitePL_and_signs hupper hupperPL
      A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv W hW hWd hU hdU
  have hgR (x : E) (hx : x ∈ R) : g x = 0 :=
    hgW x (hWs.symm.subset (Or.inr (hJR.symm.subset hx)))
  have hfix (t : Icc (-ε) ε) (x : E) (hx : x ∈ R) : H t x = x := by
    rw [hformula, hgR x hx, mul_zero, zero_smul, add_zero]
  refine ⟨r, hr, hmin, hmax, hsigns, hrsub, hrsuper, g, hgT, hgn, hgr,
    fun x hx => hgW x (hWs.symm.subset (Or.inl hx)), hgR, hgU, hgtop,
    ε, hε, H, hglobal, hc, hci, hformula, fun t => ?_⟩
  obtain ⟨hHd, hHT, hball, hcaplevels, hinter, hlevels⟩ := hall t
  refine ⟨hfix t, hHd, hHT, hball, hcaplevels, hinter, fun c => ?_⟩
  obtain ⟨L, hL, hLp⟩ := hlevels c
  refine ⟨L, hL, ?_, hLp⟩
  intro x
  obtain ⟨p, hpbase, hpval, _, hphi⟩ := hLp x
  have hmem : H t (C p) ∈ R ↔ (C p : E) ∈ R := by
    constructor
    · intro hx
      have heq : H t (C p) = C p := (H t).injective (hfix t _ hx)
      exact heq ▸ hx
    · intro hx
      rwa [hfix t _ hx]
  rw [hpval, hmem, hresidual, hpbase]
  exact hphi.symm

theorem IsFinitePL.exists_pointed_cap_collar_isotopy_fixed_residual_with_global_finitePL
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
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a})) ∧
      ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
        EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ R, g x = 0) ∧
        (∀ x, x ∉ U → g x = 0) ∧
        (∀ x (hx : x ∈ B), g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0) ∧
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
            IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
            ((t : ℝ) ≠ 0 → ∀ a : ℝ, a ∈ Ioo 0 2 →
              IsFinitePLBallPair ℝ ((H t '' d) ∩ {x | A x = (t : ℝ) * a})
                ((H t '' b) ∩ {x | A x = (t : ℝ) * a})) ∧
            (∀ c : ℝ, ((H t '' d) ∩ {x | A x = c}) ∩
                ((H t '' T) ∩ {x | A x = c}) = (H t '' b) ∩ {x | A x = c}) ∧
            ∀ c : ℝ,
              ∃ L : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                  ((H t '' T) ∩ {x | A x = c} : Set E), L.IsFinitePL ∧
                (∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  (L x : E) ∈ R ↔ upper x = c) ∧
                ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                    ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                    (upper x = c ↔ (p : E × ℝ).2 = upper x) := by
  obtain ⟨r, hr, hmin, hmax, _, hrest⟩ :=
    hC.exists_pointed_cap_collar_isotopy_fixed_residual_with_global_finitePL_and_signs
      hupper hupperPL A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv
      Q hQ hQd J hJ hJR hRzero hresidual hU hdU
  exact ⟨r, hr, hmin, hmax, hrest⟩

theorem IsFinitePL.exists_pointed_cap_collar_isotopy_fixed_residual_with_rim_intervals
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
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a})) ∧
      ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
        EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ R, g x = 0) ∧
        (∀ x, x ∉ U → g x = 0) ∧
        (∀ x (hx : x ∈ B), g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
          Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
          Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
          (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
          ∀ t : Icc (-ε) ε,
            (∀ x ∈ R, H t x = x) ∧
            FinitePiecewiseAffineOn (H t : E → E) d ∧
            FinitePiecewiseAffineOn (H t : E → E) T ∧
            IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
            ((t : ℝ) ≠ 0 → ∀ a : ℝ, a ∈ Ioo 0 2 →
              IsFinitePLBallPair ℝ ((H t '' d) ∩ {x | A x = (t : ℝ) * a})
                ((H t '' b) ∩ {x | A x = (t : ℝ) * a})) ∧
            (∀ c : ℝ, ((H t '' d) ∩ {x | A x = c}) ∩
                ((H t '' T) ∩ {x | A x = c}) = (H t '' b) ∩ {x | A x = c}) ∧
            ∀ c : ℝ,
              ∃ L : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                  ((H t '' T) ∩ {x | A x = c} : Set E), L.IsFinitePL ∧
                (∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  (L x : E) ∈ R ↔ upper x = c) ∧
                ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                    ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                    (upper x = c ↔ (p : E × ℝ).2 = upper x) := by
  obtain ⟨r, hr, hmin, hmax, hrsub, hrsuper, g, hgT, hgn, hgr, hgQ, hgR, hgU, hgtop,
      ε, hε, H, _, hrest⟩ :=
    hC.exists_pointed_cap_collar_isotopy_fixed_residual_with_global_finitePL
      hupper hupperPL A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv
      Q hQ hQd J hJ hJR hRzero hresidual hU hdU
  exact ⟨r, hr, hmin, hmax, hrsub, hrsuper, g, hgT, hgn, hgr, hgQ, hgR, hgU, hgtop,
    ε, hε, H, hrest⟩

theorem IsFinitePL.exists_pointed_cap_collar_isotopy_fixed_residual
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
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
      ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
        EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ R, g x = 0) ∧
        (∀ x, x ∉ U → g x = 0) ∧
        (∀ x (hx : x ∈ B), g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
          Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
          Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
          (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
          ∀ t : Icc (-ε) ε,
            (∀ x ∈ R, H t x = x) ∧
            FinitePiecewiseAffineOn (H t : E → E) d ∧
            FinitePiecewiseAffineOn (H t : E → E) T ∧
            IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
            ((t : ℝ) ≠ 0 → ∀ a : ℝ, a ∈ Ioo 0 2 →
              IsFinitePLBallPair ℝ ((H t '' d) ∩ {x | A x = (t : ℝ) * a})
                ((H t '' b) ∩ {x | A x = (t : ℝ) * a})) ∧
            (∀ c : ℝ, ((H t '' d) ∩ {x | A x = c}) ∩
                ((H t '' T) ∩ {x | A x = c}) = (H t '' b) ∩ {x | A x = c}) ∧
            ∀ c : ℝ,
              ∃ L : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)} ≃ₜ
                  ((H t '' T) ∩ {x | A x = c} : Set E), L.IsFinitePL ∧
                (∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  (L x : E) ∈ R ↔ upper x = c) ∧
                ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                    ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                    (upper x = c ↔ (p : E × ℝ).2 = upper x) := by
  obtain ⟨r, hr, hmin, _, hrsub, _, hrest⟩ :=
    hC.exists_pointed_cap_collar_isotopy_fixed_residual_with_rim_intervals hupper hupperPL
      A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv Q hQ hQd
      J hJ hJR hRzero hresidual hU hdU
  exact ⟨r, hr, hmin, hrsub, hrest⟩

end Homeomorph
