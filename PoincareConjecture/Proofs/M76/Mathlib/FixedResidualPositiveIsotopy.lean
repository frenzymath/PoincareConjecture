import PoincareConjecture.Proofs.M76.Mathlib.PositiveCapCollarIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions










set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePL.exists_positive_cap_collar_isotopy_fixed_residual
    {B T d b U R : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (hcap : d ∩ T = b) (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite) (hQd : Disjoint d Q.space)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hdR : Disjoint d R)
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ (r : E → ℝ) (p : E), FinitePiecewiseAffineOn r d ∧ p ∈ d \ b ∧
      (∀ x ∈ d, r x ∈ Icc (2 / 3) 1 ∧ (r x = 1 ↔ x ∈ b)) ∧
      r p = 2 / 3 ∧ (∀ x ∈ d, r x = 2 / 3 ↔ x = p) ∧
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
            (∀ x ∈ d, A (H t x) = (t : ℝ) * r x) ∧
            IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
            (0 < (t : ℝ) →
              (∀ c : ℝ, c < (t : ℝ) * (2 / 3) ∨ (t : ℝ) < c →
                (H t '' d) ∩ {x | A x = c} = ∅) ∧
              (H t '' d) ∩ {x | A x = (t : ℝ) * (2 / 3)} = {H t p} ∧
              (H t '' d) ∩ {x | A x = (t : ℝ)} = H t '' b ∧
              ∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
                IsFinitePLBallPair (ℝ × ℝ) ((H t '' d) ∩ {x | A x ≤ (t : ℝ) * a})
                  ((H t '' d) ∩ {x | A x = (t : ℝ) * a})) ∧
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
  have hWd : Disjoint d W.space := by
    rw [hWs, hJR]
    exact hQd.union_right hdR
  obtain ⟨f, hfval, r, p, hr, hp, hmin, hpmin, hpunique, g, hgT, hgn, hgr,
      hgW, hgU, ε, hε, H, hglobal, hc, hci, hformula, hall⟩ :=
    hC.exists_positive_cap_collar_isotopy hupper A hheight hd hdplane hcap v hv W hW hWd hU hdU
  have hgR (x : E) (hx : x ∈ R) : g x = 0 :=
    hgW x (hWs.symm.subset (Or.inr (hJR.symm.subset hx)))
  have hfix (t : Icc (-ε) ε) (x : E) (hx : x ∈ R) : H t x = x := by
    rw [hformula, hgR x hx, mul_zero, zero_smul, add_zero]
  have hgtop (x : E) (hx : x ∈ B) :
      g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0 :=
    hgR _ ((hresidual _).mpr rfl)
  have hgbottom (x : E) (hx : x ∈ B) : g (f (x, 0)) = g x :=
    congrArg g ((hfval ⟨(x, 0), hx, le_rfl, hupper x hx⟩).symm.trans (hbottom _ rfl))
  have hgfupper (x : E) (hx : x ∈ B) : g (f (x, upper x)) = 0 := by
    rw [← hfval ⟨(x, upper x), hx, hupper x hx, le_rfl⟩]
    exact hgtop x hx
  refine ⟨r, p, hr, hp, hmin, hpmin, hpunique, g, hgT, hgn, hgr,
    fun x hx => hgW x (hWs.symm.subset (Or.inl hx)), hgR, hgU, hgtop,
    ε, hε, H, hglobal, hc, hci, hformula, fun t => ?_⟩
  obtain ⟨hHd, hHT, hcapheight, hball, hcaplevels, hinter, hlevels⟩ := hall t
  refine ⟨hfix t, hHd, hHT, hcapheight, hball, hcaplevels, hinter, fun c => ?_⟩
  obtain ⟨L, hL, hLp⟩ := hlevels c
  have hdomain : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g (f (x, 0)))
      (upper x + (t : ℝ) * g (f (x, upper x)))} =
      {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)} := by
    ext x
    by_cases hx : x ∈ B
    · simp only [mem_ofPred_eq, hx, true_and, hgbottom x hx, hgfupper x hx,
        mul_zero, add_zero]
    · simp only [mem_ofPred_eq, hx, false_and]
  let G := (Homeomorph.setCongr hdomain.symm).trans (L.trans (Homeomorph.setCongr rfl))
  have hGp (x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)}) :
      ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
        (p : E × ℝ).1 = (x : E) ∧ (G x : E) = H t (C p) ∧
        ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
        (upper x = c ↔ (p : E × ℝ).2 = upper x) := by
    obtain ⟨p, hpbase, hpval, hplo, hphi⟩ := hLp ⟨x, hdomain.symm ▸ x.property⟩
    exact ⟨p, hpbase, hpval, by simpa only [hgbottom x x.property.1] using hplo,
      by simpa only [hgfupper x x.property.1, mul_zero, add_zero] using hphi⟩
  refine ⟨G, hL.setCongr hdomain rfl, ?_, hGp⟩
  intro x
  obtain ⟨p, hpbase, hpval, _, hphi⟩ := hGp x
  have hmem : H t (C p) ∈ R ↔ (C p : E) ∈ R := by
    constructor
    · intro hx
      have heq : H t (C p) = C p := (H t).injective (hfix t _ hx)
      exact heq ▸ hx
    · intro hx
      rwa [hfix t _ hx]
  rw [hpval, hmem, hresidual, hpbase]
  exact hphi.symm

end Homeomorph
