import PoincareConjecture.Proofs.M76.Mathlib.PointedCapCollarIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.PointedCollarUpperBoundary
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem IsFinitePL.exists_pointed_cap_collar_isotopy_fixed_upper_with_global_finitePL_and_signs
    {B T d b U : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
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
    (hQd : d ∩ Q.space ⊆ {(q : E)}) (hU : IsOpen U) (hdU : d ⊆ U) :
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
        EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
        (∀ x (hx : x ∈ B), g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
          (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
            FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
          Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
          Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
          (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
          ∀ t : Icc (-ε) ε,
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
                ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                    ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                    (upper x = c ↔ (p : E × ℝ).2 = upper x) := by
  obtain ⟨u, J, _, _, hu, hJ, hJs, _, _, hJzero⟩ :=
    hC.exists_pointed_upperBoundary_complex hupperPL hupper A hheight hbottom hqB hqzero hpos
  obtain ⟨R, hR, hRs⟩ := Q.exists_finite_triangulation_union J hQ hJ
  have hRd : d ∩ R.space ⊆ {(q : E)} := by
    intro x hx
    rcases (show x ∈ Q.space ∪ J.space from hRs ▸ hx.2) with hxQ | hxJ
    · exact hQd ⟨hx.1, hxQ⟩
    · exact hJzero ▸ And.intro hxJ (hdplane hx.1)
  obtain ⟨f, hfval, r, hr, hmin, hmax, hsigns, hrsub, hrsuper, g, hgT, hgn, hgr, hgR, hgU,
      ε, hε, H, hglobal, hc, hci, hformula, hall⟩ :=
    hC.exists_pointed_cap_collar_isotopy_with_rim_intervals_global_finitePL_and_signs
      hupper A hheight hd hdplane
      q hcap v hv R hR hRd hU hdU
  have hgtop (x : E) (hx : x ∈ B) :
      g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0 := by
    apply hgR
    rw [hRs]
    exact Or.inr (hJs.symm ▸ (show
      (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩ : E) ∈ u '' B from ⟨x, hx, hu x hx⟩))
  have hgbottom (x : E) (hx : x ∈ B) : g (f (x, 0)) = g x := by
    have hfx : f (x, 0) = x :=
      (hfval ⟨(x, 0), hx, le_rfl, hupper x hx⟩).symm.trans (hbottom _ rfl)
    exact congrArg g hfx
  have hgfupper (x : E) (hx : x ∈ B) : g (f (x, upper x)) = 0 := by
    rw [← hfval ⟨(x, upper x), hx, hupper x hx, le_rfl⟩]
    exact hgtop x hx
  refine ⟨r, hr, hmin, hmax, hsigns, hrsub, hrsuper, g, hgT, hgn, hgr, ?_, hgU, hgtop,
    ε, hε, H, hglobal, hc, hci, hformula, fun t => ?_⟩
  · intro x hx
    exact hgR x (hRs.symm ▸ Or.inl hx)
  · obtain ⟨hHd, hHT, hball, hcaplevels, hinter, hlevels⟩ := hall t
    refine ⟨hHd, hHT, hball, hcaplevels, hinter, fun c => ?_⟩
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
    refine ⟨G, hL.setCongr hdomain rfl, fun x => ?_⟩
    obtain ⟨p, hpbase, hpval, hplo, hphi⟩ := hLp ⟨x, hdomain.symm ▸ x.property⟩
    refine ⟨p, hpbase, hpval, ?_, ?_⟩
    · simpa only [hgbottom x x.property.1] using hplo
    · simpa only [hgfupper x x.property.1, mul_zero, add_zero] using hphi




theorem IsFinitePL.exists_pointed_cap_collar_isotopy_fixed_upper_with_global_finitePL
    {B T d b U : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
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
    (hQd : d ∩ Q.space ⊆ {(q : E)}) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a})) ∧
      ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
        EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
        (∀ x (hx : x ∈ B), g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
          (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
            FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
          Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
          Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
          (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
          ∀ t : Icc (-ε) ε,
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
                ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                    ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                    (upper x = c ↔ (p : E × ℝ).2 = upper x) := by
  obtain ⟨r, hr, hmin, hmax, _, hrest⟩ :=
    hC.exists_pointed_cap_collar_isotopy_fixed_upper_with_global_finitePL_and_signs
      hupper hupperPL A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv
      Q hQ hQd hU hdU
  exact ⟨r, hr, hmin, hmax, hrest⟩




theorem IsFinitePL.exists_pointed_cap_collar_isotopy_fixed_upper_with_rim_intervals
    {B T d b U : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
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
    (hQd : d ∩ Q.space ⊆ {(q : E)}) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∃ p ∈ b, r p = 2 ∧ ∀ x ∈ d, r x = 2 ↔ x = p) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | a ≤ r x}) (b ∩ {x | r x = a})) ∧
      ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
        EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
        (∀ x (hx : x ∈ B), g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
          Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
          Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
          (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
          ∀ t : Icc (-ε) ε,
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
                ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                    ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                    (upper x = c ↔ (p : E × ℝ).2 = upper x) := by
  obtain ⟨r, hr, hmin, hmax, hrsub, hrsuper, g, hgT, hgn, hgr, hgQ, hgU, hgtop,
      ε, hε, H, _, hrest⟩ :=
    hC.exists_pointed_cap_collar_isotopy_fixed_upper_with_global_finitePL
      hupper hupperPL A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv
      Q hQ hQd hU hdU
  exact ⟨r, hr, hmin, hmax, hrsub, hrsuper, g, hgT, hgn, hgr, hgQ, hgU, hgtop,
    ε, hε, H, hrest⟩







theorem IsFinitePL.exists_pointed_cap_collar_isotopy_fixed_upper
    {B T d b U : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
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
    (hQd : d ∩ Q.space ⊆ {(q : E)}) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, r x ∈ Icc 0 2 ∧ (r x = 0 ↔ x = q)) ∧
      (∀ a : ℝ, a ∈ Ioo 0 2 →
        IsFinitePLBallPair ℝ (b ∩ {x | r x ≤ a}) (b ∩ {x | r x = a})) ∧
      ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
        EqOn g r d ∧ (∀ x ∈ Q.space, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
        (∀ x (hx : x ∈ B), g (C ⟨(x, upper x), hx, hupper x hx, le_rfl⟩) = 0) ∧
        ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
          Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
          Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
          (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
          ∀ t : Icc (-ε) ε,
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
                ∀ x : {x : E | x ∈ B ∧ c ∈ Icc ((t : ℝ) * g x) (upper x)},
                  ∃ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
                    (p : E × ℝ).1 = (x : E) ∧ (L x : E) = H t (C p) ∧
                    ((t : ℝ) * g x = c ↔ (p : E × ℝ).2 = 0) ∧
                    (upper x = c ↔ (p : E × ℝ).2 = upper x) := by
  obtain ⟨r, hr, hmin, _, hrsub, _, hrest⟩ :=
    hC.exists_pointed_cap_collar_isotopy_fixed_upper_with_rim_intervals hupper hupperPL
      A hheight hbottom hd hdplane q hqB hqzero hpos hcap v hv Q hQ hQd hU hdU
  exact ⟨r, hr, hmin, hrsub, hrest⟩

end Homeomorph
