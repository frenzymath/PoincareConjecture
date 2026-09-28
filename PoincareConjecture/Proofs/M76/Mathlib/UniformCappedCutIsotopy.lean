import PoincareConjecture.Proofs.M76.Mathlib.UniformPointedArcIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.PointedCappedCutLevel
import PoincareConjecture.Proofs.M76.Mathlib.TerminalCappedCutLevel











set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]










theorem IsFinitePL.exists_uniform_capped_cut_isotopy_with_global_finitePL_and_signs
    {B T d b k U R s₀ s₁ : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    (hupperPL : FinitePiecewiseAffineOn upper B)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hqB : (q : E) ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x) (hcap : d ∩ T = b)
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ b) (hs₁ : IsClosed s₁)
    (hcover : T ⊆ s₀ ∪ s₁) (hinter : s₀ ∩ s₁ ⊆ b)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ b → (C p : E) ∈ s₀)
    (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)})
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKk : K.space = k)
    (hB : B = b ∪ k) (htouch : b ∩ k ⊆ {(q : E)})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {(q : E)})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
      (∀ x ∈ d, g x ∈ Icc 0 2 ∧ (g x = 0 ↔ x = q)) ∧
      (∀ x ∈ d, g x = 2 → x ∈ b) ∧
      (∀ x ∈ d,
        (0 < g x → x ∈ closure (d ∩ {y | g y < g x})) ∧
          (g x < 2 → x ∈ closure (d ∩ {y | g x < g y}))) ∧
      (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ k, g x = 0) ∧
      (∀ x ∈ R, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
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
          ∀ _ht : 0 < (t : ℝ), ∀ c : ℝ, 0 < c →
            ∃ F : (((T ∩ s₀) ∪ (R ∩ s₀)) ∩ {x | A x = c} : Set E) ≃ₜ
                (((H t '' (d ∪ (T ∩ s₀))) ∪ (R ∩ s₀)) ∩ {x | A x = c} : Set E),
              F.IsFinitePL ∧ ∀ x : ((R ∩ s₀) ∩ {x | A x = c} : Set E),
                (F ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x := by
  have hkB : k ⊆ B := subset_union_right.trans hB.symm.subset
  have hdK : d ∩ K.space ⊆ {(q : E)} := by
    intro x hx
    have hxk : x ∈ k := hKk.subset hx.2
    let p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} :=
      ⟨(x, 0), hkB hxk, le_rfl, hupper x (hkB hxk)⟩
    have hCp : (C p : E) = x := hbottom p rfl
    exact htouch ⟨hcap.subset ⟨hx.1, hCp ▸ (C p).property⟩, hxk⟩
  obtain ⟨P, hP, hPs⟩ := Q.exists_finite_triangulation_union K hQ hK
  have hdP : d ∩ P.space ⊆ {(q : E)} := by
    intro x hx
    rcases hPs.subset hx.2 with hxQ | hxK
    · exact hQd ⟨hx.1, hxQ⟩
    · exact hdK ⟨hx.1, hxK⟩
  obtain ⟨r, g, _, hmin, hmax, hsigns, hgT, hgn, hgr, hgP, hgR, hgU,
      ε, hε, H, hglobal, hcont, hinv, hformula, hall⟩ :=
    hC.exists_uniform_pointed_arc_isotopy_with_charts_with_global_finitePL_and_signs
      hupper hupperPL A hheight hbottom
      hd hdplane q hqB hqzero hpos hcap v hv P hP hdP J hJ hJR hRzero hresidual hU hdU
  have hgQ (x : E) (hx : x ∈ Q.space) : g x = 0 :=
    hgP x (hPs.symm.subset (Or.inl hx))
  have hgk (x : E) (hx : x ∈ k) : g x = 0 :=
    hgP x (hPs.symm.subset (Or.inr (hKk.symm.subset hx)))
  have hgmin (x : E) (hx : x ∈ d) : g x ∈ Icc 0 2 ∧ (g x = 0 ↔ x = q) := by
    rw [hgr hx]
    exact hmin x hx
  have hgB (x : E) (hx : x ∈ B) : g x ≤ 2 := by
    rcases hB.subset hx with hxb | hxk
    · exact (hgmin x (hd.1 hxb)).1.2
    · rw [hgk x hxk]
      norm_num
  have hrmax (x : E) (hx : x ∈ d) (hrx : r x = 2) : x ∈ b := by
    obtain ⟨p, hpb, _, hp⟩ := hmax
    exact ((hp x hx).mp hrx).symm ▸ hpb
  have hgmax (x : E) (hx : x ∈ d) (h : g x = 2) : x ∈ b :=
    hrmax x hx (by simpa only [hgr hx] using h)
  have hgsigns (x : E) (hx : x ∈ d) :
      (0 < g x → x ∈ closure (d ∩ {y | g y < g x})) ∧
        (g x < 2 → x ∈ closure (d ∩ {y | g x < g y})) := by
    constructor
    · intro hpos
      have h := (hsigns x hx).1 (by simpa only [hgr hx] using hpos)
      apply closure_mono ?_ h
      rintro y ⟨hyd, hy⟩
      exact ⟨hyd, by simpa only [mem_ofPred_eq, hgr hyd, hgr hx] using hy⟩
    · intro hlt
      have h := (hsigns x hx).2 (by simpa only [hgr hx] using hlt)
      apply closure_mono ?_ h
      rintro y ⟨hyd, hy⟩
      exact ⟨hyd, by simpa only [mem_ofPred_eq, hgr hyd, hgr hx] using hy⟩
  refine ⟨g, hgT, hgn, hgmin, hgmax, hgsigns, hgQ, hgk, hgR, hgU,
    ε, hε, H, hglobal, hcont, hinv, hformula, fun t => ?_⟩
  obtain ⟨hfix, hHd, hHT, hcharts, hlevels⟩ := hall t
  refine ⟨hfix, hHd, hHT, hd.image hHd (H t).injective.injOn, fun ht c hc => ?_⟩
  by_cases hsmall : c < (t : ℝ) * 2
  · let a := c / (t : ℝ)
    have ha : a ∈ Ioo (0 : ℝ) 2 :=
      ⟨div_pos hc ht, (div_lt_iff₀ ht).mpr (by simpa only [mul_comm] using hsmall)⟩
    have hca : (t : ℝ) * a = c := by dsimp [a]; field_simp [ht.ne']
    obtain ⟨L, hL, hhigh, hwidth, hLres, hLp, f, hfval, _, hball, harcR, _, _⟩ :=
      hlevels ht a ha
    rw [← hca]
    exact hC.exists_pointed_capped_cut_level A hheight hbottom hdplane hcap hresidual
      hs₀ hs₁ hcover hinter hselected (H t) hfix hB htouch hqzero
      (fun x hx => hgr (hd.1 hx)) hgk K hK hKk J hJ hJR ht (mul_pos ht ha.1)
      hhigh hwidth hL hLres hLp hfval hball harcR
  · have hHheight (x : E) (hx : x ∈ d) : A (H t x) = (t : ℝ) * r x := by
      rw [hformula, hgr hx, add_comm x]
      change A (((t : ℝ) * r x) • v +ᵥ x) = (t : ℝ) * r x
      rw [A.map_vadd, map_smul, hv]
      change (t : ℝ) * r x * 1 + A x = (t : ℝ) * r x
      rw [hdplane hx, mul_one, add_zero]
    obtain ⟨L, hL, hLres, hLp⟩ := hcharts c
    exact hC.exists_terminal_capped_cut_level A hheight hbottom hdplane hcap hresidual
      hs₀ hs₁ hcover hinter hselected (H t) hfix hB htouch hqzero hgk
      ht hc (le_of_not_gt hsmall) (fun x hx => (hmin x hx).1.2) hrmax hgB hHheight
      J hJ hJR hL hLres (fun x => by
        obtain ⟨p, hbase, hval, _, htop⟩ := hLp x
        exact ⟨p, hbase, hval, htop⟩)




theorem IsFinitePL.exists_uniform_capped_cut_isotopy_with_global_finitePL
    {B T d b k U R s₀ s₁ : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    (hupperPL : FinitePiecewiseAffineOn upper B)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hqB : (q : E) ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x) (hcap : d ∩ T = b)
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ b) (hs₁ : IsClosed s₁)
    (hcover : T ⊆ s₀ ∪ s₁) (hinter : s₀ ∩ s₁ ⊆ b)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ b → (C p : E) ∈ s₀)
    (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)})
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKk : K.space = k)
    (hB : B = b ∪ k) (htouch : b ∩ k ⊆ {(q : E)})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {(q : E)})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
      (∀ x ∈ d, g x ∈ Icc 0 2 ∧ (g x = 0 ↔ x = q)) ∧
      (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ k, g x = 0) ∧
      (∀ x ∈ R, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
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
          ∀ _ht : 0 < (t : ℝ), ∀ c : ℝ, 0 < c →
            ∃ F : (((T ∩ s₀) ∪ (R ∩ s₀)) ∩ {x | A x = c} : Set E) ≃ₜ
                (((H t '' (d ∪ (T ∩ s₀))) ∪ (R ∩ s₀)) ∩ {x | A x = c} : Set E),
              F.IsFinitePL ∧ ∀ x : ((R ∩ s₀) ∩ {x | A x = c} : Set E),
                (F ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x := by
  obtain ⟨g, hgT, hgn, hmin, _, _, hrest⟩ :=
    hC.exists_uniform_capped_cut_isotopy_with_global_finitePL_and_signs hupper hupperPL
      A hheight hbottom hd hdplane q hqB hqzero hpos hcap hs₀ hs₁ hcover hinter
      hselected v hv Q hQ hQd K hK hKk hB htouch J hJ hJR hRzero hresidual hU hdU
  exact ⟨g, hgT, hgn, hmin, hrest⟩




theorem IsFinitePL.exists_uniform_capped_cut_isotopy
    {B T d b k U R s₀ s₁ : Set E} {upper : E → ℝ} (hupper : ∀ x ∈ B, 0 ≤ upper x)
    (hupperPL : FinitePiecewiseAffineOn upper B)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hqB : (q : E) ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x) (hcap : d ∩ T = b)
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ b) (hs₁ : IsClosed s₁)
    (hcover : T ⊆ s₀ ∪ s₁) (hinter : s₀ ∩ s₁ ⊆ b)
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ b → (C p : E) ∈ s₀)
    (v : E) (hv : A.linear v = 1)
    (Q : SimplicialComplex ℝ E) (hQ : Q.faces.Finite)
    (hQd : d ∩ Q.space ⊆ {(q : E)})
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKk : K.space = k)
    (hB : B = b ∪ k) (htouch : b ∩ k ⊆ {(q : E)})
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {(q : E)})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ g : E → ℝ, FinitePiecewiseAffineOn g T ∧ (∀ x, 0 ≤ g x) ∧
      (∀ x ∈ d, g x ∈ Icc 0 2 ∧ (g x = 0 ↔ x = q)) ∧
      (∀ x ∈ Q.space, g x = 0) ∧ (∀ x ∈ k, g x = 0) ∧
      (∀ x ∈ R, g x = 0) ∧ (∀ x, x ∉ U → g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          (∀ x ∈ R, H t x = x) ∧
          FinitePiecewiseAffineOn (H t : E → E) d ∧
          FinitePiecewiseAffineOn (H t : E → E) T ∧
          IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
          ∀ _ht : 0 < (t : ℝ), ∀ c : ℝ, 0 < c →
            ∃ F : (((T ∩ s₀) ∪ (R ∩ s₀)) ∩ {x | A x = c} : Set E) ≃ₜ
                (((H t '' (d ∪ (T ∩ s₀))) ∪ (R ∩ s₀)) ∩ {x | A x = c} : Set E),
              F.IsFinitePL ∧ ∀ x : ((R ∩ s₀) ∩ {x | A x = c} : Set E),
                (F ⟨x, ⟨Or.inr x.property.1, x.property.2⟩⟩ : E) = x := by
  obtain ⟨g, hgT, hgn, hmin, hgQ, hgk, hgR, hgU, ε, hε, H, _, hrest⟩ :=
    hC.exists_uniform_capped_cut_isotopy_with_global_finitePL hupper hupperPL
      A hheight hbottom hd hdplane q hqB hqzero hpos hcap hs₀ hs₁ hcover hinter
      hselected v hv Q hQ hQd K hK hKk hB htouch J hJ hJR hRzero hresidual hU hdU
  exact ⟨g, hgT, hgn, hmin, hgQ, hgk, hgR, hgU, ε, hε, H, hrest⟩

end Homeomorph
