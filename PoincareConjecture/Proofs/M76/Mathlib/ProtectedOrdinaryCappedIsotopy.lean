import PoincareConjecture.Proofs.M76.Mathlib.FixedResidualPositiveIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.ProtectedCappedPolyhedron
import PoincareConjecture.Proofs.M76.Mathlib.SelectedCapNegativeSide
import PoincareConjecture.Proofs.M76.Mathlib.TerminalCappedCutLevel
import PoincareConjecture.Proofs.M76.Mathlib.CappedSlabLevelCoverage
import PoincareConjecture.Proofs.M76.Mathlib.AffineSliceElimination
import PoincareConjecture.Proofs.M76.Mathlib.OrdinaryCappedCutLevel

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePL.exists_protected_ordinary_capped_isotopy
    {S B T d b U R s₀ s₁ : Set E} {upper : E → ℝ}
    (hupper : ∀ x ∈ B, 0 ≤ upper x)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ) {β : ℝ} (hβ : 0 < β)
    (hslab : T ∪ R = S ∩ {x | A x ∈ Icc 0 β})
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : E) (hqd : q ∉ d) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x) (hcap : d ∩ T = b)
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ b) (hs₁ : IsClosed s₁)
    (hsS : s₀ ⊆ S) (hdmeet : d ∩ s₀ ⊆ b)
    (hcover : T ⊆ s₀ ∪ s₁) (hinter : s₀ ∩ s₁ ⊆ b)
    (hbconn : IsConnected (b \ {q}))
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ b → (C p : E) ∈ s₀)
    (v : E) (hv : A.linear v = 1)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hB : B = b ∪ N.space) (hdN : d ∩ N.space ⊆ {q})
    (hzeros : (s₀ ∩ {x | A x = 0}) \ b ⊆ N.space)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {q})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ (r g : E → ℝ) (p : E), FinitePiecewiseAffineOn r d ∧
      p ∈ d \ b ∧ r p = 2 / 3 ∧
      (∀ x ∈ d, r x ∈ Icc (2 / 3) 1 ∧ (r x = 1 ↔ x ∈ b)) ∧
      (∀ x ∈ d, r x = 2 / 3 ↔ x = p) ∧
      EqOn g r d ∧ (∀ x ∈ N.space, g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          (∀ x ∈ R, H t x = x) ∧
          (∀ x ∈ (s₀ ∪ d) ∩ {x | A x < 0}, H t x = x) ∧
          (∀ x, x ∉ U → H t x = x) ∧ (∀ x, β ≤ A x → H t x = x) ∧
          IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
          ∀ _ht : 0 < (t : ℝ),
            (∀ x, A x ≤ A (H t x)) ∧
            (H t '' (s₀ ∪ d)) ∩ {x | A x = 0} =
              (((s₀ ∪ d) ∩ {x | A x = 0}) \ d) ∧
            (H t '' d) ∩ {x | A x = (t : ℝ) * (2 / 3)} = {H t p} ∧
            (∀ c : ℝ, c < (t : ℝ) * (2 / 3) ∨ (t : ℝ) < c →
              (H t '' d) ∩ {x | A x = c} = ∅) ∧
            (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
              IsFinitePLBallPair (ℝ × ℝ) ((H t '' d) ∩ {x | A x ≤ (t : ℝ) * a})
                ((H t '' d) ∩ {x | A x = (t : ℝ) * a})) ∧
            (∀ c ∈ Ioo (0 : ℝ) β, (t : ℝ) ≤ c →
              ∃ F : (s₀ ∩ {x | A x = c} : Set E) ≃ₜ
                  ((H t '' (s₀ ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
                ∀ x : ((R ∩ s₀) ∩ {x | A x = c} : Set E),
                  ∃ y : (s₀ ∩ {x | A x = c} : Set E), (y : E) = x ∧ (F y : E) = x) ∧
            ∀ c ∈ Ioo (0 : ℝ) β, c < (t : ℝ) → (∀ x ∈ b, c < upper x) →
              ∃ (f : E → E) (X Y : Set E),
                FinitePiecewiseAffineOn f {x | x ∈ B ∧ c ≤ upper x} ∧
                InjOn f {x | x ∈ B ∧ c ≤ upper x} ∧
                b ⊆ {x | x ∈ B ∧ c ≤ upper x} ∧
                s₀ ∩ {x | A x = c} = (f '' b) ∪ X ∧ Disjoint (f '' b) X ∧
                (H t '' (s₀ ∪ d)) ∩ {x | A x = c} =
                  ((H t '' d) ∩ {x | A x = c}) ∪ Y ∧
                Disjoint ((H t '' d) ∩ {x | A x = c}) Y ∧
                ∃ F : X ≃ₜ Y, F.IsFinitePL ∧
                  ∀ x : ((R ∩ s₀) ∩ {x | A x = c} : Set E),
                    ∃ y : X, (y : E) = x ∧ (F y : E) = x := by
  have hbB : b ⊆ B := subset_union_left.trans hB.symm.subset
  have hbN : b ∩ N.space ⊆ {q} := fun _ hx => hdN ⟨hd.1 hx.1, hx.2⟩
  have hside := hs₀.cap_negative_side_of_positive_collar C hheight hbottom hbB hd.1
    A.continuous_of_finiteDimensional.continuousOn hdplane hdmeet q hbconn
    (N.isCompact_space_of_finite hN).isClosed hbN hzeros
    (fun x hx => hpos x (hbB hx)) hselected
  obtain ⟨Q, hQ, hQs, hdQ, hQneg, hQother⟩ :=
    hs₀.exists_protected_capped_polyhedron hd A q N hN hside hdN hzeros
  have hQdis : Disjoint d Q.space := by
    apply disjoint_left.mpr
    intro x hxd hxQ
    have hxq : x = q := hdQ ⟨hxd, hxQ⟩
    exact hqd (hxq ▸ hxd)
  have hRdis : Disjoint d R := by
    apply disjoint_left.mpr
    intro x hxd hxR
    have hxq : x = q := hRzero ⟨hxR, hdplane hxd⟩
    exact hqd (hxq ▸ hxd)
  let V := U ∩ {x | A x < β}
  have hV : IsOpen V := hU.inter (isOpen_lt A.continuous_of_finiteDimensional continuous_const)
  have hdV : d ⊆ V := fun x hx =>
    ⟨hdU hx, by change A x < β; rwa [hdplane hx]⟩
  obtain ⟨r, p, hr, hp, hmin, hpmin, hpunique, g, _, hgn, hgr,
      hgQ, _, hgV, _, ε, hε, H, hglobal, hcont, hinv, hformula, hall⟩ :=
    hC.exists_positive_cap_collar_isotopy_fixed_residual hupper A hheight hbottom hd hdplane
      hcap v hv Q hQ hQdis J hJ hJR hRdis hresidual hV hdV
  have hgN (x : E) (hx : x ∈ N.space) : g x = 0 :=
    hgQ x (hQs.symm.subset (Or.inr hx))
  have hgb (x : E) (hx : x ∈ b) : g x = 1 :=
    (hgr (hd.1 hx)).trans ((hmin x (hd.1 hx)).2.mpr hx)
  have hgB (x : E) (hx : x ∈ B) : g x ≤ 1 := by
    rcases hB.subset hx with hxb | hxN
    · rw [hgr (hd.1 hxb), (hmin x (hd.1 hxb)).2.mpr hxb]
    · rw [hgN x hxN]
      norm_num
  have hzeroFix (t : Icc (-ε) ε) (x : E) (hx : g x = 0) : H t x = x := by
    rw [hformula, hx, mul_zero, zero_smul, add_zero]
  have hQfix (t : Icc (-ε) ε) (x : E) (hx : x ∈ Q.space) : H t x = x :=
    hzeroFix t x (hgQ x hx)
  have hhigh (t : Icc (-ε) ε) (x : E) (hx : β ≤ A x) : H t x = x :=
    hzeroFix t x (hgV x (fun h => (not_lt_of_ge hx) h.2))
  refine ⟨r, g, p, hr, hp, hpmin, hmin, hpunique, hgr, hgN,
    ε, hε, H, hglobal, hcont, hinv, hformula, fun t => ?_⟩
  obtain ⟨hfix, _, _, hcapheight, hball, hcaplevels, _, hlevels⟩ := hall t
  have hneg (x : E) (hx : x ∈ (s₀ ∪ d) ∩ {x | A x < 0}) : H t x = x :=
    hQfix t x (hQneg hx)
  refine ⟨hfix, hneg, fun x hx => hzeroFix t x (hgV x (fun h => hx h.1)),
    hhigh t, hball, fun ht => ?_⟩
  have hraise (x : E) : A x ≤ A (H t x) := by
    rw [hformula, add_comm x]
    change A x ≤ A (((t : ℝ) * g x) • v +ᵥ x)
    rw [A.map_vadd, map_smul, hv]
    change A x ≤ (t : ℝ) * g x * 1 + A x
    simpa only [mul_one] using le_add_of_nonneg_left (mul_nonneg ht.le (hgn x))
  refine ⟨hraise, ?_, (hcaplevels ht).2.1, (hcaplevels ht).1,
    (hcaplevels ht).2.2.2, ?_, ?_⟩
  · have hdzero (x : E) (hx : x ∈ d) : g x = 0 ↔ x = q := by
      rw [hgr hx]
      have hrpos : 0 < r x := (by norm_num : (0 : ℝ) < 2 / 3).trans_le (hmin x hx).1.1
      exact iff_of_false hrpos.ne' (fun hxq => hqd (hxq ▸ hx))
    have hzero := A.image_zeroLevel_of_nonnegative_displacement
      (S := s₀ ∪ d) subset_union_right hdplane q v hv g (fun x _ => hgn x) hdzero
      (fun x hx hxA => hgQ x (hQneg ⟨hx, hxA⟩))
      (fun x hx hxA hxd => hgQ x (hQother ⟨⟨hx, hxA⟩, hxd⟩)) ht (H t)
      (fun x _ => hformula t x)
    have hempty : d ∩ {q} = ∅ := eq_empty_iff_forall_notMem.mpr
      (fun x hx => hqd ((show x = q from hx.2) ▸ hx.1))
    simpa only [hempty, union_empty] using hzero
  · intro c hc htc
    obtain ⟨L, hL, hLres, hLp⟩ := hlevels c
    obtain ⟨F, hF, hFR⟩ := hC.exists_terminal_capped_cut_level A hheight hbottom
      hdplane hcap hresidual hs₀ hs₁ hcover hinter hselected (H t) hfix
      hB hbN hqzero hgN ht hc.1 (by simpa only [mul_one] using htc)
      (fun x hx => (hmin x hx).1.2) (fun x hx => (hmin x hx).2.mp)
      hgB hcapheight J hJ hJR hL hLres
      (fun x => by obtain ⟨p, hbase, hval, _, htop⟩ := hLp x; exact ⟨p, hbase, hval, htop⟩)
    have hsource := cut_slab_level_eq hsS hslab ⟨hc.1.le, hc.2.le⟩
    have htarget := image_capped_slab_level_eq (d := d) hsS hslab (H t)
      (fun x _ => hraise x) (fun x hx hxA => hneg x ⟨Or.inl hx, hxA⟩) hfix
      ⟨hc.1, hc.2.le⟩
    let G := (Homeomorph.setCongr hsource.symm).trans
      (F.trans (Homeomorph.setCongr htarget.symm))
    exact ⟨G, hF.setCongr hsource htarget.symm, fun x =>
      ⟨⟨x, x.property.1.2, x.property.2⟩, rfl, hFR x⟩⟩
  · intro c hc hct hroof
    obtain ⟨L, hL, hLres, hLp⟩ := hlevels c
    have hbk : Disjoint b N.space := by
      apply disjoint_left.mpr
      intro x hxb hxN
      exact hqd ((show x = q from hbN ⟨hxb, hxN⟩) ▸ hd.1 hxb)
    have hHb (x : E) (hx : x ∈ b) : A (H t x) = (t : ℝ) := by
      rw [hcapheight x (hd.1 hx), (hmin x (hd.1 hx)).2.mpr hx, mul_one]
    exact hC.exists_ordinary_capped_cut_level A hslab hsS hheight hbottom
      hcap hRdis hresidual hs₀ hs₁ hcover hinter (fun _ hx => hdplane (hd.1 hx))
      hselected (H t) hfix (fun x _ => hraise x)
      (fun x hx hxA => hneg x ⟨Or.inl hx, hxA⟩)
      hB hbk hgb hgN N hN rfl J hJ hJR ⟨hc.1, hc.2.le⟩ hct hroof hHb hL hLres
      (fun x => by obtain ⟨p, hbase, hval, _, htop⟩ := hLp x; exact ⟨p, hbase, hval, htop⟩)

end Homeomorph
