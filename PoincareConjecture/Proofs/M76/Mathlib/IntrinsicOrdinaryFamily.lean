import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCutSide
import PoincareConjecture.Proofs.M76.Mathlib.ProtectedOrdinaryCappedIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.OrdinaryCappedLevelComparisons
import PoincareConjecture.Proofs.M76.Mathlib.DirectionalScalarRecovery










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem AlexanderCollarSlab.exists_ordinary_capped_family_with_rim_scalar
    {S s s' d U : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hqd : q ∉ d)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hs : IsFinitePLBallPair (ℝ × ℝ) s (P.boundary ℝ)) (hs' : IsClosed s')
    (hunion : s ∪ s' = S) (hinter : s ∩ s' ⊆ P.boundary ℝ)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ S = P.boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : S ∩ {x | A x = 0} = P.boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ P.boundary ℝ → (M.chart p : E) ∈ s)
    (v : E) (hv : A.linear v = 1) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ g : E → ℝ, FinitePiecewiseAffineOn g M.collar ∧
      (∀ x ∈ N.space, g x = 0) ∧ (∀ x ∈ M.residual, g x = 0) ∧
      (∀ x ∈ P.boundary ℝ, g x = 1) ∧
      ∃ p : E, p ∈ d \ P.boundary ℝ ∧
      ∃ ε : ℝ, ε ∈ Ioo 0 β ∧ (∀ x ∈ P.boundary ℝ, ε < M.upper x) ∧
        ∃ H : Icc (-ε) ε → E ≃ₜ E,
        (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
        Continuous (fun z : Icc (-ε) ε × E => H z.1 z.2) ∧
        Continuous (fun z : Icc (-ε) ε × E => (H z.1).symm z.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          (∀ x ∈ M.residual, H t x = x) ∧
          (∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H t x = x) ∧
          (∀ x, x ∉ U → H t x = x) ∧ (∀ x, β ≤ A x → H t x = x) ∧
          IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' P.boundary ℝ) ∧
          ∀ _ht : 0 < (t : ℝ),
            (∀ x, A x ≤ A (H t x)) ∧
            (H t '' (s ∪ d)) ∩ {x | A x = 0} = (((s ∪ d) ∩ {x | A x = 0}) \ d) ∧
            (H t '' d) ∩ {x | A x = (t : ℝ) * (2 / 3)} = {H t p} ∧
            (∀ c : ℝ, c < (t : ℝ) * (2 / 3) ∨ (t : ℝ) < c →
              (H t '' d) ∩ {x | A x = c} = ∅) ∧
            (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
              IsFinitePLBallPair (ℝ × ℝ) ((H t '' d) ∩ {x | A x ≤ (t : ℝ) * a})
                ((H t '' d) ∩ {x | A x = (t : ℝ) * a})) ∧
            (∀ c : ℝ, c < 0 ∨ (t : ℝ) ≤ c →
              ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
                ((H t '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL) ∧
            ∀ c ∈ Ioo (0 : ℝ) (t : ℝ),
              ∃ (Z : Set E) (f : E → E) (X Y : Set E),
                FinitePiecewiseAffineOn f Z ∧ InjOn f Z ∧ P.boundary ℝ ⊆ Z ∧
                s ∩ {x | A x = c} = (f '' P.boundary ℝ) ∪ X ∧
                Disjoint (f '' P.boundary ℝ) X ∧
                (H t '' (s ∪ d)) ∩ {x | A x = c} =
                  ((H t '' d) ∩ {x | A x = c}) ∪ Y ∧
                Disjoint ((H t '' d) ∩ {x | A x = c}) Y ∧
                ∃ F : X ≃ₜ Y, F.IsFinitePL := by
  have hP : P.boundary ℝ ⊆ S ∩ {x | A x = 0} :=
    subset_union_left.trans hsection.symm.subset
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  have hTS : M.collar ⊆ S :=
    (subset_union_left.trans M.cover.subset).trans inter_subset_left
  have hcapT : d ∩ M.collar = P.boundary ℝ := by
    apply Subset.antisymm
    · exact (inter_subset_inter_right _ hTS).trans hcap.subset
    · exact fun _ hx => ⟨hd.1 hx, M.bottom_covered (hP hx)⟩
  have hdmeet : d ∩ s ⊆ P.boundary ℝ :=
    (inter_subset_inter_right _ hsS).trans hcap.subset
  have hzeros : (s ∩ {x | A x = 0}) \ P.boundary ℝ ⊆ N.space := by
    rintro x ⟨hx, hxnb⟩
    exact (hsection.subset ⟨hsS hx.1, hx.2⟩).resolve_left hxnb
  obtain ⟨ec⟩ := P.nonempty_boundary_homeomorph_circle hPe hPi
  have hbconn := isConnected_sdiff_singleton_of_homeomorph_circle (P.boundary ℝ) ec q
  obtain ⟨r, g, p, _, hp, _, hmin, _, hgr, hgN, ε₀, hε₀, H₀,
      hglobal, hcont, hinv, hformula, hall⟩ :=
    M.chart_finitePL.exists_protected_ordinary_capped_isotopy
      (fun x hx => (M.upper_bounds x hx).1) A M.width_pos M.cover M.height M.bottom
      hd hdplane q hqd M.apex_upper M.upper_pos hcapT hs hs'
      hsS hdmeet (hTS.trans hunion.symm.subset) hinter hbconn hselected v hv
      N hN hsection hdN hzeros M.residualComplex M.residual_finite M.residual_space
      M.residual_zero M.roof_contact hU hdU
  have hgb (x : E) (hx : x ∈ P.boundary ℝ) : g x = 1 :=
    (hgr (hd.1 hx)).trans ((hmin x (hd.1 hx)).2.mpr hx)
  let t₀ : Icc (-ε₀) ε₀ := ⟨ε₀, (neg_le_self hε₀.le), le_rfl⟩
  have hgR (x : E) (hx : x ∈ M.residual) : g x = 0 :=
    A.directional_scalar_eq_zero_of_fixed hv hε₀.ne'
      ((hformula t₀ x).symm.trans ((hall t₀).1 x hx))
  have hg : FinitePiecewiseAffineOn g M.collar := by
    obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := M.chart_finitePL.symm
    have hHt : FinitePiecewiseAffineOn (H₀ t₀ : E → E) M.collar :=
      hKs ▸ hglobal t₀ K hK
    exact hHt.directional_scalar A hv hε₀.ne' (fun x _ => hformula t₀ x)
  obtain ⟨η, hη, hηroof⟩ := P.isCompact_boundary.exists_forall_le'
    (M.upper_finitePL.continuousOn.mono hP)
    (fun x hx => M.upper_pos x (hP hx) (fun hxq => hqd (hxq ▸ hd.1 hx)))
  let ε := min ε₀ (min η β) / 2
  have hsmall : 0 < min ε₀ (min η β) := lt_min hε₀ (lt_min hη M.width_pos)
  have hε : 0 < ε := half_pos hsmall
  have hεsmall : ε < min ε₀ (min η β) := half_lt_self hsmall
  have hεold : ε < ε₀ := hεsmall.trans_le (min_le_left _ _)
  have hεη : ε < η := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεβ : ε < β := hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let embed : Icc (-ε) ε → Icc (-ε₀) ε₀ := fun t =>
    ⟨t, (neg_le_neg hεold.le).trans t.property.1, t.property.2.trans hεold.le⟩
  have hembed : Continuous embed := continuous_subtype_val.subtype_mk _
  let H : Icc (-ε) ε → E ≃ₜ E := fun t => H₀ (embed t)
  refine ⟨g, hg, hgN, hgR, hgb, p, hp, ε, ⟨hε, hεβ⟩,
    (fun x hx => hεη.trans_le (hηroof x hx)), H,
    (fun t L hL => hglobal (embed t) L hL), ?_, ?_,
    (fun t x => hformula (embed t) x), fun t => ?_⟩
  · exact hcont.comp ((hembed.comp continuous_fst).prodMk continuous_snd)
  · exact hinv.comp ((hembed.comp continuous_fst).prodMk continuous_snd)
  · obtain ⟨hres, hnegative, hfix, hhigh, hball, hpositive⟩ := hall (embed t)
    refine ⟨hres, hnegative, hfix, hhigh, hball, fun ht => ?_⟩
    obtain ⟨hraise, hzero, hminimum, hempty, hdisks, hterminal, hlow⟩ := hpositive ht
    refine ⟨hraise, hzero, hminimum, hempty, hdisks, ?_, ?_⟩
    · apply hs.exists_ordinary_terminal_level_comparisons A hdplane ht (H t)
        hraise hnegative hhigh
      intro c hc htc
      obtain ⟨F, hF, _⟩ := hterminal c hc htc
      exact ⟨F, hF⟩
    · intro c hc
      obtain ⟨f, X, Y, hf, hinj, hb, hsrc, hsep, htgt, hcapSep, F, hF, _⟩ :=
        hlow c ⟨hc.1, hc.2.trans (t.property.2.trans_lt hεβ)⟩ hc.2
          (fun x hx => hc.2.trans ((t.property.2.trans_lt hεη).trans_le (hηroof x hx)))
      exact ⟨_, f, X, Y, hf, hinj, hb, hsrc, hsep, htgt, hcapSep, F, hF⟩




theorem AlexanderCollarSlab.exists_ordinary_capped_family
    {S s s' d U : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    {n : ℕ} (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hqd : q ∉ d)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ))
    (hs : IsFinitePLBallPair (ℝ × ℝ) s (P.boundary ℝ)) (hs' : IsClosed s')
    (hunion : s ∪ s' = S) (hinter : s ∩ s' ⊆ P.boundary ℝ)
    (hdplane : d ⊆ {x | A x = 0}) (hcap : d ∩ S = P.boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : S ∩ {x | A x = 0} = P.boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ P.boundary ℝ → (M.chart p : E) ∈ s)
    (v : E) (hv : A.linear v = 1) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ g : E → ℝ, FinitePiecewiseAffineOn g M.collar ∧
      (∀ x ∈ N.space, g x = 0) ∧ (∀ x ∈ M.residual, g x = 0) ∧
      ∃ p : E, p ∈ d \ P.boundary ℝ ∧
      ∃ ε : ℝ, ε ∈ Ioo 0 β ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
        Continuous (fun z : Icc (-ε) ε × E => H z.1 z.2) ∧
        Continuous (fun z : Icc (-ε) ε × E => (H z.1).symm z.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          (∀ x ∈ M.residual, H t x = x) ∧
          (∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H t x = x) ∧
          (∀ x, x ∉ U → H t x = x) ∧ (∀ x, β ≤ A x → H t x = x) ∧
          IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' P.boundary ℝ) ∧
          ∀ _ht : 0 < (t : ℝ),
            (∀ x, A x ≤ A (H t x)) ∧
            (H t '' (s ∪ d)) ∩ {x | A x = 0} = (((s ∪ d) ∩ {x | A x = 0}) \ d) ∧
            (H t '' d) ∩ {x | A x = (t : ℝ) * (2 / 3)} = {H t p} ∧
            (∀ c : ℝ, c < (t : ℝ) * (2 / 3) ∨ (t : ℝ) < c →
              (H t '' d) ∩ {x | A x = c} = ∅) ∧
            (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
              IsFinitePLBallPair (ℝ × ℝ) ((H t '' d) ∩ {x | A x ≤ (t : ℝ) * a})
                ((H t '' d) ∩ {x | A x = (t : ℝ) * a})) ∧
            (∀ c : ℝ, c < 0 ∨ (t : ℝ) ≤ c →
              ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
                ((H t '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL) ∧
            ∀ c ∈ Ioo (0 : ℝ) (t : ℝ),
              ∃ (Z : Set E) (f : E → E) (X Y : Set E),
                FinitePiecewiseAffineOn f Z ∧ InjOn f Z ∧ P.boundary ℝ ⊆ Z ∧
                s ∩ {x | A x = c} = (f '' P.boundary ℝ) ∪ X ∧
                Disjoint (f '' P.boundary ℝ) X ∧
                (H t '' (s ∪ d)) ∩ {x | A x = c} =
                  ((H t '' d) ∩ {x | A x = c}) ∪ Y ∧
                Disjoint ((H t '' d) ∩ {x | A x = c}) Y ∧
                ∃ F : X ≃ₜ Y, F.IsFinitePL := by
  obtain ⟨g, hg, hgN, hgR, _, p, hp, ε, hε, _, H, hglobal, hcont, hinv, hformula,
      hall⟩ := M.exists_ordinary_capped_family_with_rim_scalar P hPe hPi hqd hd hs hs'
    hunion hinter hdplane hcap N hN hsection hdN hselected v hv hU hdU
  exact ⟨g, hg, hgN, hgR, p, hp, ε, hε, H, hglobal, hcont, hinv, hformula, hall⟩

end Geometry
