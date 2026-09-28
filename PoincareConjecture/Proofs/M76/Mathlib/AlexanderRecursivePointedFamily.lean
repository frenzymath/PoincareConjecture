import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveCollarSlab
import PoincareConjecture.Proofs.M76.Mathlib.UniformCappedCutIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.SelectedCapNegativeSide
import PoincareConjecture.Proofs.M76.Mathlib.ProtectedCappedPolyhedron
import PoincareConjecture.Proofs.M76.Mathlib.CappedSlabLevelCoverage
import PoincareConjecture.Proofs.M76.Mathlib.CappedSlabFinitePL
import PoincareConjecture.Proofs.M76.Mathlib.AffineSliceElimination
import PoincareConjecture.Proofs.M76.Mathlib.AllNonzeroCappedLevels










set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem AlexanderCollarSlab.exists_pointed_capped_family_with_signs
    {S s s' b d U : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsFinitePLBallPair (ℝ × ℝ) s b) (hs' : IsClosed s')
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (hqb : q ∈ b) (hunion : s ∪ s' = S) (hinter : s ∩ s' ⊆ b)
    (hcap : d ∩ S = b) (_hbconn : IsConnected (b \ {q}))
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hB : S ∩ {x | A x = 0} = b ∪ N.space) (hdN : d ∩ N.space ⊆ {q})
    (hside : d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    (v : E) (hv : A.linear v = 1) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ g : E → ℝ, FinitePiecewiseAffineOn g M.collar ∧
      (∀ x ∈ d, g x ≤ 2) ∧ (∀ x ∈ d, g x = 2 → x ∈ b) ∧
      (∀ x ∈ d,
        (0 < g x → x ∈ closure (d ∩ {y | g y < g x})) ∧
          (g x < 2 → x ∈ closure (d ∩ {y | g x < g y}))) ∧
      (∀ x ∈ N.space, g x = 0) ∧ g q = 0 ∧
      (∀ x ∈ M.residual, g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          FinitePiecewiseAffineOn (H t : E → E) (s ∪ d) ∧
          IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
          (∀ x ∈ M.residual, H t x = x) ∧
          (∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H t x = x) ∧
          (∀ x, x ∉ U → H t x = x) ∧
          (∀ x, β ≤ A x → H t x = x) ∧
          ∀ _ht : 0 < (t : ℝ),
            (∀ x, A x ≤ A (H t x)) ∧
            ((H t '' (s ∪ d)) ∩ {x | A x = 0} =
              (((s ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q})) ∧
            ∀ c : ℝ, c ≠ 0 →
              ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
                  ((H t '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
                ∀ x : ((M.residual ∩ s) ∩ {x | A x = c} : Set E),
                  ∃ y : (s ∩ {x | A x = c} : Set E), (y : E) = x ∧ (F y : E) = x := by
  have hbB : b ⊆ S ∩ {x | A x = 0} := subset_union_left.trans hB.symm.subset
  have hsS : s ⊆ S := subset_union_left.trans hunion.subset
  have hTS : M.collar ⊆ S :=
    (subset_union_left.trans M.cover.subset).trans inter_subset_left
  have hcapT : d ∩ M.collar = b := by
    apply Subset.antisymm
    · exact (inter_subset_inter_right _ hTS).trans hcap.subset
    · exact fun x hx => ⟨hd.1 hx, M.bottom_covered (hbB hx)⟩
  have hbN : b ∩ N.space ⊆ {q} := fun _ hx => hdN ⟨hd.1 hx.1, hx.2⟩
  have hzeros : (s ∩ {x | A x = 0}) \ b ⊆ N.space := by
    rintro x ⟨hx, hxnb⟩
    exact (hB.subset ⟨hsS hx.1, hx.2⟩).resolve_left hxnb
  obtain ⟨Q, hQ, _, hdQ, hQneg, hQother⟩ :=
    hs.exists_protected_capped_polyhedron hd A q N hN hside hdN hzeros
  let V := U ∩ {x | A x < β}
  have hV : IsOpen V := hU.inter (isOpen_lt A.continuous_of_finiteDimensional continuous_const)
  have hdV : d ⊆ V := fun x hx =>
    ⟨hdU hx, by change A x < β; rw [hdplane hx]; exact M.width_pos⟩
  obtain ⟨g, hg, hgn, hmin, hgmax, hgsigns, hgQ, hgN, hgR, hgV,
      ε, hε, H, hglobal, hcont, hinv, hformula, hall⟩ :=
    M.chart_finitePL.exists_uniform_capped_cut_isotopy_with_global_finitePL_and_signs
      (fun x hx => (M.upper_bounds x hx).1) M.upper_finitePL A M.height M.bottom
      hd hdplane ⟨q, hqb⟩ (hbB hqb) M.apex_upper M.upper_pos hcapT
      hs hs' (hTS.trans hunion.symm.subset) hinter hselected v hv Q hQ hdQ
      N hN rfl hB hbN M.residualComplex M.residual_finite M.residual_space
      M.residual_zero M.roof_contact hV hdV
  have hzeroFix (t : Icc (-ε) ε) (x : E) (hx : g x = 0) : H t x = x := by
    rw [hformula, hx, mul_zero, zero_smul, add_zero]
  have hQfix (t : Icc (-ε) ε) (x : E) (hx : x ∈ Q.space) : H t x = x :=
    hzeroFix t x (hgQ x hx)
  have hhigh (t : Icc (-ε) ε) (x : E) (hx : β ≤ A x) : H t x = x :=
    hzeroFix t x (hgV x (fun h => (not_lt_of_ge hx) h.2))
  have hgq : g q = 0 := (hmin q (hd.1 hqb)).2.mpr rfl
  refine ⟨g, hg, (fun x hx => (hmin x hx).1.2), hgmax, hgsigns, hgN, hgq, hgR,
    ε, hε, H, hglobal, hcont, hinv, hformula, fun t => ?_⟩
  obtain ⟨hfix, hHd, hHT, hball, hlevels⟩ := hall t
  have hneg (x : E) (hx : x ∈ (s ∪ d) ∩ {x | A x < 0}) : H t x = x :=
    hQfix t x (hQneg hx)
  have hPL := hs.finitePiecewiseAffineOn_capped_of_slab hd A hsS M.cover Q M.residualComplex
    hQ M.residual_finite M.residual_space
    (fun x hx => hQneg ⟨Or.inl hx.1, hx.2⟩)
    (H t) hHd hHT (hQfix t) hfix (hhigh t)
  refine ⟨hPL, hball, hfix, hneg, ?_, hhigh t, fun ht => ?_⟩
  · exact fun x hx => hzeroFix t x (hgV x (fun h => hx h.1))
  · have hraise (x : E) : A x ≤ A (H t x) := by
      rw [hformula, add_comm x]
      change A x ≤ A (((t : ℝ) * g x) • v +ᵥ x)
      rw [A.map_vadd, map_smul, hv]
      change A x ≤ (t : ℝ) * g x * 1 + A x
      simpa only [mul_one] using le_add_of_nonneg_left (mul_nonneg ht.le (hgn x))
    refine ⟨hraise, ?_, ?_⟩
    · exact A.image_zeroLevel_of_nonnegative_displacement subset_union_right hdplane q v hv g
        (fun x _ => hgn x) (fun x hx => (hmin x hx).2)
        (fun x hx hxA => hgQ x (hQneg ⟨hx, hxA⟩))
        (fun x hx hxA hxd => hgQ x (hQother ⟨⟨hx, hxA⟩, hxd⟩)) ht (H t)
        (fun x _ => hformula t x)
    · apply hs.exists_all_nonzero_capped_level_comparisons A hdplane (H t)
        hraise hneg (hhigh t)
      intro c hc
      obtain ⟨F, hF, hFR⟩ := hlevels ht c hc.1
      have hsource := cut_slab_level_eq hsS M.cover ⟨hc.1.le, hc.2.le⟩
      have htarget := image_capped_slab_level_eq (d := d) hsS M.cover (H t)
        (fun x _ => hraise x) (fun x hx hxA => hneg x ⟨Or.inl hx, hxA⟩) hfix
        ⟨hc.1, hc.2.le⟩
      let F' := (Homeomorph.setCongr hsource.symm).trans
        (F.trans (Homeomorph.setCongr htarget.symm))
      refine ⟨F', hF.setCongr hsource htarget.symm, fun x => ?_⟩
      exact ⟨⟨x, x.property.1.2, x.property.2⟩, rfl, hFR x⟩




theorem AlexanderCollarSlab.exists_pointed_capped_family
    {S s s' b d U : Set E} {A : E →ᵃ[ℝ] ℝ} {q : E} {β : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs : IsFinitePLBallPair (ℝ × ℝ) s b) (hs' : IsClosed s')
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (hqb : q ∈ b) (hunion : s ∪ s' = S) (hinter : s ∩ s' ⊆ b)
    (hcap : d ∩ S = b) (_hbconn : IsConnected (b \ {q}))
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hB : S ∩ {x | A x = 0} = b ∪ N.space) (hdN : d ∩ N.space ⊆ {q})
    (hside : d ∩ closure ((s ∪ d) ∩ {x | A x < 0}) ⊆ {q})
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ S ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (M.upper p.1)},
      (p : E × ℝ).1 ∈ b → (M.chart p : E) ∈ s)
    (v : E) (hv : A.linear v = 1) (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ g : E → ℝ, FinitePiecewiseAffineOn g M.collar ∧
      (∀ x ∈ N.space, g x = 0) ∧ g q = 0 ∧
      (∀ x ∈ M.residual, g x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) (x : E), H t x = x + ((t : ℝ) * g x) • v) ∧
        ∀ t : Icc (-ε) ε,
          FinitePiecewiseAffineOn (H t : E → E) (s ∪ d) ∧
          IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
          (∀ x ∈ M.residual, H t x = x) ∧
          (∀ x ∈ (s ∪ d) ∩ {x | A x < 0}, H t x = x) ∧
          (∀ x, x ∉ U → H t x = x) ∧
          (∀ x, β ≤ A x → H t x = x) ∧
          ∀ _ht : 0 < (t : ℝ),
            (∀ x, A x ≤ A (H t x)) ∧
            ((H t '' (s ∪ d)) ∩ {x | A x = 0} =
              (((s ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {q})) ∧
            ∀ c : ℝ, c ≠ 0 →
              ∃ F : (s ∩ {x | A x = c} : Set E) ≃ₜ
                  ((H t '' (s ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
                ∀ x : ((M.residual ∩ s) ∩ {x | A x = c} : Set E),
                  ∃ y : (s ∩ {x | A x = c} : Set E), (y : E) = x ∧ (F y : E) = x := by
  obtain ⟨g, hg, _, _, _, hrest⟩ :=
    M.exists_pointed_capped_family_with_signs hs hs' hd hdplane hqb hunion hinter hcap
      _hbconn N hN hB hdN hside hselected v hv hU hdU
  exact ⟨g, hg, hrest⟩

end Geometry
