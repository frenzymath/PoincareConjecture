import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Isotopy.UniformCappedCutIsotopy
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.SelectedCapNegativeSide
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.ProtectedCappedPolyhedron
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coverings.CappedSlabLevelCoverage
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.CappedSlabFinitePL
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.AffineSliceElimination

/-!
# A protected isotopy with whole capped-surface comparisons

The positive collar selects the negative protected carrier.
Support below the slab ceiling gives finite PL regularity of
the whole capped surface; exact slab coverage gives all its
positive-level comparisons. See Alexander 1924, pp. 7--8
and M76 derivation 240.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A selected positive collar supplies one supported isotopy
of its whole capped cut disk. The negative part, residual and
upper halfspace stay fixed; its whole zero section loses exactly
the cap except at the marked point, and all positive slab levels
compare to the original cut disk. See Alexander pp. 7--8 and
derivation 240.
The same ambient maps are PL on every finite polyhedron.
See M76 derivation 252. -/
theorem IsFinitePL.exists_protected_capped_surface_isotopy_with_global_finitePL
    {S B T d b U R s₀ s₁ : Set E} {upper : E → ℝ}
    (hupper : ∀ x ∈ B, 0 ≤ upper x) (hupperPL : FinitePiecewiseAffineOn upper B)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ) {β : ℝ} (hβ : 0 < β)
    (hslab : T ∪ R = S ∩ {x | A x ∈ Icc 0 β})
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hqB : (q : E) ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x) (hcap : d ∩ T = b)
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ b) (hs₁ : IsClosed s₁)
    (hsS : s₀ ⊆ S) (hdmeet : d ∩ s₀ ⊆ b)
    (hcover : T ⊆ s₀ ∪ s₁) (hinter : s₀ ∩ s₁ ⊆ b)
    (hbconn : IsConnected (b \ {(q : E)}))
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ b → (C p : E) ∈ s₀)
    (v : E) (hv : A.linear v = 1)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hB : B = b ∪ N.space) (hdN : d ∩ N.space ⊆ {(q : E)})
    (hzeros : (s₀ ∩ {x | A x = 0}) \ b ⊆ N.space)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {(q : E)})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
      (∀ (t : Icc (-ε) ε) (L : SimplicialComplex ℝ E), L.faces.Finite →
        FinitePiecewiseAffineOn (H t : E → E) L.space) ∧
      Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
      Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
      (∀ (t : Icc (-ε) ε) (x : E), (t : ℝ) = 0 → H t x = x) ∧
      ∀ t : Icc (-ε) ε,
        FinitePiecewiseAffineOn (H t : E → E) (s₀ ∪ d) ∧
        IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
        (∀ x ∈ R, H t x = x) ∧
        (∀ x ∈ (s₀ ∪ d) ∩ {x | A x < 0}, H t x = x) ∧
        (∀ x, x ∉ U → H t x = x) ∧ (∀ x, β ≤ A x → H t x = x) ∧
        ∀ _ht : 0 < (t : ℝ),
          (∀ x, A x ≤ A (H t x)) ∧
          ((H t '' (s₀ ∪ d)) ∩ {x | A x = 0} =
            (((s₀ ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {(q : E)})) ∧
          ∀ c ∈ Ioo (0 : ℝ) β,
            ∃ F : (s₀ ∩ {x | A x = c} : Set E) ≃ₜ
                ((H t '' (s₀ ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
              ∀ x : ((R ∩ s₀) ∩ {x | A x = c} : Set E),
                ∃ y : (s₀ ∩ {x | A x = c} : Set E), (y : E) = x ∧ (F y : E) = x := by
  have hbB : b ⊆ B := subset_union_left.trans hB.symm.subset
  have hbN : b ∩ N.space ⊆ {(q : E)} := fun _ hx => hdN ⟨hd.1 hx.1, hx.2⟩
  have hside := hs₀.cap_negative_side_of_positive_collar C hheight hbottom hbB hd.1
    A.continuous_of_finiteDimensional.continuousOn hdplane hdmeet q hbconn
    (N.isCompact_space_of_finite hN).isClosed hbN hzeros
    (fun x hx => hpos x (hbB hx)) hselected
  obtain ⟨Q, hQ, _, hdQ, hQneg, hQother⟩ :=
    hs₀.exists_protected_capped_polyhedron hd A q N hN hside hdN hzeros
  let V := U ∩ {x | A x < β}
  have hV : IsOpen V := hU.inter (isOpen_lt A.continuous_of_finiteDimensional continuous_const)
  have hdV : d ⊆ V := fun x hx =>
    ⟨hdU hx, by change A x < β; rwa [hdplane hx]⟩
  obtain ⟨g, _, hgn, hmin, hgQ, _, _, hgV, ε, hε, H, hglobal, hcont, hinv, hformula, hall⟩ :=
    hC.exists_uniform_capped_cut_isotopy_with_global_finitePL
      hupper hupperPL A hheight hbottom hd hdplane
      q hqB hqzero hpos hcap hs₀ hs₁ hcover hinter hselected v hv Q hQ hdQ
      N hN rfl hB hbN J hJ hJR hRzero hresidual hV hdV
  have hzeroFix (t : Icc (-ε) ε) (x : E) (hx : g x = 0) : H t x = x := by
    rw [hformula, hx, mul_zero, zero_smul, add_zero]
  have hQfix (t : Icc (-ε) ε) (x : E) (hx : x ∈ Q.space) : H t x = x :=
    hzeroFix t x (hgQ x hx)
  have hhigh (t : Icc (-ε) ε) (x : E) (hx : β ≤ A x) : H t x = x :=
    hzeroFix t x (hgV x (fun h => (not_lt_of_ge hx) h.2))
  refine ⟨ε, hε, H, hglobal, hcont, hinv, ?_, fun t => ?_⟩
  · intro t x ht
    rw [hformula, ht, zero_mul, zero_smul, add_zero]
  · obtain ⟨hfix, hHd, hHT, hball, hlevels⟩ := hall t
    have hneg (x : E) (hx : x ∈ (s₀ ∪ d) ∩ {x | A x < 0}) : H t x = x :=
      hQfix t x (hQneg hx)
    have hPL := hs₀.finitePiecewiseAffineOn_capped_of_slab hd A hsS hslab Q J hQ hJ
      hJR (fun x hx => hQneg ⟨Or.inl hx.1, hx.2⟩) (H t) hHd hHT (hQfix t) hfix (hhigh t)
    refine ⟨hPL, hball, hfix, hneg, ?_, hhigh t, fun ht => ?_⟩
    · intro x hx
      exact hzeroFix t x (hgV x (fun h => hx h.1))
    · have hraise (x : E) : A x ≤ A (H t x) := by
        rw [hformula, add_comm x]
        change A x ≤ A (((t : ℝ) * g x) • v +ᵥ x)
        rw [A.map_vadd, map_smul, hv]
        change A x ≤ (t : ℝ) * g x * 1 + A x
        simpa only [mul_one] using le_add_of_nonneg_left (mul_nonneg ht.le (hgn x))
      refine ⟨hraise, ?_, fun c hc => ?_⟩
      · exact A.image_zeroLevel_of_nonnegative_displacement subset_union_right hdplane q v hv g
          (fun x _ => hgn x) (fun x hx => (hmin x hx).2)
          (fun x hx hxA => hgQ x (hQneg ⟨hx, hxA⟩))
          (fun x hx hxA hxd => hgQ x (hQother ⟨⟨hx, hxA⟩, hxd⟩)) ht (H t)
          (fun x _ => hformula t x)
      · obtain ⟨F, hF, hFR⟩ := hlevels ht c hc.1
        have hsource := cut_slab_level_eq hsS hslab ⟨hc.1.le, hc.2.le⟩
        have htarget := image_capped_slab_level_eq (d := d) hsS hslab (H t)
          (fun x _ => hraise x) (fun x hx hxA => hneg x ⟨Or.inl hx, hxA⟩) hfix
          ⟨hc.1, hc.2.le⟩
        let G := (Homeomorph.setCongr hsource.symm).trans
          (F.trans (Homeomorph.setCongr htarget.symm))
        refine ⟨G, hF.setCongr hsource htarget.symm, fun x => ?_⟩
        exact ⟨⟨x, x.property.1.2, x.property.2⟩, rfl, hFR x⟩

/-- The original pointed-isotopy supplier with its exact prior
interface, projected from universal ambient PL control. See
Alexander pp. 7--8 and M76 derivation 252. -/
theorem IsFinitePL.exists_protected_capped_surface_isotopy
    {S B T d b U R s₀ s₁ : Set E} {upper : E → ℝ}
    (hupper : ∀ x ∈ B, 0 ≤ upper x) (hupperPL : FinitePiecewiseAffineOn upper B)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : E →ᵃ[ℝ] ℝ) {β : ℝ} (hβ : 0 < β)
    (hslab : T ∪ R = S ∩ {x | A x ∈ Icc 0 β})
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) (hdplane : d ⊆ {x | A x = 0})
    (q : b) (hqB : (q : E) ∈ B) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ B, x ≠ q → 0 < upper x) (hcap : d ∩ T = b)
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ b) (hs₁ : IsClosed s₁)
    (hsS : s₀ ⊆ S) (hdmeet : d ∩ s₀ ⊆ b)
    (hcover : T ⊆ s₀ ∪ s₁) (hinter : s₀ ∩ s₁ ⊆ b)
    (hbconn : IsConnected (b \ {(q : E)}))
    (hselected : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ b → (C p : E) ∈ s₀)
    (v : E) (hv : A.linear v = 1)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hB : B = b ∪ N.space) (hdN : d ∩ N.space ⊆ {(q : E)})
    (hzeros : (s₀ ∩ {x | A x = 0}) \ b ⊆ N.space)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hJR : J.space = R)
    (hRzero : R ∩ {x | A x = 0} ⊆ {(q : E)})
    (hresidual : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (C p : E) ∈ R ↔ (p : E × ℝ).2 = upper (p : E × ℝ).1)
    (hU : IsOpen U) (hdU : d ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
      Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
      Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
      (∀ (t : Icc (-ε) ε) (x : E), (t : ℝ) = 0 → H t x = x) ∧
      ∀ t : Icc (-ε) ε,
        FinitePiecewiseAffineOn (H t : E → E) (s₀ ∪ d) ∧
        IsFinitePLBallPair (ℝ × ℝ) (H t '' d) (H t '' b) ∧
        (∀ x ∈ R, H t x = x) ∧
        (∀ x ∈ (s₀ ∪ d) ∩ {x | A x < 0}, H t x = x) ∧
        (∀ x, x ∉ U → H t x = x) ∧ (∀ x, β ≤ A x → H t x = x) ∧
        ∀ _ht : 0 < (t : ℝ),
          (∀ x, A x ≤ A (H t x)) ∧
          ((H t '' (s₀ ∪ d)) ∩ {x | A x = 0} =
            (((s₀ ∪ d) ∩ {x | A x = 0}) \ d) ∪ (d ∩ {(q : E)})) ∧
          ∀ c ∈ Ioo (0 : ℝ) β,
            ∃ F : (s₀ ∩ {x | A x = c} : Set E) ≃ₜ
                ((H t '' (s₀ ∪ d)) ∩ {x | A x = c} : Set E), F.IsFinitePL ∧
              ∀ x : ((R ∩ s₀) ∩ {x | A x = c} : Set E),
                ∃ y : (s₀ ∩ {x | A x = c} : Set E), (y : E) = x ∧ (F y : E) = x := by
  obtain ⟨ε, hε, H, _, hrest⟩ :=
    hC.exists_protected_capped_surface_isotopy_with_global_finitePL
      hupper hupperPL A hβ hslab hheight hbottom hd hdplane q hqB hqzero hpos hcap
      hs₀ hs₁ hsS hdmeet hcover hinter hbconn hselected v hv
      N hN hB hdN hzeros J hJ hJR hRzero hresidual hU hdU
  exact ⟨ε, hε, H, hrest⟩

end Homeomorph
