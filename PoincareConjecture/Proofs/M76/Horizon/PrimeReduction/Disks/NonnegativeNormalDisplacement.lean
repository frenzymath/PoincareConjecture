import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.SmallSupportedPLIsotopy
import PoincareConjecture.Proofs.M76.Mathlib.ConvexPolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarShear
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76




theorem exists_nonnegative_normal_displacement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T P : SimplicialComplex ℝ E) (hT : T.faces.Finite) (hP : P.faces.Finite)
    (hTP : T.space ⊆ P.space) {U : Set E} (hU : IsOpen U) (hTU : T.space ⊆ U)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) :
    ∃ (v : E) (ρ : E → ℝ) (K : SimplicialComplex ℝ E),
      A.linear v = 1 ∧ K.faces.Finite ∧ Convex ℝ K.space ∧ P.space ⊆ interior K.space ∧
      FinitePiecewiseAffineOn ρ K.space ∧ (∀ x, 0 ≤ ρ x) ∧
      (∀ x ∈ T.space, ρ x = 1) ∧ (∀ x, x ∉ U → ρ x = 0) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ H : Icc (-ε) ε → E ≃ₜ E,
        Continuous (fun p : Icc (-ε) ε × E => H p.1 p.2) ∧
        Continuous (fun p : Icc (-ε) ε × E => (H p.1).symm p.2) ∧
        (∀ (t : Icc (-ε) ε) x, H t x = x + ((t : ℝ) * ρ x) • v) ∧
        (∀ (t : Icc (-ε) ε) x, A (H t x) = A x + (t : ℝ) * ρ x) ∧
        (∀ (t : Icc (-ε) ε) x, x ∉ U → H t x = x) ∧
        ∀ t : Icc (-ε) ε, (∀ x, x ∉ interior K.space → H t x = x) ∧
          H t '' K.space = K.space ∧
          ∃ e : K.space ≃ₜ K.space, e.IsFinitePL ∧ ∀ x : K.space, (e x : E) = H t x := by
  classical
  obtain ⟨v, hv⟩ := LinearMap.surjective hA (1 : ℝ)
  obtain ⟨K, hK, hcv, hPK⟩ := (P.isCompact_space_of_finite hP).exists_finite_convex_neighborhood
  have hone : FinitePiecewiseAffineOn (fun _ : E => (1 : ℝ)) T.space :=
    (T.affineOnFaces_affine (ContinuousAffineMap.const ℝ E 1)).finitePiecewiseAffineOn hT
  obtain ⟨g, hg, hgT, hgzero, hgoutside⟩ := hone.exists_supported_extension K hK
    (hTP.trans (hPK.trans interior_subset)) (hU.inter isOpen_interior)
    (subset_inter hTU (hTP.trans hPK))
  let ρ : E → ℝ := fun x => max (g x) 0
  have hzero : FinitePiecewiseAffineOn (fun _ : E => (0 : ℝ)) K.space :=
    (K.affineOnFaces_affine (ContinuousAffineMap.const ℝ E 0)).finitePiecewiseAffineOn hK
  have hρ : FinitePiecewiseAffineOn ρ K.space := hg.max hzero
  have hρoutside (x : E) (hx : x ∉ K.space) : ρ x = 0 := by
    simp only [ρ, hgoutside x hx, max_self]
  have hρzero (x : E) (hx : x ∉ U ∩ interior K.space) : ρ x = 0 := by
    simp only [ρ, hgzero x hx, max_self]
  let f : E → E := fun x => ρ x • v
  let B : ℝ →ᴬ[ℝ] E := ((ContinuousLinearMap.id ℝ ℝ).smulRight v).toContinuousAffineMap
  have hf : FinitePiecewiseAffineOn f K.space := hρ.postcomp B
  have hfront (x : E) (hx : x ∈ frontier K.space) : f x = 0 := by
    change ρ x • v = 0
    rw [hρzero x (fun h => hx.2 h.2), zero_smul]
  obtain ⟨ε, hε, H, hc, hci, hformula, hrest⟩ :=
    hf.exists_small_supported_isotopy hcv hfront
  have hformula' (t : Icc (-ε) ε) (x : E) : H t x = x + ((t : ℝ) * ρ x) • v := by
    rw [hformula]
    by_cases hx : x ∈ K.space
    · rw [indicator_of_mem hx]
      exact congrArg (x + ·) (smul_smul (t : ℝ) (ρ x) v)
    · rw [indicator_of_notMem hx, hρoutside x hx, mul_zero, smul_zero, zero_smul]
  refine ⟨v, ρ, K, hv, hK, hcv, hPK, hρ, fun x => le_max_right _ _, ?_, ?_,
    ε, hε, H, hc, hci, hformula', ?_, ?_, hrest⟩
  · intro x hx
    simp only [ρ, hgT hx, max_eq_left zero_le_one]
  · intro x hx
    exact hρzero x (fun h => hx h.1)
  · intro t x
    rw [hformula', add_comm x]
    change A (((t : ℝ) * ρ x) • v +ᵥ x) = _
    rw [A.map_vadd, map_smul, hv]
    change (t : ℝ) * ρ x * 1 + A x = A x + (t : ℝ) * ρ x
    ring
  · intro t x hx
    rw [hformula', hρzero x (fun h => hx h.1), mul_zero, zero_smul, add_zero]




theorem exists_separated_normal_cap_pair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (T P : SimplicialComplex ℝ E) (hT : T.faces.Finite) (hP : P.faces.Finite)
    (hTP : T.space ⊆ P.space) {U : Set E} (hU : IsOpen U) (hTU : T.space ⊆ U)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (R r : Bool → Set E)
    (hR : ∀ b, IsFinitePLBallPair (ℝ × ℝ) (R b) (r b))
    (hRP : ∀ b, R b ⊆ P.space) (hboundary : ∀ b, Disjoint (r b) U)
    (hpositive : ∀ x ∈ R true, 0 ≤ A x) (hnegative : ∀ x ∈ R false, A x ≤ 0)
    (hplanar : ∀ b x, x ∈ R b → A x = 0 → x ∈ T.space) :
    ∃ F : Bool → E ≃ₜ E,
      (∀ b, (∀ x, x ∉ U → F b x = x) ∧
        EqOn (F b) id (r b) ∧ IsFinitePLBallPair (ℝ × ℝ) (F b '' R b) (r b) ∧
        ∀ x ∈ R b, if b then 0 < A (F b x) else A (F b x) < 0) ∧
      Disjoint (F true '' R true) (F false '' R false) := by
  classical
  obtain ⟨v, ρ, K, hv, hK, hcv, hPK, hρ, hρnonneg, hρT, hρzero,
    ε, hε, H, hc, hci, hformula, hheight, hfix, hrest⟩ :=
    exists_nonnegative_normal_displacement T P hT hP hTP hU hTU A hA
  let t : Bool → Icc (-ε) ε := fun b =>
    if b then ⟨ε, by constructor <;> linarith⟩ else ⟨-ε, by constructor <;> linarith⟩
  let F : Bool → E ≃ₜ E := fun b => H (t b)
  have hsign (b : Bool) (x : E) (hx : x ∈ R b) :
      if b then 0 < A (F b x) else A (F b x) < 0 := by
    change if b then 0 < A (H (t b) x) else A (H (t b) x) < 0
    rw [hheight]
    cases b
    · change A x + -ε * ρ x < 0
      by_cases hz : A x = 0
      · rw [hz, hρT x (hplanar false x hx hz)]
        linarith
      · have hneg : A x < 0 := lt_of_le_of_ne (hnegative x hx) hz
        have hprod : 0 ≤ ε * ρ x := mul_nonneg hε.le (hρnonneg x)
        nlinarith
    · change 0 < A x + ε * ρ x
      by_cases hz : A x = 0
      · rw [hz, hρT x (hplanar true x hx hz)]
        linarith
      · have hpos : 0 < A x := lt_of_le_of_ne (hpositive x hx) (Ne.symm hz)
        exact add_pos_of_pos_of_nonneg hpos (mul_nonneg hε.le (hρnonneg x))
  refine ⟨F, ?_, ?_⟩
  · intro b
    have hbfix (x : E) (hx : x ∈ r b) : F b x = x :=
      hfix (t b) x (fun hxU => Set.disjoint_left.mp (hboundary b) hx hxU)
    refine ⟨hfix (t b), hbfix, ?_, hsign b⟩
    obtain ⟨_, _, e, he, heval⟩ := hrest (t b)
    obtain ⟨g, hg, hge⟩ := he
    have hFPL : FinitePiecewiseAffineOn (F b : E → E) K.space :=
      hg.congr (fun x hx => (hge ⟨x, hx⟩).symm.trans (heval ⟨x, hx⟩))
    have hbb : F b '' r b = r b := by
      calc
        _ = id '' r b := image_congr hbfix
        _ = r b := image_id _
    have hp := (hR b).image_of_subset hFPL
      ((hRP b).trans (hPK.trans interior_subset)) (F b).injective.injOn
    rwa [hbb] at hp
  · apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hp := hsign true x hx
    have hn := hsign false z hz
    simp only [if_true, Bool.false_eq_true, if_false] at hp hn
    rw [hxy] at hp
    rw [hzy] at hn
    exact (not_lt_of_gt hp) hn

end PoincareConjecture.M76
