import PoincareConjecture.Proofs.M76.Triangulation.ActualSurfaceFrontierMap
import PoincareConjecture.Proofs.M76.Mathlib.PairedInwardSourcePolePatches
import PoincareConjecture.Proofs.M76.Mathlib.LinearFrontierGermTarget

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_actual_inward_frontier_map
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (s : Bool → Finset E) (hs : ∀ j, s j ∈ K.faces) (hcard : ∀ j, (s j).card = 3)
    (a p : Bool → E)
    (ha : ∀ j, a j ∈ intrinsicInterior ℝ (convexHull ℝ (s j : Set E)))
    (hp : ∀ j, p j ∈ intrinsicInterior ℝ (convexHull ℝ (s j : Set E)))
    (f : Bool → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (hfzero : ∀ j, f j 0 = a j)
    {R : ℝ} (hR : 0 < R)
    (hsurface : ∀ j x, x ∈ box R → (f j x ∈ K.space ↔ x.2 = 0))
    (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hflast : ∀ j x, (L j (f j x)).2 = x.2)
    (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0) (hdim : Module.finrank ℝ E = 3)
    (hheight : ∀ j x, (L j x).1.1 = A x)
    (hfheight : ∀ j x, A (f j x) = x.1.1)
    {d : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (K.space ∩ {x | A x = 0}))
    (hdplane : d ⊆ {x | A x = 0})
    (hinward : ∀ j x, x ∈ box R → x.1.1 = 0 → (f j x ∈ d ↔ 0 ≤ x.2))
    (B : SimplicialComplex ℝ E) (hB : B.faces.Finite)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hBC : B.space = C) (hzero : (0 : E) ∈ interior C)
    (Z : Finset (E →ₗ[ℝ] ℝ)) (hZ : C = {x | ∀ Q ∈ Z, Q x ≤ 1})
    (hpC : ∀ j, p j ∈ frontier C) (hpne : p false ≠ p true)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hPS : P.boundary ℝ = frontier C ∩ K.space)
    (hPzero : P.boundary ℝ ∩ {x | A x = 0} = {p false, p true})
    (hnegP : ∃ x ∈ P.boundary ℝ, A x < 0)
    (hposP : ∃ x ∈ P.boundary ℝ, 0 < A x)
    (σ : Bool → ℝ) (hσneg : σ false < 0) (hσpos : 0 < σ true)
    (hLp : ∀ j, L j (p j) = ((0, σ j), 0))
    (ε : Bool → ℝ) (hε : ∀ j, 0 < ε j) :
    ∃ (T : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ))
      (H : frontier C ≃ₜ frontier T.space)
      (ψ : Bool → (ℝ × ℝ) → E) (r : Bool → ℝ) (O : Bool → Set E),
      T.faces.Finite ∧ IsCompact T.space ∧ Convex ℝ T.space ∧
      (0 : (ℝ × ℝ) × ℝ) ∈ interior T.space ∧ H.IsFinitePL ∧
      (∀ j, Continuous (ψ j) ∧ Function.Injective (ψ j) ∧ ψ j 0 = p j ∧
        r j ∈ Ioo 0 (ε j) ∧ FinitePiecewiseAffineOn (ψ j) (base (r j)) ∧
        ψ j '' base (r j) ⊆ frontier C ∧
        (∀ x, A (ψ j x) = x.1) ∧
        (∀ x, (L j (ψ j x)).1.1 = x.1) ∧
        (∀ x, (L j (ψ j x)).2 = x.2) ∧
        IsOpen (O j) ∧ p j ∈ O j ∧ frontier C ∩ O j ⊆ ψ j '' base (r j) ∧
        ∀ i : Bool × Bool,
          SourcePoleQuadrantData (ψ j) (frontier C) K.space
            (frontier C ∩ (K.space ∪ {x | A x = 0})) (p j) (p (!j)) A
            (if i.1 then -r j else r j) (if i.2 then -r j else r j)) ∧
      (∀ i j (x : frontier C), (x : E) ∈ ψ j '' signedRectangle (r j) i →
        (H x : (ℝ × ℝ) × ℝ) = L j x) ∧
      (∀ x : frontier C, 0 ≤ A x ↔ 0 ≤ (H x : (ℝ × ℝ) × ℝ).1.1) ∧
      (∀ x : frontier C, A x ≤ 0 ↔ (H x : (ℝ × ℝ) × ℝ).1.1 ≤ 0) ∧
      ∀ x : frontier C, (x : E) ∈ K.space ↔ (H x : (ℝ × ℝ) × ℝ).2 = 0 := by
  let ratio : ℝ := σ true / (-σ false)
  have hratio : 0 < ratio := div_pos hσpos (neg_pos.mpr hσneg)
  have hratioσ : ratio * σ false = -σ true := by
    change (σ true / (-σ false)) * σ false = -σ true
    rw [div_neg, neg_mul, div_mul_cancel₀ _ hσneg.ne]
  have hpq : (((0 : ℝ), σ true), (0 : ℝ)) =
      -(ratio • (((0 : ℝ), σ false), (0 : ℝ))) := by
    simp only [Prod.smul_mk, smul_eq_mul, mul_zero, hratioσ, Prod.neg_mk, neg_zero, neg_neg]
  obtain ⟨T, U₀, U₁, hT, hD, hDcv, hDzero, hU₀, hpU₀, hU₁, hpU₁,
    hUdis, _, _, hfront₀, hfront₁, hpD₀, hpD₁⟩ :=
    exists_convex_target_of_negatively_collinear_frontier_germs Z hZ (L false) (L true)
      hratio hpq (hpC false) (hpC true) (hLp false) (hLp true)
  let V : Bool → Set ((ℝ × ℝ) × ℝ) := fun j => if j then U₁ else U₀
  have hV (j : Bool) : IsOpen (V j) := by
    cases j
    · exact hU₀
    · exact hU₁
  have hpV (j : Bool) : L j (p j) ∈ V j := by
    cases j
    · change L false (p false) ∈ U₀
      rw [hLp false]
      exact hpU₀
    · change L true (p true) ∈ U₁
      rw [hLp true]
      exact hpU₁
  have hfront (j : Bool) : frontier T.space ∩ V j = (L j '' frontier C) ∩ V j := by
    cases j
    · exact hfront₀
    · exact hfront₁
  have hpD (j : Bool) : L j (p j) ∈ frontier T.space := by
    cases j
    · simpa only [hLp false] using hpD₀
    · simpa only [hLp true] using hpD₁
  have hσ (j : Bool) : σ j ≠ 0 := by
    cases j
    · exact hσneg.ne
    · exact hσpos.ne'
  obtain ⟨ψ, r, O, δ, hpatch, htarget, hdis, hDis⟩ :=
    K.exists_paired_inward_source_pole_patches hK hbound s hs hcard a p ha hp
      f hfzero hR hsurface L hflast A hA hdim hheight hfheight hd hdplane hinward
      Z hZ hpC hpne σ hσ hLp T.space V hV hpV hUdis hfront ε hε
  simp only [forall_and] at hpatch
  rcases hpatch with ⟨hψ, hinj, hψzero, hr, hPL, hsquare, hψheight,
    hfirst, hlast, hO, hpO, hOP, hδ, _, hside, hquad⟩
  obtain ⟨H, hH, hkeep, hpos, hneg, hplane⟩ :=
    B.exists_actual_surface_frontier_map hB hC hcv hBC hzero A hA hdim
      P hP hinjP hPS p hpne hPzero hnegP hposP hd hdplane ψ hinj hψzero r
      (fun j => (hr j).1) hψheight (fun i j => hquad j i) δ hδ hside L hfirst hlast
      T hT hD hDcv rfl hDzero σ hσneg hσpos hLp hpD htarget hdis hDis
  refine ⟨T, H, ψ, r, O, hT, hD, hDcv, hDzero, hH, ?_, hkeep, hpos, hneg, hplane⟩
  intro j
  exact ⟨hψ j, hinj j, hψzero j, hr j, hPL j, hsquare j, hψheight j,
    hfirst j, hlast j, hO j, hpO j, hOP j, hquad j⟩

end Geometry.SimplicialComplex
