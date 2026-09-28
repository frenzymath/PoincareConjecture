import PoincareConjecture.Proofs.M76.Mathlib.PairedSourcePolePatches
import PoincareConjecture.Proofs.M76.Mathlib.ActualCutPoleSideTransport












set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_paired_inward_source_pole_patches
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
    {C : Set E} (H : Finset (E →ₗ[ℝ] ℝ)) (hC : C = {x | ∀ B ∈ H, B x ≤ 1})
    (hpC : ∀ j, p j ∈ frontier C) (hpne : p false ≠ p true)
    (σ : Bool → ℝ) (hσ : ∀ j, σ j ≠ 0)
    (hLp : ∀ j, L j (p j) = ((0, σ j), 0))
    (D : Set ((ℝ × ℝ) × ℝ)) (V : Bool → Set ((ℝ × ℝ) × ℝ))
    (hV : ∀ j, IsOpen (V j)) (hpV : ∀ j, L j (p j) ∈ V j)
    (hVdis : Disjoint (V false) (V true))
    (hfront : ∀ j, frontier D ∩ V j = (L j '' frontier C) ∩ V j)
    (ε : Bool → ℝ) (hε : ∀ j, 0 < ε j) :
    ∃ (ψ : Bool → (ℝ × ℝ) → E) (r : Bool → ℝ)
      (O : Bool → Set E) (δ : Bool → ℝ),
      (∀ j, Continuous (ψ j) ∧ Function.Injective (ψ j) ∧ ψ j 0 = p j ∧
        r j ∈ Ioo 0 (ε j) ∧ FinitePiecewiseAffineOn (ψ j) (base (r j)) ∧
        ψ j '' base (r j) ⊆ frontier C ∧
        (∀ x, A (ψ j x) = x.1) ∧
        (∀ x, (L j (ψ j x)).1.1 = x.1) ∧
        (∀ x, (L j (ψ j x)).2 = x.2) ∧
        IsOpen (O j) ∧ p j ∈ O j ∧ frontier C ∩ O j ⊆ ψ j '' base (r j) ∧
        0 < δ j ∧ δ j ≤ R ∧
        (∀ z : ℝ, |z| ≤ δ j → (ψ j (0, z) ∈ d ↔ 0 ≤ z)) ∧
        ∀ i : Bool × Bool,
          SourcePoleQuadrantData (ψ j) (frontier C) K.space
            (frontier C ∩ (K.space ∪ {x | A x = 0})) (p j) (p (!j)) A
            (if i.1 then -r j else r j) (if i.2 then -r j else r j)) ∧
      (∀ j, L j '' (ψ j '' base (r j)) ⊆ frontier D) ∧
      Disjoint (ψ false '' base (r false)) (ψ true '' base (r true)) ∧
      Disjoint (L false '' (ψ false '' base (r false)))
        (L true '' (ψ true '' base (r true))) := by
  classical
  have hgerms (j : Bool) : ∃ U : Set E, IsOpen U ∧ p j ∈ U ∧
      ∀ x ∈ U, x ∈ K.space ↔ (L j x).2 = 0 := by
    have hplane := K.mem_triangle_affineSpan_iff_last_eq_zero_of_cut_box
      hK hbound (hs j) (hcard j) (ha j) (f j) (hfzero j) hR
      (hsurface j) (L j) (hflast j)
    obtain ⟨U, hU, hpU, hKU⟩ :=
      K.exists_open_eq_affineSpan_of_triangle_interior hK hbound (hs j) (hcard j) (hp j)
    refine ⟨U, hU, hpU, ?_⟩
    intro x hx
    exact (show x ∈ K.space ↔ x ∈ affineSpan ℝ (s j : Set E) from
      ⟨fun h => (hKU.subset ⟨h, hx⟩).1,
        fun h => (hKU.symm.subset ⟨h, hx⟩).1⟩).trans (hplane x)
  choose U hU hpU hKU using hgerms
  obtain ⟨θ, ψ, W, r, hpatch, _, htarget, _, hdis, hDis, _⟩ :=
    exists_paired_source_pole_quadrant_patches H hC L A hheight p hpC hpne σ hσ hLp
      U hU hpU hKU D V hV hpV hVdis hfront ε hε
  have hretain (j : Bool) : ∃ (O : Set E) (δ : ℝ),
      Continuous (ψ j) ∧ Function.Injective (ψ j) ∧ ψ j 0 = p j ∧
      r j ∈ Ioo 0 (ε j) ∧ FinitePiecewiseAffineOn (ψ j) (base (r j)) ∧
      ψ j '' base (r j) ⊆ frontier C ∧
      (∀ x, A (ψ j x) = x.1) ∧
      (∀ x, (L j (ψ j x)).1.1 = x.1) ∧
      (∀ x, (L j (ψ j x)).2 = x.2) ∧
      IsOpen O ∧ p j ∈ O ∧ frontier C ∩ O ⊆ ψ j '' base (r j) ∧
      0 < δ ∧ δ ≤ R ∧
      (∀ z : ℝ, |z| ≤ δ → (ψ j (0, z) ∈ d ↔ 0 ≤ z)) ∧
      ∀ i : Bool × Bool,
        SourcePoleQuadrantData (ψ j) (frontier C) K.space
          (frontier C ∩ (K.space ∪ {x | A x = 0})) (p j) (p (!j)) A
          (if i.1 then -r j else r j) (if i.2 then -r j else r j) := by
    obtain ⟨_, _, hψ, hinj, hψzero, _, _, _, _, hr, hPL, hbase,
      hcoords, hψheight, _, _, _, ⟨O, hO, hpO, hneighbor⟩, hquad⟩ := hpatch j
    have hfirst (x : ℝ × ℝ) : (L j (ψ j x)).1.1 = x.1 :=
      congrArg (fun y : (ℝ × ℝ) × ℝ => y.1.1) (hcoords x)
    have hlast (x : ℝ × ℝ) : (L j (ψ j x)).2 = x.2 :=
      congrArg (fun y : (ℝ × ℝ) × ℝ => y.2) (hcoords x)
    obtain ⟨δ, hδ, hδR, hside⟩ :=
      K.exists_actual_cut_pole_filling_signs hK hbound (hs j) (hcard j) (ha j) (hp j)
        (f j) (hfzero j) hR (hsurface j) (L j) (hflast j)
        (ψ j) hψ hψzero hlast A hA hdim (hfheight j) hψheight hd hdplane (hinward j)
    refine ⟨O, δ, hψ, hinj, hψzero, hr, hPL,
      fun x hx => (hbase hx).1, hψheight, hfirst, hlast,
      hO, hpO, hneighbor, hδ, hδR, hside, ?_⟩
    intro i
    have hnonzero (k : Bool) : (if k then -r j else r j) ≠ 0 := by
      cases k
      · exact hr.1.ne'
      · exact neg_ne_zero.mpr hr.1.ne'
    have habs (k : Bool) : |if k then -r j else r j| ≤ r j := by
      cases k <;> simp only [Bool.false_eq_true, ite_false, ite_true, abs_neg,
        abs_of_pos hr.1, le_refl]
    exact hquad _ _ (hnonzero i.1) (hnonzero i.2) (habs i.1) (habs i.2)
  choose O δ hretain using hretain
  exact ⟨ψ, r, O, δ, hretain, fun j x hx => (htarget j hx).1, hdis, hDis⟩

end Geometry.SimplicialComplex
