import PoincareConjecture.Proofs.M76.Mathlib.CanonicalAxisArcMaps













set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes RectangleCornerArcs

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]









theorem exists_paired_source_pole_quadrant_patches
    {C S : Set E} (H : Finset (E →ₗ[ℝ] ℝ))
    (hC : C = {x | ∀ A ∈ H, A x ≤ 1})
    (e : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ)) (A : E →ₗ[ℝ] ℝ)
    (hheight : ∀ j x, (e j x).1.1 = A x)
    (p : Bool → E) (hp : ∀ j, p j ∈ frontier C) (hpne : p false ≠ p true)
    (σ : Bool → ℝ) (hσ : ∀ j, σ j ≠ 0)
    (hep : ∀ j, e j (p j) = ((0, σ j), 0))
    (U : Bool → Set E) (hU : ∀ j, IsOpen (U j)) (hpU : ∀ j, p j ∈ U j)
    (hS : ∀ j x, x ∈ U j → (x ∈ S ↔ (e j x).2 = 0))
    (D : Set ((ℝ × ℝ) × ℝ)) (V : Bool → Set ((ℝ × ℝ) × ℝ))
    (hV : ∀ j, IsOpen (V j)) (hpV : ∀ j, e j (p j) ∈ V j)
    (hVdis : Disjoint (V false) (V true))
    (hfront : ∀ j, frontier D ∩ V j = (e j '' frontier C) ∩ V j)
    (ε : Bool → ℝ) (hε : ∀ j, 0 < ε j) :
    ∃ (f : Bool → (ℝ × ℝ) → ℝ) (ψ : Bool → (ℝ × ℝ) → E)
      (W : Bool → Set E) (r : Bool → ℝ),
      (∀ j, Continuous (f j) ∧ f j 0 = 1 ∧
        Continuous (ψ j) ∧ Function.Injective (ψ j) ∧ ψ j 0 = p j ∧
        IsOpen (W j) ∧ p j ∈ W j ∧ W j ⊆ U j ∩ (e j) ⁻¹' V j ∧
        p (!j) ∉ W j ∧ r j ∈ Ioo 0 (ε j) ∧
        FinitePiecewiseAffineOn (ψ j) (base (r j)) ∧
        ψ j '' base (r j) ⊆ frontier C ∩ W j ∧
        (∀ x, e j (ψ j x) = ((x.1, σ j * f j x), x.2)) ∧
        (∀ x, A (ψ j x) = x.1) ∧
        (∀ x ∈ base (r j), ψ j x ∈ S ↔ x.2 = 0) ∧
        IsFinitePLBallPair (ℝ × ℝ) (ψ j '' base (r j)) (ψ j '' baseBoundary (r j)) ∧
        (∀ T ⊆ base (r j),
          (frontier C ∩ W j) ∩ (fun x => ((e j x).1.1, (e j x).2)) ⁻¹' T = ψ j '' T) ∧
        (∃ O : Set E, IsOpen O ∧ p j ∈ O ∧ frontier C ∩ O ⊆ ψ j '' base (r j)) ∧
        ∀ t z : ℝ, t ≠ 0 → z ≠ 0 → |t| ≤ r j → |z| ≤ r j →
          SourcePoleQuadrantData (ψ j) (frontier C) S
            (frontier C ∩ (S ∪ {x | A x = 0})) (p j) (p (!j)) A t z) ∧
      Disjoint (W false) (W true) ∧
      (∀ j, e j '' (ψ j '' base (r j)) ⊆ frontier D ∩ V j) ∧
      (∀ j, e (!j) (p (!j)) ∉ V j) ∧
      Disjoint (ψ false '' base (r false)) (ψ true '' base (r true)) ∧
      Disjoint (e false '' (ψ false '' base (r false)))
        (e true '' (ψ true '' base (r true))) ∧
      ∀ (k l : Bool) (a b : ℝ), |a| ≤ r false → |b| ≤ r true →
        Disjoint (ψ false '' axisInterval k a) (ψ true '' axisInterval l b) ∧
          Disjoint (e false '' (ψ false '' axisInterval k a))
            (e true '' (ψ true '' axisInterval l b)) := by
  classical
  obtain ⟨Q₀, Q₁, hQ₀, hQ₁, hpQ₀, hpQ₁, hQdis⟩ := t2_separation hpne
  let Q : Bool → Set E := fun j => if j then Q₁ else Q₀
  have hQ (j : Bool) : IsOpen (Q j) := by
    cases j
    · exact hQ₀
    · exact hQ₁
  have hpQ (j : Bool) : p j ∈ Q j := by
    cases j
    · exact hpQ₀
    · exact hpQ₁
  have hpother (j : Bool) : p j ≠ p (!j) := by
    cases j
    · exact hpne
    · exact hpne.symm
  let U' : Bool → Set E := fun j => (U j ∩ Q j) ∩ (e j) ⁻¹' V j
  have hU' (j : Bool) : IsOpen (U' j) :=
    ((hU j).inter (hQ j)).inter ((hV j).preimage (e j).continuous)
  have hpU' (j : Bool) : p j ∈ U' j := ⟨⟨hpU j, hpQ j⟩, hpV j⟩
  have hlocal := fun j : Bool =>
    exists_source_pole_quadrant_patches H hC (e j) A (hheight j)
      (hp j) (hpother j) (hσ j) (hep j) (hU' j) (hpU' j)
      (fun x hx => hS j x hx.1.1) (hε j)
  choose f ψ W r hf hfzero hψ hinj hψzero hW hpW hWsub hother hr
    hPL hbase hcoords hψheight hsurface hball hproject hneighbor hquad using hlocal
  have hWQ (j : Bool) : W j ⊆ Q j := fun x hx => (hWsub j hx).1.2
  have hWdis : Disjoint (W false) (W true) := hQdis.mono (hWQ false) (hWQ true)
  have hsource (j : Bool) : ψ j '' base (r j) ⊆ W j :=
    fun x hx => (hbase j hx).2
  have htarget (j : Bool) : e j '' (ψ j '' base (r j)) ⊆ frontier D ∩ V j := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hfront j).symm.subset
      ⟨⟨x, (hbase j hx).1, rfl⟩, (hWsub j (hbase j hx).2).2⟩
  have htargetV (j : Bool) : e j '' (ψ j '' base (r j)) ⊆ V j :=
    fun x hx => (htarget j hx).2
  have htargetOther (j : Bool) : e (!j) (p (!j)) ∉ V j := by
    cases j
    · intro hx
      exact disjoint_left.mp hVdis hx (hpV true)
    · intro hx
      exact disjoint_left.mp hVdis (hpV false) hx
  refine ⟨f, ψ, W, r, ?_, hWdis, htarget, htargetOther,
    hWdis.mono (hsource false) (hsource true),
    hVdis.mono (htargetV false) (htargetV true), ?_⟩
  · intro j
    refine ⟨hf j, hfzero j, hψ j, hinj j, hψzero j, hW j, hpW j, ?_,
      hother j, hr j, hPL j, hbase j, hcoords j, hψheight j, hsurface j,
      hball j, hproject j, hneighbor j, hquad j⟩
    intro x hx
    exact ⟨(hWsub j hx).1.1, (hWsub j hx).2⟩
  · intro k l a b ha hb
    exact disjoint_source_and_target_axis_intervals ψ e r (fun j => (hr j).1.le)
      W V hWdis hVdis hsource htargetV k l ha hb

end Geometry.SimplicialComplex
