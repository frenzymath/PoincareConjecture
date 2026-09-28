import PoincareConjecture.Proofs.M76.Mathlib.PositiveApexLinearCutGerms











set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}







theorem exists_paired_positive_apex_linear_germs
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (t : Fin (n + 3) → ℝ)
    (ht : ∀ i, t i ∈ Ioo (0 : ℝ) 1) (i : Fin (n + 3))
    (hvertex : P (finRotate (n + 3) i) = 0)
    (f : Bool → ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E)
    (hfzero : ∀ j, f j 0 = P.edgeCut t (if j then finRotate (n + 3) i else i))
    {r : ℝ} (hr : 0 < r)
    (harc : ∀ j x, x ∈ box r →
      (f j x ∈ P.cutArc t (if j then finRotate (n + 3) i else i) ↔
        x.1.1 = 0 ∧ x.2 = 0 ∧ 0 ≤ x.1.2))
    (A : E →ₗ[ℝ] ℝ) (hheight : ∀ j x, A (f j x) = x.1.1)
    (σ : Bool → ℝ) (hσneg : σ false < 0) (hσpos : 0 < σ true) :
    ∃ (k : Bool → ℝ) (L : Bool → E ≃L[ℝ] ((ℝ × ℝ) × ℝ)),
      f false 0 ≠ f true 0 ∧
      ∀ j, 0 < k j ∧ f j 0 ≠ 0 ∧
        k j = σ j / (-((f j).symm 0).1.2) ∧
        L j (f j 0) = ((0, σ j), 0) ∧
        (∀ x : (ℝ × ℝ) × ℝ,
          L j (f j x) = ((x.1.1, σ j + k j * x.1.2), x.2)) ∧
        (∀ x : (ℝ × ℝ) × ℝ,
          L j (f j x) = ((x.1.1, k j * (x.1.2 - ((f j).symm 0).1.2)), x.2)) ∧
        (∀ x : E, (L j x).1.1 = A x) ∧
        ∀ t z : ℝ, L j (f j ((t, 0), z)) = ((t, σ j), z) := by
  have hex (j : Bool) : ∃ (k : ℝ) (L : E ≃L[ℝ] ((ℝ × ℝ) × ℝ)),
      k = σ j / (-((f j).symm 0).1.2) ∧ 0 < k ∧
      L (f j 0) = ((0, σ j), 0) ∧
      (∀ x : (ℝ × ℝ) × ℝ,
        L (f j x) = ((x.1.1, k * (x.1.2 - ((f j).symm 0).1.2)), x.2)) ∧
      (∀ x : E, (L x).1.1 = A x) ∧
      ∀ t z : ℝ, L (f j ((t, 0), z)) = ((t, σ j), z) := by
    have hside :
        (P (if j then finRotate (n + 3) i else i) = 0 ∧ 0 < σ j) ∨
        (P (finRotate (n + 3) (if j then finRotate (n + 3) i else i)) = 0 ∧
          σ j < 0) := by
      cases j
      · exact Or.inr ⟨hvertex, hσneg⟩
      · exact Or.inl ⟨hvertex, hσpos⟩
    obtain ⟨k, L, hk, hkpos, hp, hformula, hA, hlateral⟩ :=
      P.exists_positive_apex_linear_germ_of_oriented_cut hinj t ht
        (if j then finRotate (n + 3) i else i) (f j) (hfzero j) hr (harc j)
        A (hheight j) hside
    refine ⟨k, L, hk, hkpos, ?_, hformula, hA, hlateral⟩
    rw [hfzero j]
    exact hp
  choose k L hk hkpos hp hformula hA hlateral using hex
  have hmarks : f false 0 ≠ f true 0 := by
    rw [hfzero false, hfzero true]
    intro h
    have hind : i = finRotate (n + 3) i := P.edgeCut_injective hP hinj t ht h
    exact P.edge_endpoints_ne_of_injective hinj i (congrArg P hind)
  have hσne (j : Bool) : σ j ≠ 0 := by
    cases j
    · exact hσneg.ne
    · exact hσpos.ne'
  refine ⟨k, L, hmarks, ?_⟩
  intro j
  have hcut : f j 0 ≠ 0 := by
    intro h
    have hpole := hp j
    rw [h, map_zero] at hpole
    have hzero : (0 : ℝ) = σ j :=
      congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2) hpole
    exact hσne j hzero.symm
  have hintercept : k j * (-((f j).symm 0).1.2) = σ j := by
    have h := congrArg (fun x : (ℝ × ℝ) × ℝ => x.1.2)
      ((hformula j 0).symm.trans (hp j))
    change k j * (0 - ((f j).symm 0).1.2) = σ j at h
    simpa only [zero_sub] using h
  refine ⟨hkpos j, hcut, hk j, hp j, ?_, hformula j, hA j, hlateral j⟩
  intro x
  have hmiddle : k j * (x.1.2 - ((f j).symm 0).1.2) =
      σ j + k j * x.1.2 := by nlinarith
  rw [hformula j x, hmiddle]

end Polygon
