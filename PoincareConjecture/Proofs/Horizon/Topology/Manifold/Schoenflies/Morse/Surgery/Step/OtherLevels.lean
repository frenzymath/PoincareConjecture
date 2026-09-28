import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Step
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.OtherLevels



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryStep

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)


theorem capMinus_height_mem_slab (x : E2) : |inner Real v (S.gMinus x) - c| < R := by
  obtain ⟨hl, hu⟩ := abs_lt.mp (S.gMinus_width x)
  exact abs_lt.mpr ⟨by linarith [S.a_pos, S.a_lt_quarter_R],
    by linarith [S.a_pos, S.a_lt_quarter_R]⟩


theorem capPlus_height_mem_slab (x : E2) : |inner Real v (S.gPlus x) - c| < R := by
  obtain ⟨hl, hu⟩ := abs_lt.mp (S.gPlus_width x)
  exact abs_lt.mpr ⟨by linarith [S.a_pos, S.a_lt_quarter_R],
    by linarith [S.a_pos, S.a_lt_quarter_R]⟩


theorem capMinus_avoids_of_far {k : Real} (hk : R < |k - c|) (x : E2) :
    inner Real v (S.gMinus x) ≠ k := by
  intro heq
  have hb := S.capMinus_height_mem_slab x
  rw [heq] at hb
  exact (not_lt_of_ge hk.le) hb


theorem capPlus_avoids_of_far {k : Real} (hk : R < |k - c|) (x : E2) :
    inner Real v (S.gPlus x) ≠ k := by
  intro heq
  have hb := S.capPlus_height_mem_slab x
  rw [heq] at hb
  exact (not_lt_of_ge hk.le) hb


theorem other_regular {k : Real} (hk : R < |k - c|)
    (hregular : ∀ p, inner Real v (f p) = k →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0) :
    (∀ p, inner Real v (S.fMinus p) = k →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.fMinus q)) p ≠ 0) ∧
    (∀ p, inner Real v (S.fPlus p) = k →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.fPlus q)) p ≠ 0) := by
  have hregularD : ∀ p, inner Real v (S.D (f p)) = k →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.D (f q))) p ≠ 0 := by
    rw [S.prepared_height_eq]
    simpa only [S.height_preserving] using hregular
  exact ⟨regular_level_of_disk_splicing (fun p => S.D (f p)) S.fMinus v k
      S.eMinus S.dMinus S.eMinus_source S.dMinus_closed S.gMinus
      S.capMinus_eq S.retainedMinus_eq (fun x _ => S.capMinus_avoids_of_far hk x) hregularD,
    regular_level_of_disk_splicing (fun p => S.D (f p)) S.fPlus v k
      S.ePlus S.dPlus S.ePlus_source S.dPlus_closed S.gPlus
      S.capPlus_eq S.retainedPlus_eq (fun x _ => S.capPlus_avoids_of_far hk x) hregularD⟩

private def componentsEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y :=
  (H.isQuotientMap.isCoinducing.connectedComponentsHomeomorph fun y => by
    have hfiber : H ⁻¹' {y} = {H.symm y} := by ext x; exact H.toEquiv.eq_symm_apply.symm
    rw [hfiber]
    exact isConnected_singleton).toEquiv



theorem other_card {k : Real} (hk : R < |k - c|)
    [Finite (ConnectedComponents ((fun p => inner Real v (f p)) ⁻¹' {k}))] :
    let Lminus := (fun p => inner Real v (S.fMinus p)) ⁻¹' {k}
    let Lplus := (fun p => inner Real v (S.fPlus p)) ⁻¹' {k}
    let L := (fun p => inner Real v (f p)) ⁻¹' {k}
    Finite (ConnectedComponents Lminus) ∧ Finite (ConnectedComponents Lplus) ∧
      Nat.card (ConnectedComponents Lminus) + Nat.card (ConnectedComponents Lplus) =
        Nat.card (ConnectedComponents L) := by
  let L := (fun p => inner Real v (f p)) ⁻¹' {k}
  let U : Set L := Subtype.val ⁻¹' (S.eMinus '' ball 0 1)
  let V : Set L := Subtype.val ⁻¹' (S.ePlus '' ball 0 1)
  let Lminus := (fun p => inner Real v (S.fMinus p)) ⁻¹' {k}
  let Lplus := (fun p => inner Real v (S.fPlus p)) ⁻¹' {k}
  have haε : S.a < S.ε := by linarith [S.a_lt_quarter_ε, S.ε_pos]
  have hak : S.a < |k - c| := by linarith [S.a_pos, S.a_lt_quarter_R]
  obtain ⟨hU, hV, hcard⟩ := card_other_level_components_of_parallel_disks
    (h := fun p => inner Real v (f p))
    haε hak S.T S.tube_height S.eMinus S.ePlus S.eMinus_source S.ePlus_source
    S.retained_disjoint S.slab_eq
  let : Finite (ConnectedComponents U) := hU
  let : Finite (ConnectedComponents V) := hV
  have hminus := exists_level_homeomorph_retained_of_disk_splicing
    (fun p => S.D (f p)) S.fMinus v k S.eMinus S.dMinus S.eMinus_source S.dMinus_closed
    S.gMinus S.capMinus_eq S.retainedMinus_eq (fun x _ => S.capMinus_avoids_of_far hk x)
  have hplus := exists_level_homeomorph_retained_of_disk_splicing
    (fun p => S.D (f p)) S.fPlus v k S.ePlus S.dPlus S.ePlus_source S.dPlus_closed
    S.gPlus S.capPlus_eq S.retainedPlus_eq (fun x _ => S.capPlus_avoids_of_far hk x)
  dsimp only at hminus hplus
  rw [S.prepared_height_eq] at hminus hplus
  obtain ⟨Hminus, _⟩ := hminus
  obtain ⟨Hplus, _⟩ := hplus
  let Eminus : ConnectedComponents Lminus ≃ ConnectedComponents U := componentsEquiv Hminus
  let Eplus : ConnectedComponents Lplus ≃ ConnectedComponents V := componentsEquiv Hplus
  let : Finite (ConnectedComponents Lminus) := Finite.of_equiv _ Eminus.symm
  let : Finite (ConnectedComponents Lplus) := Finite.of_equiv _ Eplus.symm
  refine ⟨inferInstance, inferInstance, ?_⟩
  exact (congrArg₂ (fun m n : Nat => m + n)
    (Nat.card_congr Eminus) (Nat.card_congr Eplus)).trans hcard



theorem regular_on_cuts {A : Set Real}
    (hseparation : ∀ k ∈ A, k ≠ c → R < |k - c|)
    (hregular : ∀ k ∈ A, ∀ p, inner Real v (f p) = k →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0) :
    (∀ k ∈ A, ∀ p, inner Real v (S.fMinus p) = k →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.fMinus q)) p ≠ 0) ∧
    (∀ k ∈ A, ∀ p, inner Real v (S.fPlus p) = k →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.fPlus q)) p ≠ 0) := by
  have hboth (k : Real) (hk : k ∈ A) :
      (∀ p, inner Real v (S.fMinus p) = k →
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.fMinus q)) p ≠ 0) ∧
      (∀ p, inner Real v (S.fPlus p) = k →
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (S.fPlus q)) p ≠ 0) := by
    by_cases hkc : k = c
    · subst k
      exact S.central_regular (hregular c hk)
    · exact S.other_regular (hseparation k hk hkc) (hregular k hk)
  exact ⟨fun k hk => (hboth k hk).1, fun k hk => (hboth k hk).2⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryStep
