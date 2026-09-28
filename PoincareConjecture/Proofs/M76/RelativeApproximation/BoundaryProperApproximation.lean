import PoincareConjecture.Proofs.M76.RelativeApproximation.RetainedModelApproximation
import PoincareConjecture.Proofs.M76.RelativeApproximation.InteriorComposite
import PoincareConjecture.Proofs.M76.RelativeApproximation.Mathlib.InteriorHomotopyPasting












set_option autoImplicit false

open Set Geometry unitInterval

namespace PoincareConjecture.M76

variable {X ι κ : Type*} [TopologicalSpace X] [T2Space X]




theorem hasRelativeBoundaryProperPLApproximation
    (e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ))
    (d : κ → OpenPartialHomeomorph X (Fin 3 → ℝ)) (R : Set X) :
    HasRelativeBoundaryProperPLApproximation e d R := by
  classical
  intro hR he hd U hU hboundary hidentity
  by_cases hne : R.Nonempty
  swap
  · refine ⟨ContinuousMap.id R, ⟨he, hd, isOpen_univ, ?_⟩, rfl, ?_⟩
    · intro x _
      exact False.elim (hne ⟨x, x.property⟩)
    · exact ⟨ContinuousMap.HomotopyRel.refl _ _⟩
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨s, F, C, K, H, hC, hAC, hCR, hfront, hK, hF, hFPL, hHF, hcharts⟩ :=
    exists_interior_supported_PL_model hR he hU hboundary
  obtain ⟨q, T, V, hqPL, _, hTR, hV, hfrontV, hT0, hT1, hTfix⟩ :=
    exists_retained_model_approximation e d hidentity hCR hfront
      K hK H F ⟨x0, hx0⟩ hHF hcharts
  let G : C(I × C, X) :=
    ⟨fun z => T (z.1, H z.2),
      T.continuous.comp (continuous_fst.prodMk (H.continuous.comp continuous_snd))⟩
  have hG0 (x : C) : G (0, x) = (x : X) := by
    change T (0, H x) = (x : X)
    rw [hT0, H.symm_apply_apply]
  obtain ⟨S, W, hW, hcover, hSC, hSW, hS0, hproper⟩ :=
    exists_interior_homotopy_pasting hC.isClosed hCR G
      (fun z => hTR (z.1, H z.2)) hG0 hV hfrontV hTfix
  let phi : C(R, R) :=
    ⟨fun x => S (1, x), S.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hphiq (x : R) (hx : (x : X) ∈ C) : (phi x : X) = q (F x) := by
    change (S (1, x) : X) = q (F x)
    rw [hSC 1 ⟨x, hx⟩]
    change T (1, H ⟨x, hx⟩) = q (F x)
    rw [hT1, hHF]
  have hPLin : ChartwisePLOn e d phi ((Subtype.val : R → X) ⁻¹' interior C) :=
    chartwisePLOn_interior_model_composite e d he hd phi
      (hCR.trans interior_subset) K H F hF hFPL hHF q hqPL hphiq
  let O : Set R := U ∩ (Subtype.val : R → X) ⁻¹' W
  have hO : IsOpen O := hU.inter (hW.preimage continuous_subtype_val)
  have hPLout : ChartwisePLOn e d phi O :=
    hidentity.congr_mono hO inter_subset_left (fun x hx => (hSW 1 x hx.2).symm)
  have hlocal (x : R) : ∃ Z : Set R, ChartwisePLOn e d phi Z ∧ x ∈ Z := by
    by_cases hx : (x : X) ∈ interior C
    · exact ⟨_, hPLin, hx⟩
    · refine ⟨O, hPLout, ?_, hcover hx⟩
      by_contra hxU
      exact hx (hAC ⟨x, hxU, rfl⟩)
  refine ⟨phi, ⟨he, hd, isOpen_univ, ?_⟩, hproper 1, ?_⟩
  · intro x _
    obtain ⟨Z, hZ, hxZ⟩ := hlocal x
    obtain ⟨i, j, J, N, a, hJ, hN, hxN, _, hNi, hNJ, hJt, hJZ, ha, hval⟩ :=
      hZ.coordinates x hxZ
    refine ⟨i, j, J, N, a, hJ, hN, hxN, subset_univ _, hNi, hNJ, hJt, ?_, ha, hval⟩
    intro z hz
    obtain ⟨y, _, hy⟩ := hJZ hz
    exact ⟨y, mem_univ _, hy⟩
  · refine ⟨{
      toFun := S
      continuous_toFun := S.continuous
      map_zero_left := hS0
      map_one_left := fun _ => rfl
      prop' := ?_
    }⟩
    intro t x hx
    apply hSW
    apply hcover
    intro hxC
    exact hx.2 (hCR (interior_subset hxC))

end PoincareConjecture.M76
