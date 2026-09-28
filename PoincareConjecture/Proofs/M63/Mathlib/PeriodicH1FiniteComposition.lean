import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1Graph
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicH1VectorDecoder
import PoincareConjecture.Proofs.M63.Mathlib.ContinuousL2Product
import PoincareConjecture.Proofs.M03.Existence.ContinuousPathCompositionNative
import Mathlib.Analysis.Calculus.Deriv.Prod










set_option autoImplicit false

open AddCircle MeasureTheory Set Filter
open scoped ContDiff

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]





theorem exists_periodicH1_finite_composition {ι : Type*} [Fintype ι]
    (k : ℕ) (Φ : (ι → ℂ) → ℂ) (hΦ : ContDiff ℝ (k + 1) Φ) :
    ∃ G : (ι → lp (fun _ : ℤ => ℂ) 2) → lp (fun _ : ℤ => ℂ) 2,
      ContDiff ℝ k G ∧ ∀ u x,
        periodicSobolevJet (L := L) 0 0 (by omega) (G u) x =
          Φ (periodicH1VectorDecoder (L := L) ι u x) := by
  classical
  have hfin (n : ℕ) (phi : (Fin n → ℂ) → ℂ) (hphi : ContDiff ℝ (k + 1) phi) :
      ∃ G : (Fin n → lp (fun _ : ℤ => ℂ) 2) → lp (fun _ : ℤ => ℂ) 2,
        ContDiff ℝ k G ∧ ∀ u x,
          periodicSobolevJet (L := L) 0 0 (by omega) (G u) x =
            phi (periodicH1VectorDecoder (L := L) (Fin n) u x) := by
    let H := lp (fun _ : ℤ => ℂ) 2
    let X := Fin n → H
    let Y := Lp ℂ 2 (@haarAddCircle L _)
    let D := periodicSobolevJet (L := L) 0 0 (by omega)
    let DX := periodicH1VectorDecoder (L := L) (Fin n)
    let DL := periodicH1DerivativeLp (L := L)
    let R := periodicH1GraphReconstruct (L := L)
    let toLp : C(AddCircle L, ℂ) →L[ℂ] Y := ContinuousMap.toLp 2 (@haarAddCircle L _) ℂ
    let p : C(Fin n → ℂ, ℂ) := ⟨phi, hphi.continuous⟩
    have hphik : ContDiff ℝ k phi := hphi.of_le (by exact_mod_cast Nat.le_succ k)
    have hDphi : ContDiff ℝ k (fderiv ℝ phi) := hphi.fderiv_right (by simp)
    let A (i : Fin n) (z : Fin n → ℂ) : ℂ →L[ℝ] ℂ :=
      (fderiv ℝ phi z).comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i)
    have hA (i : Fin n) : ContDiff ℝ k (A i) := hDphi.clm_comp contDiff_const
    let a (i : Fin n) : C(Fin n → ℂ, ℂ →L[ℝ] ℂ) := ⟨A i, (hA i).continuous⟩
    obtain ⟨M, _hMnorm, hM⟩ := exists_continuousL2_product
      (@haarAddCircle L _) (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] ℂ))
    let f (u : X) : Y := toLp (p.comp (DX u))
    let g (u : X) : Y := ∑ i, M ((a i).comp (DX u)) (DL (u i))
    let G (u : X) : H := R (f u, g u)
    have hDX : ContDiff ℝ k (fun u : X => DX u) := (DX.restrictScalars ℝ).contDiff
    have hf : ContDiff ℝ k f :=
      (toLp.restrictScalars ℝ).contDiff.comp
        ((ContinuousPathCompositionNative.contDiff_postcomp_of_order
          (AddCircle L) p hphik).comp hDX)
    have hg : ContDiff ℝ k g := by
      apply ContDiff.sum
      intro i _
      exact (M.contDiff.comp
        ((ContinuousPathCompositionNative.contDiff_postcomp_of_order
          (AddCircle L) (a i) (hA i)).comp hDX)).clm_apply
            ((DL.restrictScalars ℝ).contDiff.comp (contDiff_apply ℝ H i))
    have hG : ContDiff ℝ k G := (R.restrictScalars ℝ).contDiff.comp (hf.prodMk hg)
    let s : Set X := {u | ∀ i, u i ∈ periodicC1Core (L := L)}
    have hs : Dense s := by
      simpa only [Set.pi, Set.mem_univ, true_implies, SetLike.mem_coe, s, X] using
        dense_pi (univ : Set (Fin n)) (fun _ _ => dense_periodicC1Core (L := L))
    refine ⟨G, hG, ?_⟩
    intro u x
    refine hs.denseRange_val.induction_on u ?_ ?_
    · exact isClosed_eq
        ((ContinuousMap.evalCLM ℂ x).continuous.comp (D.continuous.comp hG.continuous))
        (hphi.continuous.comp ((ContinuousMap.evalCLM ℂ x).continuous.comp DX.continuous))
    · intro v
      let d (i : Fin n) : C(AddCircle L, ℂ) := (v.property i).choose
      have hd (i : Fin n) (y : ℝ) :
          HasDerivAt (fun z : ℝ => D (v.val i) (z : AddCircle L))
            (d i (y : AddCircle L)) y := (v.property i).choose_spec y
      let dv : C(AddCircle L, Fin n → ℂ) :=
        ⟨fun y i => d i y, continuous_pi (fun i => (d i).continuous)⟩
      let c : C(AddCircle L, ℂ) := p.comp (DX v.val)
      let c1 : C(AddCircle L, ℂ) :=
        ⟨fun y => fderiv ℝ phi (DX v.val y) (dv y),
          ((hDphi.continuous.comp (DX v.val).continuous).clm_apply dv.continuous)⟩
      have hc (y : ℝ) : HasDerivAt (fun z : ℝ => c (z : AddCircle L))
          (c1 (y : AddCircle L)) y := by
        have hvec : HasDerivAt (fun z : ℝ => DX v.val (z : AddCircle L))
            (dv (y : AddCircle L)) y := hasDerivAt_pi.mpr (fun i => hd i y)
        exact (hphi.differentiable (by simp) _).hasFDerivAt
          |>.comp_hasDerivAt y hvec
      have hDL (i : Fin n) : DL (v.val i) = toLp (d i) := by
        have hcoord : periodicH1Coordinates (D (v.val i)) (d i) (hd i) = v.val i :=
          periodicH1Decoder_injective (periodicH1Coordinates_reconstruct _ _ (hd i))
        have h := (periodicH1Graph_spec (L := L)).2 _ _ (hd i) |>.1
        rw [hcoord] at h
        exact h
      have hprod (i : Fin n) : ∀ᵐ y ∂(@haarAddCircle L _),
          M ((a i).comp (DX v.val)) (DL (v.val i)) y = A i (DX v.val y) (d i y) := by
        rw [hDL]
        filter_upwards [hM ((a i).comp (DX v.val)) (toLp (d i)),
          ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℂ) (d i)] with y hmy hdy
        change M ((a i).comp (DX v.val)) (toLp (d i)) y =
          A i (DX v.val y) (toLp (d i) y) at hmy
        change toLp (d i) y = d i y at hdy
        rwa [hdy] at hmy
      have hgcore : g v.val = toLp c1 := by
        apply Lp.ext
        filter_upwards [Lp.coeFn_finsetSum Finset.univ
          (fun i => M ((a i).comp (DX v.val)) (DL (v.val i))),
          ae_all_iff.mpr hprod,
          ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℂ) c1] with y hsum hp hc1
        change (∑ i, M ((a i).comp (DX v.val)) (DL (v.val i))) y = toLp c1 y
        rw [hsum, hc1]
        simp only [Finset.sum_apply, hp]
        exact ContinuousLinearMap.sum_comp_single ℝ (fun _ : Fin n => ℂ)
          (fderiv ℝ phi (DX v.val y)) (dv y)
      have hcoords : G v.val = periodicH1Coordinates c c1 hc := by
        change R (f v.val, g v.val) = _
        rw [hgcore]
        exact (periodicH1Graph_spec (L := L)).2 c c1 hc |>.2
      change D (G v.val) x = phi (DX v.val x)
      rw [hcoords]
      exact congrArg (fun q : C(AddCircle L, ℂ) => q x)
        (periodicH1Coordinates_reconstruct c c1 hc)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E := Pi.compRightL ℝ (fun _ : Fin (Fintype.card ι) => ℂ) e.symm
  let S := Pi.compRightL ℝ (fun _ : ι => lp (fun _ : ℤ => ℂ) 2) e
  obtain ⟨G, hG, hdecode⟩ := hfin (Fintype.card ι) (Φ ∘ E) (hΦ.comp E.contDiff)
  refine ⟨G ∘ S, hG.comp S.contDiff, ?_⟩
  intro u x
  rw [Function.comp_apply, hdecode]
  apply congrArg Φ
  ext i
  change periodicSobolevJet (L := L) 0 0 (by omega) (u (e (e.symm i))) x =
    periodicSobolevJet (L := L) 0 0 (by omega) (u i) x
  rw [e.apply_symm_apply]

end PoincareConjecture.M63
