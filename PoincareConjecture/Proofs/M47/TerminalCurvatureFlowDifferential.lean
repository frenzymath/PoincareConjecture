import PoincareConjecture.Proofs.M47.TerminalCurvatureCompleteFlow
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M47

variable {M A : Type*} [TopologicalSpace M] [TopologicalSpace A]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) A]



theorem terminalCurvature_flow_sphere_differential
    (V : (x : M) → TangentSpace (𝓡 3) x) (Phi : ℝ → M → M)
    (hzero : ∀ x, Phi 0 x = x)
    (hPhi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun tx : ℝ × M => Phi tx.1 tx.2))
    (hcurve : ∀ x, IsMIntegralCurve (fun t => Phi t x) V)
    (F : A → M) (hF : ContMDiff (𝓡 2) (𝓡 3) ∞ F)
    (z : A) (s : ℝ) (a : TangentSpace (𝓡 2) z) :
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
      (fun tz : ℝ × A => Phi tz.1 (F tz.2)) (0, z) (s, a) =
      s • V (F z) + mfderiv (𝓡 2) (𝓡 3) F z a := by
  let Q : ℝ × A → M := fun tz => Phi tz.1 (F tz.2)
  let DQ : (ℝ × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) Q (0, z)
  have hQ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ Q :=
    hPhi.comp (contMDiff_fst.prodMk (hF.comp contMDiff_snd))
  have ht : DQ (s, 0) =
      s • V (F z) := by
    have hin : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 2))
        (fun t : ℝ => (t, z)) 0 := mdifferentiableAt_id.prodMk mdifferentiableAt_const
    have hd := mfderiv_comp (0 : ℝ) ((hQ (0, z)).mdifferentiableAt (by simp)) hin
    have hi := mfderiv_prodMk
      (mdifferentiableAt_id (I := 𝓘(ℝ, ℝ)) (x := (0 : ℝ)))
      (mdifferentiableAt_const (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 2) (x := (0 : ℝ)) (c := z))
    rw [mfderiv_id, mfderiv_const] at hi
    simp only [id_eq] at hi
    rw [hi] at hd
    have hh := congrArg (fun L => L s) hd
    have hc := (hcurve (F z) 0).mfderiv
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun t => Phi t (F z)) 0 s = DQ (s, 0) at hh
    rw [hc] at hh
    change s • V (Phi 0 (F z)) = DQ (s, 0) at hh
    have hv := congrArg (fun x : M => (V x : EuclideanSpace ℝ (Fin 3))) (hzero (F z))
    rw [hv] at hh
    exact hh.symm
  have hx : DQ (0, a) =
      mfderiv (𝓡 2) (𝓡 3) F z a := by
    have hin : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2))
        (fun y : A => ((0 : ℝ), y)) z :=
      mdifferentiableAt_const.prodMk mdifferentiableAt_id
    have hd := mfderiv_comp z ((hQ (0, z)).mdifferentiableAt (by simp)) hin
    have hi := mfderiv_prodMk
      (mdifferentiableAt_const (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (x := z) (c := (0 : ℝ)))
      (mdifferentiableAt_id (I := 𝓡 2) (x := z))
    rw [mfderiv_const, mfderiv_id] at hi
    simp only [id_eq] at hi
    rw [hi] at hd
    have hh := congrArg (fun L => L a) hd
    change mfderiv (𝓡 2) (𝓡 3) (fun y => Phi 0 (F y)) z a = DQ (0, a) at hh
    have heq : (fun y : A => Phi 0 (F y)) = F := funext fun y => hzero (F y)
    rw [heq] at hh
    exact hh.symm
  have hsplit : (s, (a : EuclideanSpace ℝ (Fin 2))) =
      (s, (0 : EuclideanSpace ℝ (Fin 2))) + (0, a) := by simp
  change DQ (s, a) = _
  rw [hsplit, map_add, ht, hx]



theorem terminalCurvature_flow_sphere_bijective
    (V : (x : M) → TangentSpace (𝓡 3) x) (Phi : ℝ → M → M)
    (hzero : ∀ x, Phi 0 x = x)
    (hPhi : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
      (fun tx : ℝ × M => Phi tx.1 tx.2))
    (hcurve : ∀ x, IsMIntegralCurve (fun t => Phi t x) V)
    (F : A → M) (hF : ContMDiff (𝓡 2) (𝓡 3) ∞ F)
    (z : A) (hinj : Function.Injective (mfderiv (𝓡 2) (𝓡 3) F z))
    (hout : V (F z) ∉ range (mfderiv (𝓡 2) (𝓡 3) F z)) :
    Function.Bijective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
      (fun tz : ℝ × A => Phi tz.1 (F tz.2)) (0, z)) := by
  let L : (ℝ × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
    (fun tz : ℝ × A => Phi tz.1 (F tz.2)) (0, z)
  have hL : Function.Injective L := by
    apply (injective_iff_map_eq_zero L.toLinearMap).mpr
    rintro ⟨s, a⟩ hsa
    change L (s, a) = 0 at hsa
    rw [show L (s, a) = s • V (F z) + mfderiv (𝓡 2) (𝓡 3) F z a from
      terminalCurvature_flow_sphere_differential V Phi hzero hPhi hcurve F hF z s a] at hsa
    have hs : s = 0 := by
      by_contra hs
      apply hout
      refine ⟨(-s⁻¹) • a, ?_⟩
      have ha : mfderiv (𝓡 2) (𝓡 3) F z a = -(s • V (F z)) :=
        eq_neg_of_add_eq_zero_right hsa
      rw [map_smul, ha, smul_neg, smul_smul]
      simp only [neg_mul, inv_mul_cancel₀ hs, neg_one_smul, neg_neg]
    have ha : a = 0 := by
      apply hinj
      simpa only [hs, zero_smul, zero_add, map_zero] using hsa
    exact Prod.ext hs ha
  exact ⟨hL, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := L.toLinearMap) (by simp [Module.finrank_prod])).mp hL⟩

end PoincareConjecture.M47
