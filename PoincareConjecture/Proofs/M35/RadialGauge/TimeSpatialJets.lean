import PoincareConjecture.Proofs.M35.RadialGauge.TimeSpatialInterchange
import PoincareConjecture.Proofs.M35.RadialGauge.JointJetContinuity










set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem time_spatial_jets_interchange (k : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {u H : ℝ → V → F} {a b t : ℝ}
    (hu : ∀ s ∈ Ioo a b, ContDiff ℝ ∞ (u s))
    (hH : ∀ s ∈ Ioo a b, ContDiff ℝ ∞ (H s))
    (hc : Continuous (fun p : Ioo a b × V => H p.1.1 p.2))
    (hb : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Ioo a b, ∀ x,
      ‖iteratedFDeriv ℝ j (H s) x‖ ≤ C)
    (hPDE : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun q => u q x) (H s x) s)
    (ht : t ∈ Ioo a b) (x : V) :
    HasDerivAt (fun s => iteratedFDeriv ℝ k (u s) x)
      (iteratedFDeriv ℝ k (H t) x) t := by
  induction k generalizing F with
  | zero =>
      exact (continuousMultilinearCurryFin0 ℝ V F).symm.toContinuousLinearEquiv
        |>.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hPDE t ht x)
  | succ k ih =>
      have hdu (s : ℝ) (hs : s ∈ Ioo a b) :=
        (contDiff_infty_iff_fderiv.mp (hu s hs)).2
      have hdH (s : ℝ) (hs : s ∈ Ioo a b) :=
        (contDiff_infty_iff_fderiv.mp (hH s hs)).2
      have hdHb : ∀ j : ℕ, ∃ C : ℝ, ∀ s ∈ Ioo a b, ∀ y,
          ‖iteratedFDeriv ℝ j (fderiv ℝ (H s)) y‖ ≤ C := by
        intro j
        obtain ⟨C, hC⟩ := hb (j + 1)
        exact ⟨C, fun s hs y => by
          rw [norm_iteratedFDeriv_fderiv]
          exact hC s hs y⟩
      have hdc : Continuous (fun p : Ioo a b × V => fderiv ℝ (H p.1.1) p.2) :=
        spatial_fderiv_jointly_continuous_of_uniform_bounds
          (f := fun s : Ioo a b => H s.1) hc
          (fun s : Ioo a b => hH s.1 s.2) (fun j => by
            obtain ⟨C, hC⟩ := hb j
            exact ⟨C, fun s : Ioo a b => hC s.1 s.2⟩)
      obtain ⟨C, hC⟩ := hb 1
      have hdPDE (s : ℝ) (hs : s ∈ Ioo a b) (y : V) :
          HasDerivAt (fun q => fderiv ℝ (u q) y) (fderiv ℝ (H s) y) s :=
        time_fderiv_interchange hs
          (fun q hq => (hu q hq).differentiable (by simp)) hPDE
          (fun z => continuousOn_iff_continuous_domRestrict.mpr
            (hc.comp (continuous_id.prodMk continuous_const)))
          (fun z => continuousOn_iff_continuous_domRestrict.mpr
            (hdc.comp (continuous_id.prodMk continuous_const)))
          (fun q hq => (hH q hq).differentiable (by simp))
          (fun q hq z => by simpa only [norm_iteratedFDeriv_one] using hC q hq z) y
      have hd := ih hdu hdH hdc hdHb hdPDE
      have hh := (continuousMultilinearCurryRightEquiv' ℝ k V F).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hd
      simpa only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        Function.comp_def, iteratedFDeriv_succ_eq_comp_right] using hh

end PoincareConjecture.M35.RadialGauge
