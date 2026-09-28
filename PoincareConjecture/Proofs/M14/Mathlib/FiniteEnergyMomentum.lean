import PoincareConjecture.Proofs.M08.EndpointMomentum
import PoincareConjecture.Proofs.M08.ChartRegularity
import Mathlib.Analysis.ODE.PicardLindelof

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology intervalIntegral

namespace ODE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem contDiffOn_of_finite_energy_momentum {a b : ℝ} (hab : a < b)
    {S : Set E} (A : ℝ × E → E →L[ℝ] E) (F : ℝ → E × E → E)
    (hA : ContDiffOn ℝ ∞ A (Icc a b ×ˢ S))
    (hunit : ∀ z ∈ Icc a b ×ˢ S, IsUnit (A z))
    (hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Icc a b ×ˢ (S ×ˢ univ)))
    (u d : ℝ → E) (hu : ContinuousOn u (Icc a b)) (hmem : MapsTo u (Icc a b) S)
    (hud : ∀ s ∈ Ioo a b, HasDerivAt u (d s) s)
    (hd : MemLp d 2 (volume.restrict (Icc a b)))
    (hQ : IntervalIntegrable (fun s => F s (u s, d s)) volume a b)
    (hPd : ∀ s ∈ Ioo a b, HasDerivAt (fun r => A (r, u r) (d r))
      (F s (u s, d s)) s) :
    ContDiffOn ℝ ∞ u (Icc a b) ∧ EqOn (derivWithin u (Icc a b)) d (Ioo a b) ∧
      ∀ s ∈ Icc a b,
        HasDerivWithinAt (fun r => A (r, u r) (derivWithin u (Icc a b) r))
          (F s (u s, derivWithin u (Icc a b) s)) (Icc a b) s := by
  let C := Icc a b
  let P := fun s => A (s, u s) (d s)
  let Q := fun s => F s (u s, d s)
  let B := fun s => Ring.inverse (A (s, u s))
  have hgraph : ContinuousOn (fun s => (s, u s)) C := continuousOn_id.prodMk hu
  have hgraphmem : MapsTo (fun s => (s, u s)) C (C ×ˢ S) :=
    fun _ hs => ⟨hs, hmem hs⟩
  have hB : ContinuousOn B C :=
    (PoincareConjecture.M08.contDiffOn_inverse_operator A hA hunit).continuousOn.comp hgraph hgraphmem
  have hinv (s : ℝ) (hs : s ∈ C) (v : E) : B s (A (s, u s) v) = v :=
    PoincareConjecture.M08.inverse_operator_apply _ (hunit _ (hgraphmem hs)) v
  obtain ⟨c, q, Pbar, hPbar, hq, hPc, hqc, hPeq, hqeq, _, hudbar, _⟩ :=
    PoincareConjecture.M08.endpoint_velocity_of_momentum hab u d P Q hu hud hd
      (fun s => A (s, u s)) B hB hinv (fun _ _ => rfl) hQ hPd
  let Qbar := fun s => F s (u s, q s)
  have hQbar : ContinuousOn Qbar C := hF.continuousOn.comp
    (continuousOn_id.prodMk (hu.prodMk hqc)) (fun _ hs => ⟨hs, hmem hs, mem_univ _⟩)
  have hQeq : EqOn Qbar Q (Ioo a b) := by
    intro s hs
    dsimp only [Qbar, Q]
    rw [hqeq hs]
  have hPdbar (s : ℝ) (hs : s ∈ C) : HasDerivWithinAt Pbar (Qbar s) C s := by
    rw [show Pbar = (fun r => c + ∫ t in a..r, Q t) from funext hPbar]
    exact PoincareConjecture.M08.endpoint_momentum_derivative_of_continuous_force
      hab c Q Qbar hQeq hQbar s hs
  let phase := fun t (z : E × E) =>
    let v := Ring.inverse (A (t, z.1)) z.2
    (v, F t (z.1, v))
  let Ω := C ×ˢ (S ×ˢ (univ : Set E))
  let k := fun z : ℝ × (E × E) => (z.1, z.2.1)
  have hk : ContDiffOn ℝ ∞ k Ω := contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hmap : MapsTo k Ω (C ×ˢ S) := fun _ hz => ⟨hz.1, hz.2.1⟩
  have hBinv := (PoincareConjecture.M08.contDiffOn_inverse_operator A hA hunit).comp hk hmap
  have hv := hBinv.clm_apply contDiffOn_snd.snd
  have hforce := hF.comp (contDiffOn_fst.prodMk (contDiffOn_snd.fst.prodMk hv))
    (fun _ hz => ⟨hz.1, hz.2.1, mem_univ _⟩)
  have hphase : ContDiffOn ℝ ∞ (Function.uncurry phase) Ω := hv.prodMk hforce
  have hinvq (s : ℝ) : Ring.inverse (A (s, u s)) (Pbar s) = q s := (hq s).symm
  have hphaseDeriv (s : ℝ) (hs : s ∈ C) :
      HasDerivWithinAt (fun r => (u r, Pbar r)) (phase s (u s, Pbar s)) C s := by
    simpa only [phase, hinvq s, Qbar] using (hudbar s hs).prodMk (hPdbar s hs)
  have hphaseMem : MapsTo (fun s => (u s, Pbar s)) C (S ×ˢ univ) :=
    fun _ hs => ⟨hmem hs, mem_univ _⟩
  have hsmooth := contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤)
    hphase hphaseDeriv hphaseMem
  have hqd (s : ℝ) (hs : s ∈ C) : derivWithin u C s = q s :=
    (hudbar s hs).derivWithin (uniqueDiffOn_Icc hab s hs)
  have hactualInterior : EqOn (fun s => A (s, u s) (q s)) Pbar (Ioo a b) := by
    intro s hs
    dsimp only
    rw [hqeq hs]
    exact (hPeq hs).symm
  have hactualClosed : EqOn (fun s => A (s, u s) (q s)) Pbar C :=
    hactualInterior.of_subset_closure
      ((hA.continuousOn.comp hgraph hgraphmem).clm_apply hqc) hPc Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
  have hactual : EqOn (fun s => A (s, u s) (derivWithin u C s)) Pbar C := by
    intro s hs
    dsimp only
    rw [hqd s hs]
    exact hactualClosed hs
  refine ⟨hsmooth.fst, fun s hs => (hqd s (Ioo_subset_Icc_self hs)).trans (hqeq hs), ?_⟩
  intro s hs
  rw [hqd s hs]
  exact (hPdbar s hs).congr_of_mem (fun _ hr => hactual hr) hs

end ODE
