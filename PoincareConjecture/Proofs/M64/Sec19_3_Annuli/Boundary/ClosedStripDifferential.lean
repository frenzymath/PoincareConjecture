import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.PeriodicStripEquation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteConformality

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M64

local notation "S" => Set.ofPred (fun p : LoopPlane => p 1 ∈ Icc (0 : ℝ) 1)

theorem annulusClosedStrip_uniqueDiffOn : UniqueDiffOn ℝ S := by
  have hc : Convex ℝ S := (convex_Icc (0 : ℝ) 1).linear_preimage
    (EuclideanSpace.projₗ (1 : Fin 2))
  have hWS : m64AnnulusOpenStrip ⊆ S := fun _ hp => ⟨hp.1.le, hp.2.le⟩
  apply uniqueDiffOn_convex hc
  refine ⟨annulusPoint 0 (1 / 2), ?_⟩
  apply (interior_maximal hWS isOpen_m64AnnulusOpenStrip)
  constructor <;> norm_num [annulusPoint]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

omit [IsManifold (𝓡 n) ∞ M] in

theorem annulus_within_derivative_restrict {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f S) {p : LoopPlane} (hp : p ∈ m64AnnulusDomain) :
    mfderivWithin (𝓡 2) (𝓡 n) f m64AnnulusDomain p =
      mfderivWithin (𝓡 2) (𝓡 n) f S p :=
  mfderivWithin_subset (fun _ h => h.2.2)
    (m64AnnulusDomain_uniqueDiffOn p hp).uniqueMDiffWithinAt
    ((hf p hp.2.2).mdifferentiableWithinAt one_ne_zero)

omit [IsManifold (𝓡 n) ∞ M] in

theorem annulus_strip_derivative_translate {f : LoopPlane → M}
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f S) (T : LoopPlane) (hT : T 1 = 0)
    (hperiod : ∀ p, f (T + p) = f p) {p : LoopPlane} (hp : p ∈ S) :
    mfderivWithin (𝓡 2) (𝓡 n) f S (T + p) = mfderivWithin (𝓡 2) (𝓡 n) f S p := by
  have hmap : MapsTo (fun p : LoopPlane => T + p) S S := by
    intro q hq
    change (T + q) 1 ∈ Icc (0 : ℝ) 1
    simpa only [PiLp.add_apply, hT, zero_add] using (show q 1 ∈ Icc (0 : ℝ) 1 from hq)
  have hP : HasFDerivAt (fun q : LoopPlane => T + q) (ContinuousLinearMap.id ℝ LoopPlane) p :=
    (hasFDerivAt_id p).const_add T
  have hPd : MDifferentiableWithinAt (𝓡 2) (𝓡 2) (fun q : LoopPlane => T + q) S p :=
    hP.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  have hUD := annulusClosedStrip_uniqueDiffOn p hp
  have hder := mfderivWithin_comp p ((hf _ (hmap hp)).mdifferentiableWithinAt one_ne_zero)
    hPd hmap hUD.uniqueMDiffWithinAt
  have hPd' : mfderivWithin (𝓡 2) (𝓡 2) (fun q : LoopPlane => T + q) S p =
      ContinuousLinearMap.id ℝ LoopPlane := by
    rw [mfderivWithin_eq_fderivWithin]
    exact hP.hasFDerivWithinAt.fderivWithin hUD
  have hfunD : mfderivWithin (𝓡 2) (𝓡 n) (f ∘ fun q : LoopPlane => T + q) S p =
      mfderivWithin (𝓡 2) (𝓡 n) f S p :=
    mfderivWithin_congr_of_mem (fun q _ => hperiod q) hp
  have hall := hder.symm.trans hfunD
  erw [hPd'] at hall
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun L => L v) hall

theorem annulus_strip_derivative_representative (A : M64Annulus g c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S) {p : LoopPlane} (hp : p ∈ S) :
    ∃ q ∈ m64AnnulusDomain, A.map q = A.map p ∧
      mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain q =
        mfderivWithin (𝓡 2) (𝓡 n) A.map S p := by
  obtain ⟨k, q, hq, -, -, hpoint⟩ := annulus_periodic_representative p hp
  have hfun := annulus_periodic_integer_translate A.periodic k
  have hder := annulus_strip_derivative_translate hA (annulusPoint (k • curvePeriod) 0)
    rfl hfun hp
  have hvalue := hfun p
  rw [hpoint] at hder hvalue
  exact ⟨q, hq, hvalue, (annulus_within_derivative_restrict hA hq).trans hder⟩

theorem annulus_strip_within_injective (A : M64Annulus g c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hinj : ∀ p ∈ m64AnnulusDomain,
      Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map m64AnnulusDomain p)) :
    ∀ p ∈ S, Function.Injective (mfderivWithin (𝓡 2) (𝓡 n) A.map S p) := by
  intro p hp
  obtain ⟨q, hq, -, hd⟩ := annulus_strip_derivative_representative A hA hp
  simpa +instances only [hd] using! hinj q hq

theorem annulus_strip_within_conformal (A : M64Annulus g c0 c1) (r : ℝ)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map S)
    (hAi : ContMDiffOn (𝓡 2) (𝓡 n) ∞ A.map m64AnnulusInterior)
    (hconf : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0) :
    ∀ p ∈ S, let d := mfderivWithin (𝓡 2) (𝓡 n) A.map S p
      let b := EuclideanSpace.basisFun (Fin 2) ℝ
      r * g.inner (A.map p) (d (b 0)) (d (b 0)) =
          r⁻¹ * g.inner (A.map p) (d (b 1)) (d (b 1)) ∧
        g.inner (A.map p) (d (b 0)) (d (b 1)) = 0 := by
  have hclosed := m64AnnulusWithinGram_modulus_conformal A r
    (hA.mono (fun _ hp => hp.2.2)) hAi hconf
  intro p hp
  obtain ⟨q, hq, hvalue, hd⟩ := annulus_strip_derivative_representative A hA hp
  have hmetric (v w : LoopPlane) :
      g.inner (A.map q) (mfderivWithin (𝓡 2) (𝓡 n) A.map S p v)
        (mfderivWithin (𝓡 2) (𝓡 n) A.map S p w) =
      g.inner (A.map p) (mfderivWithin (𝓡 2) (𝓡 n) A.map S p v)
        (mfderivWithin (𝓡 2) (𝓡 n) A.map S p w) :=
    congrArg (fun y : M => g.inner y (mfderivWithin (𝓡 2) (𝓡 n) A.map S p v)
      (mfderivWithin (𝓡 2) (𝓡 n) A.map S p w)) hvalue
  have hgram (i j : Fin 2) : m64AnnulusWithinGram g A.map q i j =
      g.inner (A.map p)
        (mfderivWithin (𝓡 2) (𝓡 n) A.map S p (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderivWithin (𝓡 2) (𝓡 n) A.map S p (EuclideanSpace.basisFun (Fin 2) ℝ j)) := by
    simpa +instances only [m64AnnulusWithinGram, hd] using!
      hmetric (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j)
  simpa only [hgram] using hclosed q hq

end PoincareConjecture.M64
