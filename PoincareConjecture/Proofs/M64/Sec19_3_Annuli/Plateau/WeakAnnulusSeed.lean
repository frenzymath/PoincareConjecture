import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicGreenIdentity












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem m64ObservedWeakAnnulus_of_contMDiff
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) (hA : ContMDiff (𝓡 2) (𝓡 n) 1 A.map)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e c0 c1, W.map = A.map ∧
      ∀ i, ∀ᵐ p ∂mu, W.column i p =
        fderiv ℝ (e ∘ A.map) p (EuclideanSpace.single i 1) := by
  let f : LoopPlane → E := e ∘ A.map
  have hf : ContDiff ℝ 1 f := contMDiff_iff_contDiff.mp (he.comp hA)
  let D : Fin 2 → LoopPlane → E := fun i p =>
    fderiv ℝ f p (EuclideanSpace.single i 1)
  have hD (i : Fin 2) : Continuous (D i) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hvalue : MemLp f 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm hf.continuous.aestronglyMeasurable).mpr
    exact (hf.continuous.norm.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hcolumn (i : Fin 2) : MemLp (D i) 2 mu := by
    apply (memLp_two_iff_integrable_sq_norm (hD i).aestronglyMeasurable).mpr
    exact ((hD i).norm.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  let column : Fin 2 → Lp E 2 mu := fun i => (hcolumn i).toLp (D i)
  have hcoe (i : Fin 2) : column i =ᵐ[mu] D i := (hcolumn i).coeFn_toLp
  have htangent (i : Fin 2) (p : LoopPlane) :
      D i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (A.map p)) := by
    refine ⟨mfderiv (𝓡 2) (𝓡 n) A.map p (EuclideanSpace.single i 1), ?_⟩
    have hc := mfderiv_comp p (he.mdifferentiable (by simp) _)
      (hA.mdifferentiable (by simp) _)
    have hd := congrArg (fun L => L (EuclideanSpace.single i 1)) hc
    rw [mfderiv_eq_fderiv] at hd
    exact hd.symm
  have hpartial (i : Fin 2) (b : Fin m) :
      HasWeakPartialDeriv i (fun p => D i p b) (fun p => f p b) S := by
    let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) b
    have hb : ContDiff ℝ 1 (fun p => f p b) := P.contDiff.comp hf
    have hweak := HasWeakPartialDeriv.of_contDiff (Ω := S) isOpen_interior (i := i) hb
    have hd : (fun p => fderiv ℝ (fun q => f q b) p (EuclideanSpace.single i 1)) =
        fun p => D i p b := by
      funext p
      have hh := (P.hasFDerivAt.comp p (hf.differentiable (by simp) p).hasFDerivAt).fderiv
      exact congrArg (fun L => L (EuclideanSpace.single i 1)) hh
    rwa [hd] at hweak
  let W : M64ObservedWeakAnnulus (n := n) e c0 c1 := {
    map := A.map
    observed_memLp := hvalue
    column := column
    tangent := fun i => (hcoe i).mono (fun p hp => hp ▸ htangent i p)
    weak_partial := fun i b => m64WeakPartialDeriv_ae_congr EventuallyEq.rfl
      ((hcoe i).symm.mono (fun p hp => congrArg (fun v : E => v b) hp)) (hpartial i b)
    boundary := by
      intro phi hphi
      have hh := m64Annulus_vertical_green_identity hf hphi
      have heq : (∫ p in S, phi p • column 1 p) = ∫ p in S, phi p • D 1 p :=
        integral_congr_ae ((hcoe 1).mono fun p hp => congrArg (fun v : E => phi p • v) hp)
      rw [heq]
      simpa only [D, f, Function.comp_apply, A.upper_boundary, A.lower_boundary] using hh
    seam := by
      intro phi hphi hseam
      have heq : (∫ p in S, phi p • column 0 p) = ∫ p in S, phi p • D 0 p :=
        integral_congr_ae ((hcoe 0).mono fun p hp => congrArg (fun v : E => phi p • v) hp)
      rw [heq]
      exact m64Annulus_periodic_green_identity hf hphi
        (fun x s => congrArg e (A.periodic x s)) hseam }
  exact ⟨W, rfl, hcoe⟩

end PoincareConjecture
