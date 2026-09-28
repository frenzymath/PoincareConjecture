import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakReplacementFlux











set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S




theorem M64ObservedWeakAnnulus.replace
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {K : Set LoopPlane} [DecidablePred (· ∈ K)] (hK : MeasurableSet K) (hKS : K ⊆ S)
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict K))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict K,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hgreen : ∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (∫ p in K, phi p • V i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (f p)) =
      (∫ p in K, phi p • A.column i p) +
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.map p))) :
    ∃ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      B.map = K.piecewise f A.map ∧
      ∀ i, (B.column i : LoopPlane → E) =ᵐ[mu] K.piecewise (V i) (A.column i) := by
  classical
  let F := K.piecewise f A.map
  let D := fun i => K.piecewise (V i) (A.column i)
  have hFe : e ∘ F = K.piecewise (e ∘ f) (e ∘ A.map) := by
    funext p
    by_cases hp : p ∈ K <;> simp [F, hp]
  have hFl : MemLp (e ∘ F) 2 mu := by
    rw [hFe]
    exact m64MemLp_piecewise_of_subset hK hKS hf A.observed_memLp
  have hDl (i : Fin 2) : MemLp (D i) 2 mu :=
    m64MemLp_piecewise_of_subset hK hKS (hV i) (Lp.memLp (A.column i))
  let column := fun i => (hDl i).toLp (D i)
  have hcoe (i : Fin 2) : (column i : LoopPlane → E) =ᵐ[mu] D i :=
    (hDl i).coeFn_toLp
  have hflux (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2) :
      (∫ p in S, phi p • column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (F p)) =
      (∫ p in S, phi p • A.column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.map p)) := by
    have hc := (hphi.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1))
    have hh := m64WeakReplacement_flux hK hKS (e ∘ A.map) (e ∘ f)
      (A.column i) (V i) phi (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1))
      A.observed_memLp hf (Lp.memLp (A.column i)) (hV i)
      (m64Annulus_continuous_memLp_two hphi.continuous)
      (m64Annulus_continuous_memLp_two hc) (hgreen phi hphi i)
    have hdint : (∫ p in S, phi p • column i p) = ∫ p in S, phi p • D i p :=
      integral_congr_ae ((hcoe i).mono fun p hp => congrArg (fun v : E => phi p • v) hp)
    rw [hdint]
    rw [← hFe] at hh
    simpa +instances only [Function.comp_def, D] using! hh
  let B : M64ObservedWeakAnnulus (n := n) e c0 c1 := {
    map := F
    observed_memLp := hFl
    column := column
    tangent := fun i => by
      have hlocal := (ae_restrict_iff' hK).mp (ht i)
      filter_upwards [hcoe i, ae_restrict_of_ae hlocal, A.tangent i] with p hp hl ha
      rw [hp]
      by_cases hpK : p ∈ K
      · have hFp : F p = f p := piecewise_eq_of_mem K f A.map hpK
        rw [hFp]
        simpa only [D, piecewise_eq_of_mem _ _ _ hpK] using hl hpK
      · have hFp : F p = A.map p := piecewise_eq_of_notMem K f A.map hpK
        rw [hFp]
        simpa only [D, piecewise_eq_of_notMem _ _ _ hpK] using ha
    weak_partial := fun i b => by
      intro phi hphi hc hs
      have hp := m64Annulus_continuous_memLp_two hphi.continuous
      have hq := m64Annulus_continuous_memLp_two
        ((hphi.continuous_fderiv (by simp)).clm_apply
          (continuous_const (y := EuclideanSpace.single i 1)))
      let L := EuclideanSpace.proj (𝕜 := ℝ) b
      have hproj (v : LoopPlane → E) (hv : MemLp v 2 mu)
          (theta : LoopPlane → ℝ) (htheta : MemLp theta 2 mu) :
          L (∫ p in S, theta p • v p) = ∫ p in S, theta p * v p b := by
        simpa only [map_smul, smul_eq_mul, L, EuclideanSpace.coe_proj] using
          (L.integral_comp_comm (m64L2_test_integrable hv htheta)).symm
      have hh := congrArg L (hflux phi (hphi.of_le (by simp)) i)
      simp only [map_add] at hh
      rw [hproj (column i) (Lp.memLp (column i)) phi hp,
        hproj (fun p => e (F p)) hFl _ hq,
        hproj (A.column i) (Lp.memLp (A.column i)) phi hp,
        hproj (fun p => e (A.map p)) A.observed_memLp _ hq] at hh
      have hold := A.weak_partial i b phi hphi hc hs
      simp only [mul_comm] at hh hold ⊢
      linarith
    boundary := fun phi hphi => (hflux phi hphi 1).trans (A.boundary phi hphi)
    seam := fun phi hphi hseam => (hflux phi hphi 0).trans (A.seam phi hphi hseam) }
  exact ⟨B, rfl, hcoe⟩

end PoincareConjecture
