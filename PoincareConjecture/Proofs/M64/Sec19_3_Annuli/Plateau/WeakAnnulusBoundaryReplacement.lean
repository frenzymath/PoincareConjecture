import PoincareConjecture.Proofs.M64.Mathlib.WeakReplacementFluxDefect
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 d0 d1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "I" => Icc (0 : ℝ) curvePeriod

theorem M64ObservedWeakAnnulus.replace_boundary
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
        (∫ p in K, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.map p)) +
      if i = 1 then
        (∫ x in I, phi (annulusPoint x 1) • e (d1 x) -
          phi (annulusPoint x 0) • e (d0 x)) -
        (∫ x in I, phi (annulusPoint x 1) • e (c1 x) -
          phi (annulusPoint x 0) • e (c0 x)) else 0) :
    ∃ B : M64ObservedWeakAnnulus (n := n) e d0 d1,
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
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.map p)) +
      if i = 1 then
        (∫ x in I, phi (annulusPoint x 1) • e (d1 x) -
          phi (annulusPoint x 0) • e (d0 x)) -
        (∫ x in I, phi (annulusPoint x 1) • e (c1 x) -
          phi (annulusPoint x 0) • e (c0 x)) else 0 := by
    have hc := (hphi.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1))
    have hh := m64WeakReplacement_flux_defect hK hKS (e ∘ A.map) (e ∘ f)
      (A.column i) (V i) phi (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1))
      _ A.observed_memLp hf (Lp.memLp (A.column i)) (hV i)
      (m64Annulus_continuous_memLp_two hphi.continuous)
      (m64Annulus_continuous_memLp_two hc) (hgreen phi hphi i)
    have hdint : (∫ p in S, phi p • column i p) = ∫ p in S, phi p • D i p :=
      integral_congr_ae ((hcoe i).mono fun p hp => congrArg (fun v : E => phi p • v) hp)
    rw [hdint]
    rw [← hFe] at hh
    simpa +instances only [Function.comp_def, D] using! hh
  let B : M64ObservedWeakAnnulus (n := n) e d0 d1 := {
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
      have hz {p : LoopPlane} (h : p ∉ S) : phi p = 0 :=
        image_eq_zero_of_notMem_tsupport (fun ht => h (hs ht))
      have hlo (x : ℝ) : phi (annulusPoint x 0) = 0 := hz (by
        intro h
        exact lt_irrefl (0 : ℝ) ((m64AnnulusInterior_coordinates _).mp h).2.2.1)
      have hhi (x : ℝ) : phi (annulusPoint x 1) = 0 := hz (by
        intro h
        exact lt_irrefl (1 : ℝ) ((m64AnnulusInterior_coordinates _).mp h).2.2.2)
      have hh := hflux phi (hphi.of_le (by simp)) i
      simp only [hlo, hhi, zero_smul, sub_self, integral_zero, ite_self, add_zero] at hh
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
      have hscalar := congrArg L hh
      simp only [map_add] at hscalar
      rw [hproj (column i) (Lp.memLp (column i)) phi hp,
        hproj (fun p => e (F p)) hFl _ hq,
        hproj (A.column i) (Lp.memLp (A.column i)) phi hp,
        hproj (fun p => e (A.map p)) A.observed_memLp _ hq] at hscalar
      have hold := A.weak_partial i b phi hphi hc hs
      simp only [mul_comm] at hscalar hold ⊢
      linarith
    boundary := fun phi hphi => by
      have hh := hflux phi hphi 1
      simp only [ite_true] at hh
      rw [A.boundary phi hphi] at hh
      exact hh.trans (by abel)
    seam := fun phi hphi hs => by
      have hh := hflux phi hphi 0
      simpa using hh.trans (by simpa using A.seam phi hphi hs) }
  exact ⟨B, rfl, hcoe⟩

end PoincareConjecture
