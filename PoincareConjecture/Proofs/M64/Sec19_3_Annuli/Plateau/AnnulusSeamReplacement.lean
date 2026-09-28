import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamPatchIntegration

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
local notation "O" => m64AnnulusSeamDomain
local notation "mu" => volume.restrict S
local notation "v" => m64AnnulusSeamTranslation

theorem m64RectangleTest_periodic_of_support {phi : LoopPlane → ℝ}
    (hs : tsupport phi ⊆ S) (s : ℝ) :
    phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s) := by
  have hright : phi (annulusPoint curvePeriod s) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => by
      have hlt := ((m64AnnulusInterior_coordinates _).mp (hs h)).2.1
      simp only [annulusPoint, Matrix.cons_val_zero, lt_self_iff_false] at hlt
  have hleft : phi (annulusPoint 0 s) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => by
      have hlt := ((m64AnnulusInterior_coordinates _).mp (hs h)).1
      simp only [annulusPoint, Matrix.cons_val_zero, lt_self_iff_false] at hlt
  rw [hright, hleft]

theorem M64ObservedWeakAnnulus.seam_replace
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    {K : Set LoopPlane} (hK : MeasurableSet K) (hKO : K ⊆ O)
    (hsep : Disjoint K ((fun p : LoopPlane => p - v) ⁻¹' K))
    (f : LoopPlane → M) (V : Fin 2 → LoopPlane → E)
    (hf : MemLp (e ∘ f) 2 (volume.restrict K))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict K))
    (ht : ∀ i, ∀ᵐ p ∂volume.restrict K,
      V i p ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f p)))
    (hgreen : ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi → ∀ i : Fin 2,
      (i = 1 ∨ ∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in K, m64AnnulusSeamExtend phi p • V i p) +
        (∫ p in K,
          m64AnnulusSeamExtend (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p • e (f p)) =
      (∫ p in K, m64AnnulusSeamExtend phi p •
        m64AnnulusSeamExtend (A.column i : LoopPlane → E) p) +
        (∫ p in K,
          m64AnnulusSeamExtend (fun q => fderiv ℝ phi q (EuclideanSpace.single i 1)) p •
            e (m64AnnulusSeamExtend A.map p))) :
    ∃ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      B.map = m64AnnulusSeamPatch K f A.map ∧
      ∀ i, (B.column i : LoopPlane → E) =ᵐ[mu]
        m64AnnulusSeamPatch K (V i) (A.column i) := by
  classical
  let F := m64AnnulusSeamPatch K f A.map
  let D := fun i => m64AnnulusSeamPatch K (V i) (A.column i)
  have hFe : e ∘ F = m64AnnulusSeamPatch K (e ∘ f) (e ∘ A.map) :=
    m64AnnulusSeamPatch_comp K f A.map e
  have hFl : MemLp (e ∘ F) 2 mu := by
    rw [hFe]
    exact m64AnnulusSeamPatch_memLp hK hKO hsep hf A.observed_memLp
  have hDl (i : Fin 2) : MemLp (D i) 2 mu :=
    m64AnnulusSeamPatch_memLp hK hKO hsep (hV i) (Lp.memLp (A.column i))
  let column := fun i => (hDl i).toLp (D i)
  have hcoe (i : Fin 2) : (column i : LoopPlane → E) =ᵐ[mu] D i := (hDl i).coeFn_toLp
  have hflux (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) (i : Fin 2)
      (htest : i = 1 ∨ ∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
      (∫ p in S, phi p • column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (F p)) =
      (∫ p in S, phi p • A.column i p) +
        (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • e (A.map p)) := by
    have hc := (hphi.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i 1))
    have hgreen' := hgreen phi hphi i htest
    have hext (p : LoopPlane) : e (m64AnnulusSeamExtend A.map p) =
        m64AnnulusSeamExtend (e ∘ A.map) p := congrFun (m64AnnulusSeamExtend_comp A.map e) p
    simp_rw [hext] at hgreen'
    have hh := m64AnnulusSeamPatch_flux hK hKO hsep (e ∘ A.map) (e ∘ f)
      (A.column i) (V i) phi (fun p => fderiv ℝ phi p (EuclideanSpace.single i 1))
      A.observed_memLp hf (Lp.memLp (A.column i)) (hV i)
      (m64Annulus_continuous_memLp_two hphi.continuous)
      (m64Annulus_continuous_memLp_two hc) hgreen'
    have hdint : (∫ p in S, phi p • column i p) = ∫ p in S, phi p • D i p :=
      integral_congr_ae ((hcoe i).mono fun p hp => congrArg (fun w : E => phi p • w) hp)
    rw [hdint]
    rw [← hFe] at hh
    simpa only [Function.comp_def, D] using hh
  let B : M64ObservedWeakAnnulus (n := n) e c0 c1 := {
    map := F
    observed_memLp := hFl
    column := column
    tangent := fun i => by
      have hlocal := (ae_restrict_iff' hK).mp (ht i)
      have htrans := measurePreserving_add_right (volume : Measure LoopPlane) (-v)
      have hshift := htrans.quasiMeasurePreserving.ae hlocal
      filter_upwards [hcoe i, ae_restrict_of_ae hlocal, ae_restrict_of_ae hshift, A.tangent i]
        with p hp hl hshift ha
      rw [hp]
      change m64AnnulusSeamPatch K (V i) (A.column i) p ∈
        range (mfderiv (𝓡 n) (𝓡 m) e (m64AnnulusSeamPatch K f A.map p))
      by_cases hpK : p ∈ K
      · have hFp : m64AnnulusSeamPatch K f A.map p = f p := by
          simp only [m64AnnulusSeamPatch, if_pos hpK]
        rw [hFp]
        simpa only [m64AnnulusSeamPatch, if_pos hpK] using hl hpK
      · by_cases hqK : p - v ∈ K
        · have hFp : m64AnnulusSeamPatch K f A.map p = f (p - v) := by
            simp only [m64AnnulusSeamPatch, if_neg hpK, if_pos hqK]
          rw [hFp]
          have hq : V i (p - v) ∈ range (mfderiv (𝓡 n) (𝓡 m) e (f (p - v))) := by
            rw [sub_eq_add_neg p v]
            exact hshift (by simpa only [sub_eq_add_neg] using hqK)
          simpa only [m64AnnulusSeamPatch, if_neg hpK, if_pos hqK] using hq
        · have hFp : m64AnnulusSeamPatch K f A.map p = A.map p := by
            simp only [m64AnnulusSeamPatch, if_neg hpK, if_neg hqK]
          rw [hFp]
          simpa only [m64AnnulusSeamPatch, if_neg hpK, if_neg hqK] using ha
    weak_partial := fun i b => by
      intro phi hphi hc hs
      have hp := m64Annulus_continuous_memLp_two hphi.continuous
      have hq := m64Annulus_continuous_memLp_two
        ((hphi.continuous_fderiv (by simp)).clm_apply
          (continuous_const (y := EuclideanSpace.single i 1)))
      let L := EuclideanSpace.proj (𝕜 := ℝ) b
      have hproj (w : LoopPlane → E) (hw : MemLp w 2 mu)
          (theta : LoopPlane → ℝ) (htheta : MemLp theta 2 mu) :
          L (∫ p in S, theta p • w p) = ∫ p in S, theta p * w p b := by
        simpa only [map_smul, smul_eq_mul, L, EuclideanSpace.coe_proj] using
          (L.integral_comp_comm (m64L2_test_integrable hw htheta)).symm
      have hh := congrArg L (hflux phi (hphi.of_le (by simp)) i
        (Or.inr fun s _ => m64RectangleTest_periodic_of_support hs s))
      simp only [map_add] at hh
      rw [hproj (column i) (Lp.memLp (column i)) phi hp,
        hproj (fun p => e (F p)) hFl _ hq,
        hproj (A.column i) (Lp.memLp (A.column i)) phi hp,
        hproj (fun p => e (A.map p)) A.observed_memLp _ hq] at hh
      have hold := A.weak_partial i b phi hphi hc hs
      simp only [mul_comm] at hh hold ⊢
      linarith
    boundary := fun phi hphi => (hflux phi hphi 1 (Or.inl rfl)).trans (A.boundary phi hphi)
    seam := fun phi hphi hseam =>
      (hflux phi hphi 0 (Or.inr hseam)).trans (A.seam phi hphi hseam) }
  exact ⟨B, rfl, hcoe⟩

end PoincareConjecture
