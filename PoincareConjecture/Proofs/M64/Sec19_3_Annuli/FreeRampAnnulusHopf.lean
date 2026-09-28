import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeRampInteriorImmersion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MinimalAnnulusAreaStationarity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamGeometry














set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

private theorem annulusInterior_of_mem_interior {p : LoopPlane}
    (hp : p ∈ interior m64AnnulusDomain) : p ∈ m64AnnulusInterior := by
  have hc := (m64AnnulusInterior_coordinates p).mp hp
  change ∀ i : Fin 2, i ∈ (univ : Set (Fin 2)) →
    p i ∈ Ioo ((0 : Fin 2 → ℝ) i) (![curvePeriod, 1] i)
  intro i _
  fin_cases i
  · exact ⟨hc.1, hc.2.1⟩
  · exact hc.2.2

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

variable (P : M62.CircleProductData F circumference) (hcirc : 0 < circumference) (t : ℝ)
  {c0 c1 : ℝ → P.charts.Point}
  (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 c0)
  (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 c1)
  (hp0 : Function.Periodic c0 curvePeriod) (hp1 : Function.Periodic c1 curvePeriod)
  (hr0 : M63IsRampAt P c0 t) (hr1 : M63IsRampAt P c1 t)
  (sigma0 sigma1 : M64PeriodicDegreeOneLift)
  (A : M64Annulus (P.flow.metric t) (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
  {r : ℝ} (hr : 0 < r)
  (hminimum : A.area = m64LeastAnnulusArea (P.flow.metric t)
    (c0 ∘ sigma0.map) (c1 ∘ sigma1.map))
  (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
    r * m60AreaGram (P.flow.metric t) A.map p 0 0 =
        r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1 ∧
      m60AreaGram (P.flow.metric t) A.map p 0 1 = 0)
  (hA : ∀ p ∈ m64AnnulusDomain,
    ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ A.map p)

include hcirc hc0 hc1 hp0 hp1 hr0 hr1 hr hminimum hconformal hA





theorem m64FreeRampModulusMinimum_branchSet_empty : m64AnnulusBranchSet A = ∅ := by
  have hi := m64FreeRampModulusMinimum_mfderiv_injective P hcirc t hc0 hc1 hp0 hp1
    hr0 hr1 sigma0 sigma1 A hr hminimum hconformal hA
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hinj := hi p (annulusInterior_of_mem_interior hp.1)
  have he : (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : LoopPlane) = 0 := by
    apply hinj
    rw [hp.2]
    rfl
  have hcoord := congrArg (fun z : LoopPlane => z 0) he
  norm_num at hcoord





theorem m64FreeRampModulusMinimum_branchAwareFirstVariation :
    M64AnnulusBranchAwareFirstVariationCertificate A := by
  let : Fact (0 < circumference) := ⟨hcirc⟩
  have hi := m64FreeRampModulusMinimum_mfderiv_injective P hcirc t hc0 hc1 hp0 hp1
    hr0 hr1 sigma0 sigma1 A hr hminimum hconformal hA
  have hempty := m64FreeRampModulusMinimum_branchSet_empty P hcirc t hc0 hc1 hp0 hp1
    hr0 hr1 sigma0 sigma1 A hr hminimum hconformal hA
  have hcuts : M64PiecewiseC1Annulus A := by
    let cut : Fin (1 + 1) → ℝ := fun i => (i : ℝ) * curvePeriod
    have hcut : StrictMono cut := by
      intro i j hij
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hij)
        (by unfold curvePeriod; positivity)
    apply m64PiecewiseC1Annulus_of_cuts A (by norm_num) cut hcut (by simp [cut])
      (by simp [cut])
    intro j p hp
    have hj : j = 0 := Fin.eq_zero j
    subst j
    have hpdom : p ∈ m64AnnulusDomain := by
      change 0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1
      simpa [cut] using hp
    exact ((hA p hpdom).of_le (by simp)).contMDiffWithinAt
  exact {
    regularity := {
      piecewise_c1 := hcuts
      interior_smooth := fun p hp => (hA p (interior_subset hp)).contMDiffWithinAt }
    area_stationary := m64AnnulusAreaStationary_of_modulus_conformal_minimum
      A hr hminimum hconformal
    finite_branch_set := by rw [hempty]; exact finite_empty
    injective_off_branch_set := fun p hp _ => hi p (annulusInterior_of_mem_interior hp) }

end PoincareConjecture
