import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.VariableModulusLowerContinuity
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusRadialFlip













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

local notation "O" => m64AnnulusLowerDomain
local notation "T" => m64AnnulusRadialFlip
local notation "U" => T ⁻¹' O
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S



theorem m64Annulus_upperDomain_coordinates (p : LoopPlane) :
    p ∈ U ↔ 0 < p 0 ∧ p 0 < curvePeriod ∧ 0 < p 1 ∧ p 1 < 2 := by
  change T p ∈ O ↔ _
  simp only [m64AnnulusLowerDomain, mem_ofPred_eq, m64AnnulusRadialFlip_apply,
    PiLp.add_apply, m60PlaneReflection_apply, annulusPoint, Matrix.cons_val_zero,
    Matrix.cons_val_one, ite_true, zero_add, show (1 : Fin 2) ≠ 0 from by decide, ite_false]
  constructor <;> rintro ⟨h0, hP, h1, h2⟩ <;> exact ⟨h0, hP, by linarith, by linarith⟩



theorem m64Annulus_radialDomains_inter : O ∩ U = S := by
  ext p
  rw [mem_inter_iff, m64Annulus_upperDomain_coordinates, m64AnnulusInterior_coordinates]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨hl.1, hl.2.1, hu.2.2.1, hl.2.2.2⟩
  · rintro ⟨h0, hP, h1, h2⟩
    exact ⟨⟨h0, hP, by linarith, h2⟩, ⟨h0, hP, h1, by linarith⟩⟩

namespace M64ObservedWeakAnnulus

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [CompactSpace M] [T2Space M]
  {e : M → EuclideanSpace ℝ (Fin m)} {c0 c1 : ℝ → M}

local notation "E" => EuclideanSpace ℝ (Fin m)



theorem weighted_upper_continuous_representative
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1) (hc1P : Function.Periodic c1 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v) {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus) :
    ∃ F : LoopPlane → M, ContinuousOn F U ∧ F =ᵐ[mu] A.map ∧
      ∀ x ∈ Ioo (0 : ℝ) curvePeriod, F (annulusPoint x 1) = c1 x := by
  obtain ⟨W, hmap, -, henergy⟩ := A.exists_radial_flip
  have hminW (B : M64ObservedWeakAnnulus (n := n) e c1 c0) :
      W.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus := by
    obtain ⟨Z, -, -, hZ⟩ := B.exists_radial_flip
    rw [henergy, ← hZ Q modulus]
    exact hmin Z
  obtain ⟨F, hF, hae, htrace⟩ := W.weighted_lower_continuous_representative
    g he hei hread hc1 hc1P Q hQ hpos hC hcoercive hmodulus hminW
  have hFS : F =ᵐ[mu] W.map := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset m64AnnulusLower_rect_subset hae,
      ae_restrict_mem isOpen_interior.measurableSet] with p hp hpS
    rw [hp, lowerExtensionMap, m64AnnulusLowerExtend_right _ _ hpS]
  refine ⟨F ∘ T, hF.comp m64AnnulusRadialFlip.continuous.continuousOn
    (fun _ hp => hp), ?_, ?_⟩
  · filter_upwards [m64AnnulusRadialFlip_restrict_measurePreserving.quasiMeasurePreserving.ae hFS]
      with p hp
    change F (T p) = A.map p
    rw [hp, hmap, Function.comp_apply, m64AnnulusRadialFlip_involutive p]
  · intro x hx
    simpa only [Function.comp_apply, m64AnnulusRadialFlip_point, sub_self] using htrace x hx





theorem weighted_radial_continuous_representative
    (A : M64ObservedWeakAnnulus (n := n) e c0 c1)
    (g : RiemannianMetric n M) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (hei : IsClosedEmbedding e) (hread : M60.SUChartReadable (n := n) e)
    (hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c0) (hc0P : Function.Periodic c0 curvePeriod)
    (hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 c1) (hc1P : Function.Periodic c1 curvePeriod)
    (Q : M → E →L[ℝ] E →L[ℝ] ℝ) (hQ : Continuous Q)
    (hpos : ∀ q v, 0 ≤ Q q v v) {C : ℝ} (hC : 0 ≤ C)
    (hcoercive : ∀ (q : M) (v : E), v ∈ range (mfderiv (𝓡 n) (𝓡 m) e q) →
      ‖v‖ ^ 2 ≤ C * Q q v v) {modulus : ℝ} (hmodulus : 0 < modulus)
    (hmin : ∀ B : M64ObservedWeakAnnulus (n := n) e c0 c1,
      A.weightedEnergy Q modulus ≤ B.weightedEnergy Q modulus) :
    ∃ F : LoopPlane → M, ContinuousOn F (O ∪ U) ∧ F =ᵐ[mu] A.map ∧
      (∀ x ∈ Ioo (0 : ℝ) curvePeriod, F (annulusPoint x 0) = c0 x) ∧
      ∀ x ∈ Ioo (0 : ℝ) curvePeriod, F (annulusPoint x 1) = c1 x := by
  classical
  obtain ⟨F0, hF0, hF0ae, htrace0⟩ := A.weighted_lower_continuous_representative
    g he hei hread hc0 hc0P Q hQ hpos hC hcoercive hmodulus hmin
  obtain ⟨F1, hF1, hF1ae, htrace1⟩ := A.weighted_upper_continuous_representative
    g he hei hread hc1 hc1P Q hQ hpos hC hcoercive hmodulus hmin
  have hSO : S ⊆ O := m64AnnulusLower_rect_subset
  have hSU : S ⊆ U := by
    rw [← m64Annulus_radialDomains_inter]
    exact inter_subset_right
  have hF0S : F0 =ᵐ[mu] A.map := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hSO hF0ae,
      ae_restrict_mem isOpen_interior.measurableSet] with p hp hpS
    rw [hp, lowerExtensionMap, m64AnnulusLowerExtend_right _ _ hpS]
  have heq : EqOn F0 F1 S := Measure.eqOn_open_of_ae_eq
    (hF0S.trans hF1ae.symm) isOpen_interior (hF0.mono hSO) (hF1.mono hSU)
  let F := m64AnnulusLowerDomain.piecewise F0 F1
  have h0 : EqOn F F0 O := fun p hp => piecewise_eq_of_mem O F0 F1 hp
  have h1 : EqOn F F1 U := by
    intro p hp
    by_cases hpO : p ∈ O
    · rw [h0 hpO]
      apply heq
      rw [← m64Annulus_radialDomains_inter]
      exact ⟨hpO, hp⟩
    · exact piecewise_eq_of_notMem O F0 F1 hpO
  refine ⟨F, (hF0.congr h0).union_of_isOpen (hF1.congr h1)
    m64AnnulusLowerDomain_isOpen
    (m64AnnulusLowerDomain_isOpen.preimage m64AnnulusRadialFlip.continuous), ?_, ?_, ?_⟩
  · filter_upwards [hF0S, ae_restrict_mem isOpen_interior.measurableSet] with p hp hpS
    exact (h0 (hSO hpS)).trans hp
  · intro x hx
    have hp : annulusPoint x 0 ∈ O :=
      ⟨hx.1, hx.2, by norm_num [annulusPoint], by norm_num [annulusPoint]⟩
    exact (h0 hp).trans (htrace0 x hx)
  · intro x hx
    have hp : annulusPoint x 1 ∈ U := (m64Annulus_upperDomain_coordinates _).mpr
      ⟨hx.1, hx.2, by norm_num [annulusPoint], by norm_num [annulusPoint]⟩
    exact (h1 hp).trans (htrace1 x hx)

end M64ObservedWeakAnnulus
end PoincareConjecture
