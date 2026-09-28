import PoincareConjecture.Proofs.M76.Rigidity.ParameterPrismProduct
import PoincareConjecture.Proofs.M76.Rigidity.ParameterFrontierOpenness
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PrescribedProductCorrection
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperProductOpenness

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "E" => (V2 × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "J" => Icc (-(1 / 4 : ℝ)) (1 / 4)
local notation "Jo" => Ioo (-(1 / 4 : ℝ)) (1 / 4)

theorem exists_corrected_parameter_product (B : E → E)
    (hB : FinitePiecewiseAffineOn B (Q ×ˢ J)) (hBi : InjOn B (Q ×ˢ J))
    (hBm : MapsTo B (Q ×ˢ J) (Q ×ˢ Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hBc : ∀ z ∈ Q, B (z, 0) = (z, 0))
    (hBo : IsOpen ((fun z : Q × ℝ => ((z.1 : V2), z.2)) ⁻¹'
      (B '' (Q ×ˢ Jo)))) :
    ∃ g : E → E, FinitePiecewiseAffineOn g (D ×ˢ J) ∧ InjOn g (D ×ˢ J) ∧
      MapsTo g (D ×ˢ J) (D ×ˢ Ioo (-1 : ℝ) 1) ∧
      (∀ z ∈ D ×ˢ J, (g z).1 ∈ Q ↔ z.1 ∈ Q) ∧
      (∀ z ∈ Q, ∀ t ∈ J, g (z, t) = B (z, t)) ∧
      (∀ z ∈ D, g (z, 0) = (z, 0)) ∧
      ∀ v : ℝ, 0 < v → v ≤ 1 / 4 →
        IsOpen ((Subtype.val : (D ×ˢ I : Set E) → E) ⁻¹'
          (g '' (D ×ˢ Ioo (-v) v))) := by
  let P := originalParameterPrismProduct
  have hBfront : MapsTo B (Q ×ˢ J) (frontier (D ×ˢ I)) := by
    intro z hz
    have hb := hBm hz
    rw [originalParameterPrism_frontier]
    exact Or.inl ⟨hb.1, by linarith [hb.2.1], by linarith [hb.2.2]⟩
  have hcenter (z : V2) (hz : z ∈ Q) : B (z, 0) = P.map (z, 0) := by
    rw [hBc z hz, originalParameterPrismProduct_map]
    simp only [mul_zero]
  have hopen : IsOpen ((Subtype.val : frontier (D ×ˢ I) → E) ⁻¹'
      (B '' (Q ×ˢ Jo))) := by
    apply isOpen_parameterPrism_frontier_of_lateral ?_ hBo
    rintro _ ⟨z, hz, rfl⟩
    have hb := hBm ⟨hz.1, Ioo_subset_Icc_self hz.2⟩
    exact ⟨hb.1, by linarith [hb.2.1], by linarith [hb.2.2]⟩
  have hband : MapsTo B (Q ×ˢ J) (P.map '' (D ×ˢ Ioo (-1 : ℝ) 1)) := by
    intro z hz
    have hb := hBm hz
    refine ⟨((B z).1, 2 * (B z).2), ⟨sphere_subset_closedBall hb.1, ?_⟩, ?_⟩
    · constructor <;> linarith [hb.2.1, hb.2.2]
    · rw [originalParameterPrismProduct_map]
      exact Prod.ext rfl (by ring)
  obtain ⟨g, hg, hgi, hgm, hgb, hgl, hgc⟩ :=
    HamiltonIndexOne.exists_prescribed_product_correction P
      originalParameterPrismBase_finitePL B hB hBi hBfront hcenter hopen
      (by norm_num : (0 : ℝ) < 1 / 4) le_rfl hband
  have htime : MapsTo g (D ×ˢ J) (D ×ˢ Ioo (-1 : ℝ) 1) := by
    intro z hz
    have hin := hgm hz
    refine ⟨hin.1, ?_⟩
    by_cases hzQ : z.1 ∈ Q
    · have heq : g z = B z := hgl z.1 hzQ z.2 hz.2
      rw [heq]
      have hb := hBm ⟨hzQ, hz.2⟩
      exact ⟨by linarith [hb.2.1], by linarith [hb.2.2]⟩
    · constructor
      · by_contra hn
        have ht : (g z).2 = -1 := le_antisymm (not_lt.mp hn) hin.2.1
        apply hzQ ((hgb z hz).mp ?_)
        rw [originalParameterPrism_frontier]
        exact Or.inr ⟨hin.1, Or.inl ht⟩
      · by_contra hn
        have ht : (g z).2 = 1 := le_antisymm hin.2.2 (not_lt.mp hn)
        apply hzQ ((hgb z hz).mp ?_)
        rw [originalParameterPrism_frontier]
        exact Or.inr ⟨hin.1, Or.inr ht⟩
  refine ⟨g, hg, hgi, htime, ?_, hgl, ?_, ?_⟩
  · intro z hz
    constructor
    · intro hq
      apply (hgb z hz).mp
      rw [originalParameterPrism_frontier]
      exact Or.inl ⟨hq, (hgm hz).2⟩
    · intro hq
      have heq : g z = B z := hgl z.1 hq z.2 hz.2
      rw [heq]
      exact (hBm ⟨hq, hz.2⟩).1
  · intro z hz
    exact hgc ⟨z, hz⟩
  · intro v hv hvsmall
    have hsub : D ×ˢ Icc (-v) v ⊆ D ×ˢ J := by
      intro z hz
      exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
    have hball := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
      (isFinitePLBallPair_Icc (show -v < v by linarith))
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKS, _⟩, _⟩, _⟩ := hball
    have hgv : FinitePiecewiseAffineOn g (D ×ˢ Icc (-v) v) :=
      hKS ▸ hg.restrict K hK (hKS.subset.trans hsub)
    exact HamiltonIndexOne.isOpen_image_proper_finitePL_product
      originalParameterPrismCoordinates plDomain_originalParameterPrism hv g hgv
      (hgi.mono hsub) (fun z hz => hgm (hsub hz)) (fun z hz => hgb z (hsub hz))

end PoincareConjecture.M76
