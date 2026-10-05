import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Spheres.Mathlib.TwoFootSphereReplacement
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Levels.Mathlib.TwoFootHeightCarrier
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Spheres.Mathlib.FinitePLCubeSphereModel
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Spheres.OriginalFinitePLSphereImage

/-!
# The exact original sphere from the constructed two-foot geometry

Apply the whole finite disk-complement construction to the literal
ball contacts and both complete rims. Its carrier is exactly the
exposed old spheres and middle level. Normalize that actual sphere
and return it through the unchanged original model inverse.
See Wall015, section 5, equations (3)--(5).
-/

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- The actual two-foot ball and both old sphere models construct
the entire original replacement sphere on the literal exposed-height
carrier. The original chartwise PL inverse is retained pointwise.
All geometric inputs here are the outputs of the original arc model
and its whole-foot consumers. See Wall015, section 5. -/
theorem exists_original_two_foot_height_sphere
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K : SimplicialComplex ℝ E) {g : E → X}
    (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    {N D S₀ S₁ d₀ r₀ d₁ r₁ : Set E} {h : E → ℝ} {beta : ℝ}
    (hNK : N ⊆ K.space) (hDN : D ⊆ N) (hS₀ : S₀ ⊆ D) (hS₁ : S₁ ⊆ D)
    (e₀ : S₀ ≃ₜ frontier (halfBall 1)) (he₀ : e₀.IsFinitePL)
    (e₁ : S₁ ≃ₜ frontier (halfBall 1)) (he₁ : e₁.IsFinitePL)
    (hball : IsFinitePLBallPair ((ℝ × ℝ) × ℝ)
      (N ∩ {x | beta ≤ h x})
      ((N ∩ {x | h x = beta}) ∪ (D ∩ {x | beta ≤ h x})))
    (hd₀ : IsFinitePLBallPair (ℝ × ℝ) d₀ r₀)
    (hd₁ : IsFinitePLBallPair (ℝ × ℝ) d₁ r₁)
    (hc₀ : (N ∩ {x | beta ≤ h x}) ∩ S₀ = d₀)
    (hc₁ : (N ∩ {x | beta ≤ h x}) ∩ S₁ = d₁)
    (hfeet : d₀ ∪ d₁ = D ∩ {x | beta ≤ h x})
    (hr₀ : r₀ = d₀ ∩ {x | h x = beta})
    (hr₁ : r₁ = d₁ ∩ {x | h x = beta})
    (hdisjoint : Disjoint S₀ S₁)
    (hout₀ : (S₀ \ d₀).Nonempty) (hout₁ : (S₁ \ d₁).Nonempty) :
    Nonempty (ChartwisePLSphere e
      (g '' (((S₀ ∪ S₁) ∩ {x | h x ≤ beta}) ∪ (N ∩ {x | h x = beta})))) := by
  have hfoot₀ : d₀ ⊆ (N ∩ {x | h x = beta}) ∪ (D ∩ {x | beta ≤ h x}) :=
    fun _ hx => Or.inr (hfeet.subset (Or.inl hx))
  have hfoot₁ : d₁ ⊆ (N ∩ {x | h x = beta}) ∪ (D ∩ {x | beta ≤ h x}) :=
    fun _ hx => Or.inr (hfeet.subset (Or.inr hx))
  obtain ⟨G, hG⟩ := exists_sphere_model_of_two_foot_ball e₀ he₀ e₁ he₁
    hball hd₀ hd₁ hc₀ hc₁ hfoot₀ hfoot₁ hdisjoint hout₀ hout₁
  have hcarrier := two_foot_replacement_eq_height_carrier
    hDN hS₀ hS₁ hc₀ hc₁ hfeet hr₀ hr₁
  let H := (Homeomorph.setCongr hcarrier.symm).trans G
  have hH : H.IsFinitePL := hG.setCongr hcarrier rfl
  have hcv : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i => (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  have hdim : Module.finrank ℝ ((ℝ × ℝ) × ℝ) = 3 := by
    simp [Module.finrank_prod]
  obtain ⟨b, hb⟩ := hH.exists_unit_cube_sphere_model
    (isCompact_halfBall (Or.inl rfl)) hcv
    (interior_halfBall_nonempty (h := 1) (Or.inl rfl)) hdim
  apply exists_chartwisePLSphere_image K hg hgi _ b hb
  rintro x (⟨hx | hx, _⟩ | hx)
  · exact hNK (hDN (hS₀ hx))
  · exact hNK (hDN (hS₁ hx))
  · exact hNK hx.1

end PoincareMT.M76
