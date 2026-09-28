import PoincareConjecture.Definitions.M27ProductModels









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

noncomputable section

universe u

namespace PoincareConjecture.AncientCylinderQuotient

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  (q : UnitTwoSphere × ℝ → M)
  (hq : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ q)
  (d : (UnitTwoSphere × ℝ) ≃ₜ (UnitTwoSphere × ℝ))
  (hdeck : q ∘ d = q)

include hq hdeck in
theorem deck_contMDiff :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ d := by
  intro p
  let hl := hq (d p)
  have hc : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (q ∘ d) := by
    rw [hdeck]
    exact hq.contMDiff
  have hs := hl.localInverse_contMDiffAt.comp p (hc p)
  apply hs.congr_of_eventuallyEq
  filter_upwards [d.continuous.continuousAt.preimage_mem_nhds
    (hl.localInverse.open_target.mem_nhds hl.localInverse_mem_target)] with z hz
  exact (hl.localInverse_left_inv hz).symm

include hdeck in
theorem deck_symm : q ∘ d.symm = q := by
  funext p
  have h := congrFun hdeck (d.symm p)
  simpa only [Function.comp_apply, d.apply_symm_apply] using h.symm


def deckDiffeomorph :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (UnitTwoSphere × ℝ) (UnitTwoSphere × ℝ) ∞ where
  toEquiv := d.toEquiv
  contMDiff_toFun := deck_contMDiff q hq d hdeck
  contMDiff_invFun := deck_contMDiff q hq d.symm (deck_symm q d hdeck)

@[simp] theorem deckDiffeomorph_apply (p : UnitTwoSphere × ℝ) :
    deckDiffeomorph q hq d hdeck p = d p := rfl

@[simp] theorem deckDiffeomorph_symm_apply (p : UnitTwoSphere × ℝ) :
    (deckDiffeomorph q hq d hdeck).symm p = d.symm p := rfl

variable [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M}

include hq hdeck in


theorem deck_productInner (F : M27RoundSphereFamily)
    (hmetric : ∀ t, t ≤ 0 → ∀ p : UnitTwoSphere × ℝ,
      ∀ v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p,
        (K.flow.metric t).inner (q p)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p w) =
          F.productInner t p v w)
    (t : ℝ) (ht : t ≤ 0) (p : UnitTwoSphere × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
    F.productInner t (d p)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d p v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d p w) =
      F.productInner t p v w := by
  have hd := deck_contMDiff q hq d hdeck
  have hder (a : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) p) :
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q (d p)
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) d p a) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) q p a := by
    rw [← mfderiv_comp_apply p (hq.mdifferentiable (by simp) _)
      (hd.mdifferentiable (by simp) _), hdeck]
  rw [← hmetric t ht, hder v, hder w]
  have hp := congrFun hdeck p
  change q (d p) = q p at hp
  rw [hp]
  exact hmetric t ht p v w

end PoincareConjecture.AncientCylinderQuotient
