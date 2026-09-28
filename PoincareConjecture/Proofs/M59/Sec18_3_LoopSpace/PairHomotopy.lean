import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.PairInterpolation
import PoincareConjecture.Proofs.M58.Mathlib.LocalContraction









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

noncomputable section

universe u v

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



def m59EndpointPairLoop (C : ℝ × (M × M) → M) (t : I)
    (delta gamma : C1FreeLoopSpace (M := M))
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, delta z, gamma z)) : C1FreeLoopSpace (M := M) := by
  classical
  exact if t = 0 then gamma else if t = 1 then delta
    else m59PairInterpolationLoop C t delta gamma hC



theorem m59EndpointPairLoop_apply (C : ℝ × (M × M) → M)
    (h0 : ∀ p q, C (0, p, q) = q) (t : I)
    (delta gamma : C1FreeLoopSpace (M := M))
    (h1 : ∀ z, C (1, delta z, gamma z) = delta z)
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, delta z, gamma z)) (z : LoopCircle) :
    m59EndpointPairLoop C t delta gamma hC z = C (t, delta z, gamma z) := by
  classical
  unfold m59EndpointPairLoop
  split_ifs with ht ht
  · subst t
    exact (h0 _ _).symm
  · subst t
    exact (h1 z).symm
  · exact m59PairInterpolationLoop_apply C t delta gamma hC z



theorem m59EndpointPairLoop_constant (C : ℝ × (M × M) → M)
    (hdiag : ∀ t p, C (t, p, p) = p) (t : I) (p : M)
    (hC : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, constantC1Loop p z, constantC1Loop p z)) :
    m59EndpointPairLoop C t (constantC1Loop p) (constantC1Loop p) hC = constantC1Loop p := by
  classical
  unfold m59EndpointPairLoop
  split_ifs
  · rfl
  · rfl
  · exact Proofs.M58.loop_eq_of_fields (funext fun _ => hdiag t p)
      (funext fun _ => hdiag t p)



theorem continuous_m59EndpointPairLoop {X : Type v} [TopologicalSpace X]
    (C : ℝ × (M × M) → M) (h0 : ∀ p q, C (0, p, q) = q)
    (t : X → I) (delta gamma : X → C1FreeLoopSpace (M := M))
    (h1 : ∀ x z, C (1, delta x z, gamma x z) = delta x z)
    (hC : ∀ x (z : LoopCircle),
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t x, delta x z, gamma x z))
    (ht : Continuous t) (hd : Continuous delta) (hg : Continuous gamma) :
    Continuous (fun x => m59EndpointPairLoop C (t x) (delta x) (gamma x) (hC x)) :=
  continuous_of_loop_values_eq
    (continuous_m59PairInterpolationLoop C (fun x => (t x : ℝ)) delta gamma hC
      (continuous_subtype_val.comp ht) hd hg)
    (fun x z => (m59EndpointPairLoop_apply C h0 (t x) (delta x) (gamma x) (h1 x) (hC x) z).trans
      (m59PairInterpolationLoop_apply C (t x) (delta x) (gamma x) (hC x) z).symm)



def m59PairLoopHomotopy {X : Type v} [TopologicalSpace X]
    (C : ℝ × (M × M) → M) (h0 : ∀ p q, C (0, p, q) = q)
    (F G : C(X, C1FreeLoopSpace (M := M)))
    (h1 : ∀ x z, C (1, G x z, F x z) = G x z)
    (hC : ∀ (t : I) x (z : LoopCircle),
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, G x z, F x z)) : F.Homotopy G := by
  classical
  exact {
    toFun := fun p => m59EndpointPairLoop C p.1 (G p.2) (F p.2) (hC p.1 p.2)
    continuous_toFun := continuous_m59EndpointPairLoop C h0 Prod.fst
      (fun p : I × X => G p.2) (fun p : I × X => F p.2)
      (fun p => h1 p.2) (fun p => hC p.1 p.2)
      continuous_fst (G.continuous.comp continuous_snd) (F.continuous.comp continuous_snd)
    map_zero_left := fun _ => by simp [m59EndpointPairLoop]
    map_one_left := fun _ => by simp [m59EndpointPairLoop] }




theorem m59_exists_near_loop_homotopy [T2Space M]
    (hcompact : IsCompact (univ : Set M)) :
    ∃ U : Set (M × M), IsOpen U ∧ diagonal M ⊆ U ∧
      ∀ {X : Type v} [TopologicalSpace X] (F G : C(X, C1FreeLoopSpace (M := M))),
        (∀ x z, (G x z, F x z) ∈ U) →
        ∃ H : F.Homotopy G, ∀ t x p,
          F x = constantC1Loop p → G x = constantC1Loop p → H (t, x) = constantC1Loop p := by
  obtain ⟨C, U, hU, hdiag, h0, h1, hfix, hC⟩ :=
    Proofs.M58.exists_local_contraction (𝓡 3) hcompact 1
  refine ⟨U, hU, hdiag, ?_⟩
  intro X _ F G hFG
  let H := m59PairLoopHomotopy C h0 F G (fun x z => h1 _ (hFG x z))
    (fun t x z => hC _ ⟨t.property, hFG x z⟩)
  refine ⟨H, ?_⟩
  intro t x p hF hG
  change m59EndpointPairLoop C t (G x) (F x) _ = _
  have hh : ∀ z : LoopCircle,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (t, constantC1Loop p z, constantC1Loop p z) := by
    intro z
    simpa only [hF, hG, Nat.cast_one] using hC (t, G x z, F x z) ⟨t.property, hFG x z⟩
  simpa only [hF, hG] using m59EndpointPairLoop_constant C hfix t p hh

end PoincareConjecture
