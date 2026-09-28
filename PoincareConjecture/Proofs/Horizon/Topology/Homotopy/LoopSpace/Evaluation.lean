import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.LoopSpace

instance loopCircleCompactSpace : CompactSpace LoopCircle := by
  let e : (Metric.sphere (0 : LoopPlane) 1) ≃ₜ LoopCircle :=
    Homeomorph.setCongr (by ext z; exact mem_sphere_zero_iff_norm)
  exact e.compactSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

def loopValues : C(C1FreeLoopSpace (M := M), C(LoopCircle, M)) :=
  ⟨fun γ => ⟨γ.toFun, γ.continuous⟩, by
    have h : Continuous (fun γ : C1FreeLoopSpace (M := M) =>
        ((⟨γ.toFun, γ.continuous⟩ : C(LoopCircle, M)), c1LoopTangent γ)) :=
      continuous_induced_dom
    exact h.fst⟩

noncomputable def loopTangents :
    C(C1FreeLoopSpace (M := M), C(LoopCircle, TangentBundle (𝓡 3) M)) :=
  ⟨c1LoopTangent, by
    have h : Continuous (fun γ : C1FreeLoopSpace (M := M) =>
        ((⟨γ.toFun, γ.continuous⟩ : C(LoopCircle, M)), c1LoopTangent γ)) :=
      continuous_induced_dom
    exact h.snd⟩

theorem continuous_loop_eval :
    Continuous (fun p : C1FreeLoopSpace (M := M) × LoopCircle => p.1 p.2) :=
  continuous_eval.comp ((loopValues (M := M)).continuous.prodMap continuous_id)

theorem continuous_loop_tangent_eval :
    Continuous (fun p : C1FreeLoopSpace (M := M) × LoopCircle =>
      c1LoopTangent p.1 p.2) :=
  continuous_eval.comp ((loopTangents (M := M)).continuous.prodMap continuous_id)

theorem continuous_iff_values_tangents {X : Type v} [TopologicalSpace X]
    (f : X → C1FreeLoopSpace (M := M)) :
    Continuous f ↔ Continuous (fun x => loopValues (f x)) ∧
      Continuous (fun x => loopTangents (f x)) := by
  exact continuous_induced_rng.trans continuous_prodMk

def loopEvaluation (z : LoopCircle) : C(C1FreeLoopSpace (M := M), M) :=
  ⟨fun γ => γ z, (continuous_eval_const z).comp (loopValues (M := M)).continuous⟩

theorem c1LoopTangent_constant (x : M) :
    c1LoopTangent (constantC1Loop x) =
      ContinuousMap.const LoopCircle (⟨x, 0⟩ : TangentBundle (𝓡 3) M) := by
  apply ContinuousMap.ext
  intro z
  dsimp only [c1LoopTangent, constantC1Loop]
  simp only [mfderiv_const]
  rfl

theorem continuous_constantC1Loop :
    Continuous (constantC1Loop : M → C1FreeLoopSpace (M := M)) := by
  apply (continuous_iff_values_tangents _).mpr
  constructor
  · change Continuous (ContinuousMap.const LoopCircle : M → C(LoopCircle, M))
    exact ContinuousMap.continuous_const'
  · change Continuous (fun x : M => c1LoopTangent (constantC1Loop x))
    simp_rw [c1LoopTangent_constant]
    exact ContinuousMap.continuous_const'.comp
      (Bundle.Trivialization.continuous_zeroSection ℝ)

noncomputable def constantLoopMap : C(M, C1FreeLoopSpace (M := M)) :=
  ⟨constantC1Loop, continuous_constantC1Loop⟩

end PoincareConjecture.LoopSpace
